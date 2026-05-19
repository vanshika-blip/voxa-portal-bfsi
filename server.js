'use strict';
/**
 * server.js — Voxa Portal Node Server (ALL logic in Node, no GAS proxy)
 *
 * Architecture:
 *   - Every API action is handled natively here (reads/writes Google Sheets directly)
 *   - GAS is kept only as a DB / sheet storage layer (no logic there needed)
 *   - Per-agent spreadsheets (agent.spreadsheetId) for Master_Tracker, Qualified_Leads, etc.
 *   - Per-team spreadsheets (team.spreadsheetId) for Manual_Tracker, Interview_Lineup
 *   - Main spreadsheet for Users, Teams, Agents, Sessions, Audit Log, Trigger Log, etc.
 *
 * ROOT CAUSE FIX: express.json() only parses application/json.
 *   The frontend sends Content-Type: text/plain → req.body was always {}.
 *   Fixed by using express text + JSON.parse middleware.
 */

const express  = require('express');
const cors     = require('cors');
const crypto   = require('crypto');
const axios    = require('axios');
const path     = require('path');
const { google } = require('googleapis');

const sheetsHelper = require('./sheets');
const {
  readSheet, readSheetAsObjects, writeRow, writeRows,
  appendRows, clearRange, deleteRows, ensureSheet,
  testConnection, sleep, withRetry,
} = sheetsHelper;

const {
  startPoller, pollActiveBatches, backfillMissingOutputs,
  repairUnassignedLeads, cleanupExpiredSessions, dedupeAllSheets,
  archiveCompletedLeads, archiveCompletedMT, archiveManualTracker,
  processCallbackQueue, processRetryQueue,
  getArchivedLeads, getArchivedMT, getArchivedManual,
  getStatus,
} = require('./poller');

const app  = express();
const PORT = process.env.PORT || 10000;

// ─── Env vars ──────────────────────────────────────────────────────────────────
const MAIN_SS_ID      = process.env.SPREADSHEET_ID;
const HUNAR_BASE      = 'https://api.voice.hunar.ai';
const HUNAR_KEY       = process.env.HUNAR_API_KEY || 'hunar_va_live_sk_qH3Xewk3DcBI68rKsMtLmBxw60earGaMWQdcZIEW_mcmIdwn_x8FRQ';
const POLLER_TOKEN    = process.env.POLLER_TOKEN || 'voxa-bfsi-2026';
const MANUAL_TRACKER_SS_ID = process.env.MANUAL_TRACKER_SS_ID || '';
const LINEUP_SS_ID         = process.env.LINEUP_SS_ID || '';
const SERVICE_EMAIL   = process.env.SERVICE_ACCOUNT_EMAIL || '';
const GAS_URL         = process.env.GAS_URL; // Only used for email sending (optional)
const PORTAL_MAIL     = process.env.MAIL_FROM || 'Voxa <noreply@voxa.ai>';
const DASHBOARD_URL   = process.env.DASHBOARD_URL || 'https://voxatest.vercel.app';

// ─── Constants matching GAS ───────────────────────────────────────────────────
const SESSION_TTL_MS       = 12 * 60 * 60 * 1000;
const SETUP_TOKEN_TTL_MS   = 48 * 60 * 60 * 1000;
const PW_ITERATIONS        = 2000;
const IST_TZ               = 'Asia/Kolkata';

// Main SS sheet names
const S = {
  USERS:    'Users',
  TEAMS:    'Teams',
  AGENTS:   'Agents',
  TLOG:     'Trigger Log',
  SESSIONS: 'Sessions',
  AUDIT:    'Audit Log',
  CB_Q:     '_Callback_Queue',
  RETRY_Q:  '_Retry_Queue',
  TEAM_LST: '_Team_Lists',
  SQ:       '_Support_Queries',
};

// Per-agent SS sheet names
const AGT = {
  MT: 'Master_Tracker',
  QL: 'Qualified_Leads',
  CT: 'Campaign_Tracker',
  CI: 'Call_Input',
  NC: 'Not_Connected',
  CB: 'Callbacks',
};

// Per-team SS sheet names
const TEAM_SH = {
  MANUAL: 'Manual_Tracker',
  LINEUP: 'Interview_Lineup',
};

const ROLES = ['super_admin', 'team_lead', 'individual_contributor', 'recruiter'];
const FINAL_ST = new Set(['COMPLETED', 'NOT_CONNECTED', 'CANCELLED', 'FAILED']);

// ─── Body parsing: CRITICAL FIX ───────────────────────────────────────────────
// Frontend sends Content-Type: text/plain with JSON body.
// express.json() only parses application/json → req.body was always {}.
// This middleware reads any body as text and JSON-parses it.
app.use(cors());
app.use((req, res, next) => {
  let raw = '';
  req.on('data', chunk => { raw += chunk; });
  req.on('end', () => {
    if (raw.trim()) {
      try { req.body = JSON.parse(raw); } catch (_) { req.body = {}; }
    } else {
      req.body = {};
    }
    next();
  });
});
app.use(express.static(path.join(__dirname, 'public')));

// ─── In-memory caches ─────────────────────────────────────────────────────────
let _usersCache    = null; let _usersCacheAt  = 0;
let _agentsCache   = null; let _agentsCacheAt = 0;
let _teamsCache    = null; let _teamsCacheAt  = 0;
let _sessionCache  = new Map(); // token → session object

// ─── Password utils ───────────────────────────────────────────────────────────
function hashPassword(pw, salt) {
  let buf = crypto.createHash('sha256').update(`${salt}:${pw}`, 'utf8').digest();
  for (let i = 1; i < PW_ITERATIONS; i++) buf = crypto.createHash('sha256').update(buf).digest();
  return buf.toString('base64');
}
function verifyPassword(pw, salt, stored) {
  if (!pw || !salt || !stored) return false;
  const computed = hashPassword(pw, salt);
  if (computed.length !== stored.length) return false;
  let diff = 0;
  for (let i = 0; i < computed.length; i++) diff |= computed.charCodeAt(i) ^ stored.charCodeAt(i);
  return diff === 0;
}

// ─── Sheet data loaders ───────────────────────────────────────────────────────
async function getAllUsers(force = false) {
  if (!force && _usersCache && Date.now() - _usersCacheAt < 60_000) return _usersCache;
  const { headers, rows } = await readSheet(MAIN_SS_ID, S.USERS);
  if (!headers.length) return (_usersCache = []);
  const idx = h => headers.indexOf(h);
  _usersCache = rows.map(r => ({
    email:            String(r[idx('Email')]              || '').toLowerCase().trim(),
    name:             String(r[idx('Name')]               || '').trim(),
    role:             String(r[idx('Role')]               || '').trim().toLowerCase(),
    team:             String(r[idx('Team')]               || '').trim(),
    dailyMinuteLimit: Number(r[idx('Daily Minute Limit')] || 0),
    active:           r[idx('Active')] === true || String(r[idx('Active')]).toUpperCase() === 'TRUE',
    passwordHash:     String(r[idx('Password Hash')]      || '').trim(),
    passwordSalt:     String(r[idx('Password Salt')]      || '').trim(),
    setupToken:       String(r[idx('Setup Token')]        || '').trim(),
    tokenExpires:     r[idx('Setup Token Expires')]       || '',
  })).filter(u => u.email);
  _usersCacheAt = Date.now();
  return _usersCache;
}

async function findUser(email) {
  const users = await getAllUsers();
  return users.find(u => u.email === String(email || '').toLowerCase().trim()) || null;
}

async function writeUserFields(email, partial) {
  email = String(email).toLowerCase().trim();
  const { headers, rows } = await readSheet(MAIN_SS_ID, S.USERS);
  if (!headers.length) return false;
  const idx = h => headers.indexOf(h);
  const ei = idx('Email');
  for (let i = 0; i < rows.length; i++) {
    if (String(rows[i][ei] || '').toLowerCase().trim() !== email) continue;
    const c = rows[i];
    const n = headers.map((h, j) => partial[h] !== undefined ? partial[h] : c[j]);
    await writeRow(MAIN_SS_ID, S.USERS, i + 2, n);
    _usersCache = null;
    return true;
  }
  return false;
}

async function getAllAgents(force = false) {
  if (!force && _agentsCache && Date.now() - _agentsCacheAt < 120_000) return _agentsCache;
  const { headers, rows } = await readSheet(MAIN_SS_ID, S.AGENTS);
  if (!headers.length) return (_agentsCache = []);
  const idx = h => headers.indexOf(h);
  _agentsCache = rows.map(r => {
    let cv = [], rs = {}, qv = [], qr = [];
    try { cv = JSON.parse(r[idx('Custom Variables')] || '[]'); } catch (_) {}
    try { rs = JSON.parse(r[idx('Result Schema')]    || '{}'); } catch (_) {}
    try {
      const raw = r[idx('Qualification Values')];
      if (typeof raw === 'string' && raw.trim().startsWith('[')) qv = JSON.parse(raw);
      else if (raw) qv = [String(raw)];
    } catch (_) {}
    try {
      const raw = r[idx('Qualification Rules')];
      if (typeof raw === 'string' && raw.trim().startsWith('[')) qr = JSON.parse(raw);
    } catch (_) {}
    return {
      agentCode:           String(r[idx('Agent Code')]           || '').trim(),
      agentId:             String(r[idx('Agent ID')]             || '').trim(),
      displayName:         String(r[idx('Display Name')]         || '').trim(),
      description:         String(r[idx('Description')]          || '').trim(),
      language:            String(r[idx('Language')]             || 'ENGLISH').trim(),
      voicePersona:        String(r[idx('Voice Persona')]        || '').trim(),
      customVariables:     Array.isArray(cv) ? cv : [],
      resultSchema:        rs || {},
      qualificationField:  String(r[idx('Qualification Field')]  || '').trim(),
      qualificationValues: Array.isArray(qv) ? qv.filter(Boolean) : [],
      qualificationRules:  Array.isArray(qr) ? qr : [],
      estSecondsPerCall:   Number(r[idx('Est Seconds Per Call')] || 60),
      active:              r[idx('Active')] === true || r[idx('Active')] === 'TRUE',
      createdBy:           String(r[idx('Created By')]           || '').trim(),
      clientName:          String(r[idx('Client Name')]          || '').trim(),
      spreadsheetId:       String(r[idx('Spreadsheet ID')]       || '').trim(),
      addedById:           r[idx('Added By ID')] === true || r[idx('Added By ID')] === 'TRUE',
      agentPrompt:         String(r[idx('Agent Prompt')]         || '').trim(),
      resultPrompt:        String(r[idx('Result Prompt')]        || '').trim(),
      introduction:        String(r[idx('Introduction')]         || '').trim(),
    };
  }).filter(a => a.agentCode);
  _agentsCacheAt = Date.now();
  return _agentsCache;
}

async function findAgent(code) {
  const agents = await getAllAgents();
  return agents.find(a => a.agentCode === code) || null;
}

async function findAgentByHunarId(id) {
  const agents = await getAllAgents();
  return agents.find(a => a.agentId === id) || null;
}

async function writeAgentRow(agent) {
  const { headers, rows } = await readSheet(MAIN_SS_ID, S.AGENTS);
  if (!headers.length) return;
  const vals = headers.map(h => {
    switch (h) {
      case 'Agent Code':           return agent.agentCode || '';
      case 'Agent ID':             return agent.agentId || '';
      case 'Display Name':         return agent.displayName || '';
      case 'Description':          return agent.description || '';
      case 'Language':             return agent.language || 'ENGLISH';
      case 'Voice Persona':        return agent.voicePersona || '';
      case 'Custom Variables':     return JSON.stringify(agent.customVariables || []);
      case 'Result Schema':        return JSON.stringify(agent.resultSchema || {});
      case 'Qualification Field':  return agent.qualificationField || '';
      case 'Qualification Values': return JSON.stringify(agent.qualificationValues || []);
      case 'Qualification Rules':  return JSON.stringify(agent.qualificationRules || []);
      case 'Est Seconds Per Call': return Number(agent.estSecondsPerCall || 60);
      case 'Active':               return !!agent.active;
      case 'Last Synced':          return new Date().toISOString();
      case 'Created On':           return agent.createdOn || new Date().toISOString();
      case 'Created By':           return agent.createdBy || '';
      case 'Added By ID':          return !!agent.addedById;
      case 'Agent Prompt':         return agent.agentPrompt || '';
      case 'Result Prompt':        return agent.resultPrompt || '';
      case 'Introduction':         return agent.introduction || '';
      case 'Client Name':          return agent.clientName || '';
      case 'Spreadsheet ID':       return agent.spreadsheetId || '';
      default:                     return '';
    }
  });
  const codeIdx = headers.indexOf('Agent Code');
  for (let i = 0; i < rows.length; i++) {
    if (String(rows[i][codeIdx] || '') === agent.agentCode) {
      // Preserve createdOn / createdBy
      const createdOnIdx  = headers.indexOf('Created On');
      const createdByIdx  = headers.indexOf('Created By');
      if (createdOnIdx >= 0 && rows[i][createdOnIdx]) vals[createdOnIdx] = rows[i][createdOnIdx];
      if (createdByIdx >= 0 && rows[i][createdByIdx]) vals[createdByIdx] = rows[i][createdByIdx];
      await writeRow(MAIN_SS_ID, S.AGENTS, i + 2, vals);
      _agentsCache = null;
      return;
    }
  }
  await appendRows(MAIN_SS_ID, S.AGENTS, [vals]);
  _agentsCache = null;
}

async function getAllTeams(force = false) {
  if (!force && _teamsCache && Date.now() - _teamsCacheAt < 120_000) return _teamsCache;
  const { headers, rows } = await readSheet(MAIN_SS_ID, S.TEAMS);
  if (!headers.length) return (_teamsCache = []);
  const idx = h => headers.indexOf(h);
  _teamsCache = rows.map(r => ({
    id:            String(r[idx('Team ID')]       || '').trim(),
    name:          String(r[idx('Team Name')]     || '').trim(),
    spreadsheetId: String(r[idx('Spreadsheet ID')]|| '').trim(),
  })).filter(t => t.name);
  _teamsCacheAt = Date.now();
  return _teamsCache;
}

async function findTeam(name) {
  const teams = await getAllTeams();
  return teams.find(t => t.name === name) || null;
}

// ─── Hunar API ─────────────────────────────────────────────────────────────────
async function hunarGet(path) {
  try {
    const r = await axios.get(`${HUNAR_BASE}${path}`, {
      headers: { 'X-API-Key': HUNAR_KEY, 'Content-Type': 'application/json' },
      timeout: 15000,
    });
    return { ok: true, data: r.data };
  } catch (e) {
    return { ok: false, error: e.response?.data ? JSON.stringify(e.response.data).slice(0, 300) : e.message };
  }
}
async function hunarPost(path, body) {
  try {
    const r = await axios.post(`${HUNAR_BASE}${path}`, body, {
      headers: { 'X-API-Key': HUNAR_KEY, 'Content-Type': 'application/json' },
      timeout: 30000,
    });
    return { ok: true, data: r.data };
  } catch (e) {
    return { ok: false, error: e.response?.data ? JSON.stringify(e.response.data).slice(0, 300) : e.message };
  }
}

// ─── Drive: create + share spreadsheets ──────────────────────────────────────
function _getGoogleAuth() {
  const b64 = process.env.GOOGLE_SERVICE_ACCOUNT_B64;
  if (!b64) throw new Error('GOOGLE_SERVICE_ACCOUNT_B64 not set');
  const sa = JSON.parse(Buffer.from(b64, 'base64').toString('utf8'));
  return new google.auth.GoogleAuth({
    credentials: sa,
    scopes: [
      'https://www.googleapis.com/auth/spreadsheets',
      'https://www.googleapis.com/auth/drive',
    ],
  });
}

async function createSpreadsheet(title) {
  // GAS has full Drive access — delegate spreadsheet creation to GAS
  // Node cannot create Drive files due to org policy restrictions on service accounts
  const gasUrl = process.env.GAS_URL;
  if (!gasUrl) throw new Error('GAS_URL not set — needed for spreadsheet creation');
  try {
    const res = await axios.post(gasUrl, {
      action: 'createspreadsheet',
      title,
      secret: process.env.POLLER_TOKEN || 'voxa-bfsi-2026',
    }, { timeout: 30000 });
    const data = res.data;
    if (!data.ok || !data.ssId) throw new Error(data.error || 'GAS did not return ssId');
    return data.ssId;
  } catch (e) {
    throw new Error('Could not create spreadsheet via GAS: ' + e.message);
  }
}

async function shareSpreadsheet(fileId, ...emails) {
  try {
    const auth = _getGoogleAuth();
    const drive = google.drive({ version: 'v3', auth });
    for (const email of emails.filter(Boolean)) {
      await drive.permissions.create({
        fileId,
        requestBody: { role: 'writer', type: 'user', emailAddress: email },
        sendNotificationEmail: false,
      });
    }
  } catch (e) {
    console.warn('[drive] Could not share spreadsheet:', e.message);
  }
}

// ─── Spreadsheet initialisation (mirrors GAS _initAgentSS / _initTeamSS) ─────
function resultFieldNames(schema) {
  if (!schema || typeof schema !== 'object') return [];
  if (schema.properties) return Object.keys(schema.properties);
  return Object.keys(schema).filter(k => k !== 'type' && k !== 'required');
}

const FIXED_MT_H  = ['Call ID','Request ID','Callee Name','Mobile Number','Status','Duration (Minutes)','Duration (Seconds)','Started At','Ended At','Answered By','Engagement Status','Call Ended By','Recording URL','Triggered By','Created At','Updated At'];
const FIXED_CI_H  = ['Row ID','Uploaded At','Request ID','Triggered By','Callee Name','Mobile Number'];
const FIXED_QL_EX = ['Call Status','Feedback','Selection Process','Turnup Status','Remarks','Remarks Updated At','Remarks Updated By','Assigned To Email','Recruiter','Date Added'];
const CT_H        = ['Request ID','Campaign Name','Triggered By','Triggered At','Contacts Count','Status','Completed','Connected','Not Connected','Failed','Qualified','Actual Minutes','Estimated Minutes','Last Updated'];
const NC_H        = ['Call ID','Callee Name','Mobile Number','Status','Request ID','Retry Count','Retries Left','Next Retry Scheduled At','Triggered By','Last Updated','Retry Scheduled Date','Trigger Status','Retry Request ID'];
const CB_EXTRA_H  = ['Callback Field','Callback Value','Scheduled Date','Queue ID','Trigger Status','Retry Request ID','Date Added'];
const MANUAL_H    = ['Unique ID','Date','Candidate Name','Contact Number','Location','Client','Role','Source','Call Status','Lined-up','Remarks','Added By Email','Added By Name','Team','In Lineup','Created At'];
const LINEUP_H    = ['Source','Call ID','Callee Name','Mobile Number','Agent Code','Agent Name','Campaign Name','Request ID','Started At','Month','Selection Process','Turnup Status','Assigned Recruiter Email','Assigned Recruiter Name','Client','Email','DOB','Qualification','Work Experience','Current CTC','Expected CTC','Notice Period','Role','Location','CIBIL Score','SPOC Name','Current Employer','CV Link','Date Added'];

async function initAgentSS(ssId, agent) {
  const rf  = resultFieldNames(agent.resultSchema);
  const cv  = agent.customVariables || [];
  const ciH = [...FIXED_CI_H, ...cv, 'Extra Raw Data'];
  const mtH = [...FIXED_MT_H, ...cv.map(v => `in.${v}`), ...rf.map(f => `out.${f}`)];
  const qlH = [...mtH, ...FIXED_QL_EX];
  const cbH = [...qlH, ...CB_EXTRA_H];
  await Promise.all([
    ensureSheet(ssId, AGT.MT, mtH,  '#34495e'),
    ensureSheet(ssId, AGT.QL, qlH,  '#1a7f4b'),
    ensureSheet(ssId, AGT.CT, CT_H, '#2c3e50'),
    ensureSheet(ssId, AGT.CI, ciH,  '#1a6fdc'),
    ensureSheet(ssId, AGT.NC, NC_H, '#8e44ad'),
    ensureSheet(ssId, AGT.CB, cbH,  '#d4880a'),
  ]);
}

async function initTeamSS(ssId) {
  await Promise.all([
    ensureSheet(ssId, TEAM_SH.MANUAL, MANUAL_H, '#0369a1'),
    ensureSheet(ssId, TEAM_SH.LINEUP, LINEUP_H, '#5b21b6'),
  ]);
}

// ─── Session management ───────────────────────────────────────────────────────
async function validateSession(token) {
  if (!token) return null;
  const c = _sessionCache.get(token);
  if (c) {
    if (c.expires < Date.now()) { _sessionCache.delete(token); return null; }
    return c;
  }
  // Fallback: check Sessions sheet
  try {
    const { headers, rows } = await readSheet(MAIN_SS_ID, S.SESSIONS);
    if (!headers.length) return null;
    const ti = headers.indexOf('Token');
    const ei = headers.indexOf('Email');
    const xi = headers.indexOf('Expires At');
    for (const r of rows) {
      if (String(r[ti] || '') !== token) continue;
      const expires = new Date(r[xi] || 0).getTime();
      if (expires < Date.now()) return null;
      const email = String(r[ei] || '').toLowerCase().trim();
      const user  = await findUser(email);
      if (!user || !user.active) return null;
      const sess = { email, expires, role: user.role, team: user.team, name: user.name };
      _sessionCache.set(token, sess);
      return sess;
    }
  } catch (_) {}
  return null;
}

function _createSessionToken() {
  return crypto.randomUUID() + '-' + crypto.randomBytes(4).toString('hex');
}

async function persistSession(token, email, expires) {
  _sessionCache.set(token, { email, expires });
  try {
    await appendRows(MAIN_SS_ID, S.SESSIONS, [[token, email, new Date().toISOString(), new Date(expires).toISOString()]]);
  } catch (_) {}
}

// ─── Audit log ────────────────────────────────────────────────────────────────
async function audit(actorEmail, action, target, details) {
  try {
    await appendRows(MAIN_SS_ID, S.AUDIT, [[new Date().toISOString(), actorEmail, action, target, details || '']]);
  } catch (_) {}
}

// ─── Qualification ─────────────────────────────────────────────────────────────
function isQualified(agent, result) {
  const rules = agent.qualificationRules;
  if (rules && rules.length) {
    return rules.every(rule => {
      if (!rule.field) return true;
      const val = result[rule.field];
      if (!val && val !== 0) return false;
      const kws = (rule.keywords || []).filter(Boolean);
      if (!kws.length) return !!val;
      const low = String(val).toLowerCase();
      return kws.some(k => low.includes(String(k).toLowerCase()));
    });
  }
  if (!agent.qualificationField) return false;
  const val = result[agent.qualificationField];
  if (!val) return false;
  const vs = agent.qualificationValues || [];
  if (!vs.length) return !!val;
  const low = String(val).toLowerCase().trim();
  return vs.some(v => low.includes(String(v).toLowerCase().trim()));
}

// ─── Role helpers ──────────────────────────────────────────────────────────────
function isTLLike(role) { return ['team_lead', 'individual_contributor', 'super_admin'].includes(role); }

function agentsVisibleTo(actor, agents, users = []) {
  const active = agents.filter(a => a.active);
  if (actor.role === 'super_admin') return active;

  if (actor.role === 'team_lead' || actor.role === 'individual_contributor') {
    // Primary: agents explicitly created by this user
    // Secondary: agents with no createdBy (bulk-pasted) — visible to all TL-like roles
    // Tertiary: agents created by anyone on same team
    const sameTeamEmails = new Set(
      users.filter(u => u.team === actor.team && u.active && isTLLike(u.role)).map(u => u.email)
    );
    return active.filter(a =>
      a.createdBy === actor.email ||          // their own agents
      !a.createdBy ||                          // bulk-pasted (no owner) — visible to all
      sameTeamEmails.has(a.createdBy)          // same team member's agents
    );
  }

  if (actor.role === 'recruiter') {
    if (!actor.team) return [];
    const tlEmails = new Set(
      users.filter(u => u.team === actor.team && u.active && isTLLike(u.role)).map(u => u.email)
    );
    return active.filter(a =>
      tlEmails.has(a.createdBy) || !a.createdBy  // team's agents + unowned agents
    );
  }
  return [];
}

function visibleUserEmails(actor, users) {
  if (actor.role === 'super_admin') return users.map(u => u.email);
  if (isTLLike(actor.role)) return users.filter(u => u.team === actor.team).map(u => u.email);
  return [actor.email];
}

function publicUser(u) {
  return { email: u.email, name: u.name, role: u.role, team: u.team,
    dailyMinuteLimit: u.dailyMinuteLimit, active: u.active, hasPassword: !!u.passwordHash };
}

function publicAgent(a) {
  return {
    agentCode: a.agentCode, agentId: a.agentId, displayName: a.displayName,
    description: a.description, language: a.language, voicePersona: a.voicePersona,
    customVariables: a.customVariables, resultSchema: a.resultSchema,
    qualificationField: a.qualificationField, qualificationValues: a.qualificationValues || [],
    qualificationRules: a.qualificationRules || [], estSecondsPerCall: a.estSecondsPerCall,
    active: a.active, createdBy: a.createdBy || '', addedById: !!a.addedById,
    agentPrompt: a.agentPrompt || '', resultPrompt: a.resultPrompt || '',
    introduction: a.introduction || '', clientName: a.clientName || '',
    spreadsheetId: a.spreadsheetId || '',
  };
}

function slug(s) {
  return String(s || '').toLowerCase().replace(/[^a-z0-9]+/g, '_').replace(/^_+|_+$/g, '').slice(0, 40);
}

function defaultQualField(rs) {
  if (!rs || typeof rs !== 'object') return '';
  const keys = rs.properties ? Object.keys(rs.properties) : Object.keys(rs).filter(k => k !== 'type' && k !== 'required');
  for (const k of keys) if (/qualif/i.test(k) || /interested/i.test(k)) return k;
  return keys[0] || '';
}

function istDateStr(date = new Date()) {
  return date.toLocaleDateString('en-CA', { timeZone: IST_TZ }); // YYYY-MM-DD
}

// ─── Email (proxy to GAS if GAS_URL set, else log) ────────────────────────────
async function sendEmail(to, subject, htmlBody) {
  if (GAS_URL) {
    try {
      await axios.post(GAS_URL, { action: 'sendemail', to, subject, htmlBody }, { timeout: 10000 });
    } catch (e) {
      console.warn('[email] GAS email failed:', e.message);
    }
  } else {
    console.log(`[email] Would send to ${to}: ${subject}`);
  }
}

function inviteEmailHtml(user, url, isReset) {
  return `<div style="font-family:-apple-system,sans-serif;max-width:560px;margin:auto">
<div style="background:#6739b7;color:#fff;padding:24px;border-radius:12px 12px 0 0"><h1 style="margin:0;font-size:20px">Voxa</h1></div>
<div style="background:#fff;padding:28px;border:1px solid #eee;border-radius:0 0 12px 12px">
<p>Hi ${user.name || user.email}</p>
${isReset ? '<p>A password reset was requested.</p>' : `<p>You have been invited as <b>${user.role}</b>${user.team ? ` on <b>${user.team}</b>` : ''}.</p>`}
<p><a href="${url}" style="background:#6739b7;color:#fff;padding:12px 28px;border-radius:8px;text-decoration:none;font-weight:600;display:inline-block">${isReset ? 'Reset Password' : 'Set Up My Account'}</a></p>
<p style="color:#666;font-size:13px">Link expires in 48 hours.</p>
</div></div>`;
}

// ─── Today usage ──────────────────────────────────────────────────────────────
async function todayUsageFor(email) {
  email = String(email || '').toLowerCase();
  const today = istDateStr();
  try {
    const { headers, rows } = await readSheet(MAIN_SS_ID, S.TLOG);
    if (!headers.length) return { minutes: 0, calls: 0 };
    const ei = headers.indexOf('User Email');
    const ti = headers.indexOf('Timestamp');
    const mi = headers.indexOf('Estimated Minutes');
    const ci = headers.indexOf('Contacts Count');
    let mins = 0, calls = 0;
    rows.forEach(r => {
      if (String(r[ei] || '').toLowerCase() !== email) return;
      const d = new Date(r[ti] || 0);
      if (isNaN(d.getTime())) return;
      if (d.toLocaleDateString('en-CA', { timeZone: IST_TZ }) !== today) return;
      mins  += Number(r[mi] || 0);
      calls += Number(r[ci] || 0);
    });
    return { minutes: mins, calls };
  } catch (_) { return { minutes: 0, calls: 0 }; }
}

// ═══════════════════════════════════════════════════════════════════════════════
// ACTION HANDLERS
// ═══════════════════════════════════════════════════════════════════════════════

// ─── Auth ─────────────────────────────────────────────────────────────────────
async function handleLogin(body) {
  const email = String(body.email || '').toLowerCase().trim();
  const pw    = String(body.password || '');
  if (!email || !pw) return { ok: false, error: 'EMAIL_AND_PASSWORD_REQUIRED' };
  const user = await findUser(email);
  if (!user)           return { ok: false, error: 'INVALID_CREDENTIALS' };
  if (!user.active)    return { ok: false, error: 'ACCOUNT_INACTIVE' };
  if (!user.passwordHash) return { ok: false, error: 'PASSWORD_NOT_SET', message: 'Check your email for the setup link.' };
  if (!verifyPassword(pw, user.passwordSalt, user.passwordHash)) return { ok: false, error: 'INVALID_CREDENTIALS' };
  const token   = _createSessionToken();
  const expires = Date.now() + SESSION_TTL_MS;
  _sessionCache.set(token, { email: user.email, name: user.name, role: user.role, team: user.team, expires });
  await persistSession(token, user.email, expires);
  audit(user.email, 'login', email, '').catch(() => {});
  return { ok: true, session: token, user: publicUser(user) };
}

async function handleLogout(body) {
  const token = body.session;
  if (token) _sessionCache.delete(token);
  // Clean sheet row async
  (async () => {
    try {
      const { headers, rows } = await readSheet(MAIN_SS_ID, S.SESSIONS);
      if (!headers.length) return;
      const ti = headers.indexOf('Token');
      for (let i = 0; i < rows.length; i++) {
        if (String(rows[i][ti] || '') === token) {
          await deleteRows(MAIN_SS_ID, S.SESSIONS, [i + 2]); break;
        }
      }
    } catch (_) {}
  })();
  return { ok: true };
}

async function handleVerifyToken(body) {
  const tok = String(body.token || '').trim();
  if (!tok) return { ok: false, error: 'TOKEN_REQUIRED' };
  const users = await getAllUsers();
  const user  = users.find(u => u.setupToken === tok);
  if (!user) return { ok: false, error: 'INVALID_TOKEN' };
  if (user.tokenExpires && new Date(user.tokenExpires).getTime() < Date.now()) return { ok: false, error: 'TOKEN_EXPIRED' };
  return { ok: true, email: user.email, name: user.name, role: user.role };
}

async function handleCompleteSetup(body) {
  const tok = String(body.token || '').trim();
  const pw  = String(body.password || '');
  if (!tok || !pw) return { ok: false, error: 'TOKEN_AND_PASSWORD_REQUIRED' };
  if (pw.length < 8) return { ok: false, error: 'PASSWORD_TOO_SHORT' };
  const users = await getAllUsers();
  const user  = users.find(u => u.setupToken === tok);
  if (!user) return { ok: false, error: 'INVALID_TOKEN' };
  if (user.tokenExpires && new Date(user.tokenExpires).getTime() < Date.now()) return { ok: false, error: 'TOKEN_EXPIRED' };
  const salt = crypto.randomUUID().replace(/-/g, '');
  const hash = hashPassword(pw, salt);
  await writeUserFields(user.email, {
    'Password Hash': hash, 'Password Salt': salt,
    'Setup Token': '', 'Setup Token Expires': '', 'Active': true,
  });
  _usersCache = null;
  const token   = _createSessionToken();
  const expires = Date.now() + SESSION_TTL_MS;
  await persistSession(token, user.email, expires);
  audit(user.email, 'complete_setup', user.email, '').catch(() => {});
  const freshUser = await findUser(user.email);
  return { ok: true, session: token, user: publicUser(freshUser) };
}

async function handleRequestReset(body) {
  const email = String(body.email || '').toLowerCase().trim();
  if (!email) return { ok: false, error: 'EMAIL_REQUIRED' };
  const user = await findUser(email);
  if (!user) return { ok: true, message: 'If that email exists, a reset link has been sent.' };
  const tok = crypto.randomUUID();
  const exp = new Date(Date.now() + SETUP_TOKEN_TTL_MS).toISOString();
  await writeUserFields(email, { 'Setup Token': tok, 'Setup Token Expires': exp });
  const url = `${DASHBOARD_URL}/?token=${encodeURIComponent(tok)}`;
  sendEmail(email, 'Reset your portal password', inviteEmailHtml(user, url, true)).catch(() => {});
  return { ok: true, message: 'If that email exists, a reset link has been sent.' };
}

async function handleChangePassword(actor, body) {
  const oldPw = String(body.oldPassword || '');
  const newPw = String(body.newPassword || '');
  if (newPw.length < 8) return { ok: false, error: 'PASSWORD_TOO_SHORT' };
  const full = await findUser(actor.email);
  if (!verifyPassword(oldPw, full.passwordSalt, full.passwordHash)) return { ok: false, error: 'OLD_PASSWORD_WRONG' };
  const salt = crypto.randomUUID().replace(/-/g, '');
  const hash = hashPassword(newPw, salt);
  await writeUserFields(actor.email, { 'Password Hash': hash, 'Password Salt': salt });
  _usersCache = null;
  return { ok: true };
}

async function handleMe(actor) {
  const [agents, users] = await Promise.all([getAllAgents(), getAllUsers()]);
  const isUnlimited = actor.role === 'super_admin';
  const today = isUnlimited ? { minutes: 0, calls: 0 } : await todayUsageFor(actor.email);
  const vis = agentsVisibleTo(actor, agents, users);
  return {
    ok: true,
    user: publicUser(actor),
    agents: vis.map(publicAgent),
    today: {
      minutesUsed:      isUnlimited ? 0    : Math.round(today.minutes * 100) / 100,
      minutesLimit:     isUnlimited ? null : actor.dailyMinuteLimit,
      minutesRemaining: isUnlimited ? null : Math.max(0, Math.round((actor.dailyMinuteLimit - today.minutes) * 100) / 100),
      callsMade:        today.calls,
      unlimited:        isUnlimited,
    },
  };
}

// ─── User management ──────────────────────────────────────────────────────────
async function handleListUsers(actor) {
  const [users, _] = await Promise.all([getAllUsers(), null]);
  const vis = new Set(visibleUserEmails(actor, users));
  return {
    ok: true,
    users: users.filter(u => vis.has(u.email)).map(u => {
      const p = publicUser(u); p.pending = !u.passwordHash; return p;
    }),
  };
}

async function handleUpsertUser(actor, body) {
  const u = body.user || {};
  if (!u.email) return { ok: false, error: 'EMAIL_REQUIRED' };
  u.email = String(u.email).toLowerCase().trim();
  u.role  = String(u.role || 'recruiter').toLowerCase();
  if (!ROLES.includes(u.role)) return { ok: false, error: 'INVALID_ROLE' };
  if (actor.role === 'team_lead' || actor.role === 'individual_contributor') { u.role = 'recruiter'; u.team = actor.team; }
  const existing = await findUser(u.email);
  if (existing) {
    if (isTLLike(actor.role) && actor.role !== 'super_admin' && existing.team !== actor.team) return { ok: false, error: 'FORBIDDEN' };
    await writeUserFields(u.email, {
      'Name':               u.name  !== undefined ? u.name  : existing.name,
      'Role':               u.role,
      'Team':               u.team  !== undefined ? u.team  : existing.team,
      'Daily Minute Limit': u.dailyMinuteLimit !== undefined ? Number(u.dailyMinuteLimit) : existing.dailyMinuteLimit,
      'Active':             u.active !== undefined ? !!u.active : existing.active,
    });
    audit(actor.email, 'update_user', u.email, '').catch(() => {});
    return { ok: true };
  }
  // New user
  const tok = crypto.randomUUID();
  const exp = new Date(Date.now() + SETUP_TOKEN_TTL_MS).toISOString();
  const row = [u.email, u.name || u.email, u.role, u.team || '', Number(u.dailyMinuteLimit || 0), false, '', '', tok, exp, new Date().toISOString(), actor.email];
  await appendRows(MAIN_SS_ID, S.USERS, [row]);
  _usersCache = null;
  const url  = `${DASHBOARD_URL}/?token=${encodeURIComponent(tok)}`;
  sendEmail(u.email, "You're invited to the Portal", inviteEmailHtml({ email: u.email, name: u.name || u.email, role: u.role, team: u.team || '' }, url, false)).catch(() => {});
  audit(actor.email, 'create_user', u.email, '').catch(() => {});
  return { ok: true, invited: true };
}

async function handleResendInvite(actor, body) {
  const email = String(body.email || '').toLowerCase().trim();
  const user  = await findUser(email);
  if (!user) return { ok: false, error: 'NOT_FOUND' };
  const tok = crypto.randomUUID();
  const exp = new Date(Date.now() + SETUP_TOKEN_TTL_MS).toISOString();
  await writeUserFields(email, { 'Setup Token': tok, 'Setup Token Expires': exp });
  const url = `${DASHBOARD_URL}/?token=${encodeURIComponent(tok)}`;
  sendEmail(email, user.passwordHash ? 'Reset your portal password' : "You're invited", inviteEmailHtml(user, url, !!user.passwordHash)).catch(() => {});
  return { ok: true };
}

async function handleDeleteUser(actor, body) {
  const email  = String(body.email || '').toLowerCase().trim();
  const target = await findUser(email);
  if (!target) return { ok: false, error: 'NOT_FOUND' };
  if (target.email === actor.email) return { ok: false, error: 'CANNOT_DEACTIVATE_SELF' };
  if (actor.role !== 'super_admin' && isTLLike(actor.role)) {
    if (target.role !== 'recruiter') return { ok: false, error: 'FORBIDDEN' };
    if (target.team !== actor.team)  return { ok: false, error: 'FORBIDDEN_CROSS_TEAM' };
  }
  await writeUserFields(email, { 'Active': false });
  audit(actor.email, 'deactivate_user', email, '').catch(() => {});
  return { ok: true };
}

async function handleSetLimit(actor, body) {
  const email   = String(body.email || '').toLowerCase().trim();
  const minutes = Number(body.minutes);
  if (isNaN(minutes) || minutes < 0) return { ok: false, error: 'INVALID_MINUTES' };
  const target = await findUser(email);
  if (!target) return { ok: false, error: 'USER_NOT_FOUND' };
  if (actor.role === 'super_admin' || (isTLLike(actor.role) && target.role === 'recruiter' && target.team === actor.team)) {
    await writeUserFields(email, { 'Daily Minute Limit': minutes });
    audit(actor.email, 'set_limit', email, String(minutes)).catch(() => {});
    return { ok: true };
  }
  return { ok: false, error: 'FORBIDDEN' };
}

// ─── Teams ─────────────────────────────────────────────────────────────────────
async function handleListTeams(actor) {
  let teams = await getAllTeams();
  if (isTLLike(actor.role) && actor.role !== 'super_admin') teams = teams.filter(t => t.name === actor.team);
  if (actor.role === 'recruiter') teams = [];
  return { ok: true, teams };
}

async function handleUpsertTeam(actor, body) {
  if (actor.role !== 'super_admin') return { ok: false, error: 'FORBIDDEN' };
  const t = body.team || {};
  if (!t.name) return { ok: false, error: 'NAME_REQUIRED' };
  const teams = await getAllTeams();
  const existing = teams.find(tm => tm.name === t.name);
  if (existing && existing.spreadsheetId) { _teamsCache = null; return { ok: true }; }
  // Create spreadsheet for team
  let ssId = existing?.spreadsheetId || '';
  if (!ssId) {
    ssId = await createSpreadsheet(`Voxa Team: ${t.name}`);
    if (SERVICE_EMAIL) await shareSpreadsheet(ssId, SERVICE_EMAIL);
  }
  await initTeamSS(ssId);
  if (existing) {
    // Update existing row
    const { headers, rows } = await readSheet(MAIN_SS_ID, S.TEAMS);
    const ni = headers.indexOf('Team Name');
    const si = headers.indexOf('Spreadsheet ID');
    for (let i = 0; i < rows.length; i++) {
      if (String(rows[i][ni] || '') === t.name) {
        if (si >= 0) { const r = [...rows[i]]; r[si] = ssId; await writeRow(MAIN_SS_ID, S.TEAMS, i + 2, r); }
        break;
      }
    }
  } else {
    const id = crypto.randomUUID().slice(0, 8);
    await appendRows(MAIN_SS_ID, S.TEAMS, [[id, t.name, new Date().toISOString(), ssId]]);
  }
  _teamsCache = null;
  audit(actor.email, 'upsert_team', t.name, `ssId=${ssId}`).catch(() => {});
  return { ok: true, spreadsheetId: ssId };
}

// ─── Agents ─────────────────────────────────────────────────────────────────────
async function handleListAgents(actor) {
  const [agents, users] = await Promise.all([getAllAgents(), getAllUsers()]);
  if (actor.role === 'super_admin') return { ok: true, agents: agents.map(publicAgent) };
  return { ok: true, agents: agentsVisibleTo(actor, agents, users).map(publicAgent) };
}

async function handleAddAgentById(actor, body) {
  if (!isTLLike(actor.role)) return { ok: false, error: 'FORBIDDEN' };
  const agentId = String(body.agentId || '').trim();
  if (!agentId) return { ok: false, error: 'AGENT_ID_REQUIRED' };
  const uuidRe = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
  if (!uuidRe.test(agentId)) return { ok: false, error: 'INVALID_AGENT_ID_FORMAT' };
  const fetch = await hunarGet(`/external/v1/agents/${encodeURIComponent(agentId)}/`);
  if (!fetch.ok) return { ok: false, error: 'HUNAR_FETCH_FAILED', message: fetch.error };
  const d = fetch.data;
  const existing = await findAgentByHunarId(d.id);
  if (existing && existing.spreadsheetId) {
    await shareSpreadsheet(existing.spreadsheetId, actor.email);
    await writeAgentRow({ ...existing, active: true, lastSynced: new Date().toISOString() });
    _agentsCache = null;
    return { ok: true, created: false, agentCode: existing.agentCode, agentId: d.id, displayName: d.name, spreadsheetId: existing.spreadsheetId, message: 'Agent exists. Spreadsheet shared with you.' };
  }
  // New agent
  const baseCode = slug(d.name || d.id);
  const suffix   = slug(actor.email.split('@')[0]);
  const agents   = await getAllAgents();
  let agentCode  = `${baseCode}_${suffix}`;
  let n = 1;
  while (agents.find(a => a.agentCode === agentCode)) agentCode = `${baseCode}_${suffix}_${++n}`;
  let ssId;
  try {
    ssId = await createSpreadsheet(`Voxa Agent: ${agentCode}`);
  } catch (e) {
    return { ok: false, error: 'SPREADSHEET_CREATE_FAILED', message: e.message + ' — Check that GOOGLE_SERVICE_ACCOUNT_B64 env var is set on Render.' };
  }
  // Share is non-fatal — fails silently if Drive API not enabled
  shareSpreadsheet(ssId, SERVICE_EMAIL, actor.email).catch(() => {});
  const agentObj = {
    agentCode, agentId: d.id, displayName: d.name, description: d.summary || '',
    language: d.language || 'ENGLISH', voicePersona: d.voice_persona || '',
    customVariables: d.custom_variables || [], resultSchema: d.result_schema || {},
    qualificationField: defaultQualField(d.result_schema), qualificationValues: [],
    qualificationRules: [], estSecondsPerCall: 60, active: true,
    createdBy: actor.email, addedById: true, agentPrompt: '', resultPrompt: '',
    introduction: '', clientName: '', spreadsheetId: ssId,
  };
  await initAgentSS(ssId, agentObj);
  await writeAgentRow(agentObj);
  _agentsCache = null;
  audit(actor.email, 'add_agent_by_id', agentCode, `hunarId=${d.id} ssId=${ssId}`).catch(() => {});
  return { ok: true, created: true, agentCode, agentId: d.id, displayName: d.name, spreadsheetId: ssId, message: 'Agent added. Spreadsheet created and shared with you.' };
}

async function handleSyncAgents(actor, body) {
  if (actor.role !== 'super_admin') return { ok: false, error: 'FORBIDDEN' };
  const list = await hunarGet('/external/v1/agents/?page=1&page_size=200');
  if (!list.ok) return { ok: false, error: 'HUNAR_API_ERROR', message: list.error };
  const items = (list.data.results || []);
  const results = [];
  for (const summary of items) {
    const detail = await hunarGet(`/external/v1/agents/${encodeURIComponent(summary.id)}/`);
    if (!detail.ok) continue;
    const d = detail.data;
    const exist = await findAgentByHunarId(d.id);
    const code  = exist ? exist.agentCode : slug(d.name || d.id);
    let ssId    = exist?.spreadsheetId || '';
    if (!ssId) {
      ssId = await createSpreadsheet(`Voxa Agent: ${code}`);
      if (SERVICE_EMAIL) await shareSpreadsheet(ssId, SERVICE_EMAIL);
      const tmp = { agentCode: code, customVariables: d.custom_variables || [], resultSchema: d.result_schema || {} };
      await initAgentSS(ssId, tmp);
    }
    const merged = {
      agentCode: code, agentId: d.id,
      displayName:         exist ? exist.displayName || d.name : d.name,
      description:         exist ? exist.description || d.summary || '' : d.summary || '',
      language:            d.language || 'ENGLISH', voicePersona: d.voice_persona || '',
      customVariables:     d.custom_variables || [], resultSchema: d.result_schema || {},
      qualificationField:  exist ? exist.qualificationField : defaultQualField(d.result_schema),
      qualificationValues: exist ? exist.qualificationValues || [] : [],
      qualificationRules:  exist ? exist.qualificationRules  || [] : [],
      estSecondsPerCall:   exist ? exist.estSecondsPerCall : 60,
      active:              exist ? exist.active : false,
      createdBy:           exist ? exist.createdBy : actor.email,
      addedById:           exist ? !!exist.addedById : false,
      agentPrompt:         exist ? exist.agentPrompt  || '' : '',
      resultPrompt:        exist ? exist.resultPrompt || '' : '',
      introduction:        exist ? exist.introduction || '' : '',
      clientName:          exist ? exist.clientName   || '' : '',
      spreadsheetId:       ssId,
    };
    await writeAgentRow(merged);
    results.push({ id: d.id, code, ok: true, ssId });
    await sleep(500);
  }
  _agentsCache = null;
  audit(actor.email, 'sync_agents', String(items.length), '').catch(() => {});
  return { ok: true, synced: results.length, results };
}

async function handleUpsertAgent(actor, body) {
  if (actor.role !== 'super_admin' && !isTLLike(actor.role)) return { ok: false, error: 'FORBIDDEN' };
  const a = body.agent || {};
  if (!a.agentCode) return { ok: false, error: 'AGENT_CODE_REQUIRED' };
  a.agentCode = slug(a.agentCode);
  const exist  = await findAgent(a.agentCode);
  const merged = exist ? { ...exist } : { agentCode: a.agentCode, agentId: '', createdBy: actor.email, addedById: false, spreadsheetId: '' };
  const str  = ['agentId','displayName','description','language','voicePersona','qualificationField','agentPrompt','resultPrompt','introduction','clientName'];
  str.forEach(k => { if (a[k] !== undefined) merged[k] = a[k]; });
  if (a.estSecondsPerCall !== undefined) merged.estSecondsPerCall = Number(a.estSecondsPerCall);
  if (a.customVariables   !== undefined) merged.customVariables   = a.customVariables;
  if (a.resultSchema      !== undefined) merged.resultSchema      = a.resultSchema;
  if (a.active            !== undefined) merged.active            = !!a.active;
  // Defensively parse in case frontend sends as JSON string instead of array
  let qRules = a.qualificationRules;
  if (typeof qRules === 'string') { try { qRules = JSON.parse(qRules); } catch (_) { qRules = []; } }
  if (Array.isArray(qRules)) merged.qualificationRules = qRules;

  let qValues = a.qualificationValues;
  if (typeof qValues === 'string') { try { qValues = JSON.parse(qValues); } catch (_) { qValues = []; } }
  if (Array.isArray(qValues)) merged.qualificationValues = qValues.filter(Boolean);
  if (!merged.spreadsheetId) {
    const ssId = await createSpreadsheet(`Voxa Agent: ${merged.agentCode}`);
    if (SERVICE_EMAIL) await shareSpreadsheet(ssId, SERVICE_EMAIL, actor.email);
    await initAgentSS(ssId, merged);
    merged.spreadsheetId = ssId;
  }
  await writeAgentRow(merged);
  _agentsCache = null;
  audit(actor.email, 'upsert_agent', merged.agentCode, '').catch(() => {});
  return { ok: true };
}

async function handleDeleteAgent(actor, body) {
  if (actor.role !== 'super_admin') return { ok: false, error: 'FORBIDDEN' };
  const code = String(body.agentCode || '').trim();
  const exist = await findAgent(code);
  if (!exist) return { ok: false, error: 'NOT_FOUND' };
  await writeAgentRow({ ...exist, active: false });
  _agentsCache = null;
  return { ok: true };
}

async function handleRepairAgentSheets(actor) {
  if (actor.role !== 'super_admin') return { ok: false, error: 'FORBIDDEN' };
  const agents = await getAllAgents();
  let fixed = 0;
  for (const agent of agents) {
    if (!agent.spreadsheetId) continue;
    try { await initAgentSS(agent.spreadsheetId, agent); fixed++; } catch (e) { console.error('[repair]', agent.agentCode, e.message); }
  }
  return { ok: true, fixed };
}

// ─── Campaign / Upload Contacts ────────────────────────────────────────────────
async function handleUploadContacts(actor, body) {
  const agentCode = String(body.agentCode || '').trim();
  const rows      = body.rows || [];
  if (!agentCode) return { ok: false, error: 'AGENT_CODE_REQUIRED' };
  if (!rows.length) return { ok: false, error: 'NO_ROWS' };
  const agent = await findAgent(agentCode);
  if (!agent)               return { ok: false, error: 'AGENT_NOT_FOUND' };
  if (!agent.active)        return { ok: false, error: 'AGENT_INACTIVE' };
  if (!agent.spreadsheetId) return { ok: false, error: 'AGENT_NO_SPREADSHEET' };
  const agents = await getAllAgents();
  const usersVis = await getAllUsers();
  if (!agentsVisibleTo(actor, agents, usersVis).find(a => a.agentCode === agentCode)) return { ok: false, error: 'AGENT_NOT_VISIBLE' };

  const estMin = rows.length * agent.estSecondsPerCall / 60;
  if (actor.role !== 'super_admin') {
    const usage = await todayUsageFor(actor.email);
    const rem   = actor.dailyMinuteLimit - usage.minutes;
    if (estMin > rem) return { ok: false, error: 'LIMIT_EXCEEDED', message: `Estimated ${Math.ceil(estMin)} min; you have ${Math.floor(rem)} min left.` };
  }

  const now    = new Date();
  const dateTs = now.toISOString().slice(0, 19).replace(/[-:T]/g, '').slice(0, 15);
  const reqId  = `portal_${dateTs}_${actor.email.split('@')[0].replace(/[^a-z0-9]/gi, '').slice(0, 8)}`;
  const cv     = agent.customVariables || [];

  const payload = {
    agent_id: agent.agentId, request_id: reqId,
    data: rows.map(r => {
      const cd = {};
      cv.forEach(k => { if (r.custom_data?.[k] !== undefined) cd[k] = String(r.custom_data[k] || ''); });
      return { callee_name: String(r.callee_name || '').trim(), mobile_number: String(r.mobile_number || '').trim(), custom_data: cd };
    }),
    remove_invalid_rows: true, remove_duplicate_phone_numbers: true, timezone: IST_TZ,
  };

  const apiRes = await hunarPost('/external/v1/calls/bulk/', payload);
  if (!apiRes.ok) return { ok: false, error: 'HUNAR_API_ERROR', message: apiRes.error };
  const calls  = Array.isArray(apiRes.data) ? apiRes.data : [];
  const ssId   = agent.spreadsheetId;

  // Seed Call_Input
  const ciH   = await _getSheetHeaders(ssId, AGT.CI);
  const ciRows = rows.map((r, i) => {
    const row = new Array(ciH.length).fill('');
    const set = (n, v) => { const k = ciH.indexOf(n); if (k >= 0) row[k] = v; };
    set('Row ID', `${reqId}_${i + 1}`);
    set('Uploaded At', now.toISOString());
    set('Request ID', reqId);
    set('Triggered By', actor.email);
    set('Callee Name', r.callee_name || '');
    set('Mobile Number', r.mobile_number || '');
    cv.forEach(k => { const ki = ciH.indexOf(k); if (ki >= 0) row[ki] = r.custom_data?.[k] || ''; });
    return row;
  });
  if (ciRows.length) await appendRows(ssId, AGT.CI, ciRows);

  // Seed Campaign_Tracker
  const campName = `Portal_${actor.email.split('@')[0].slice(0, 8)}_${dateTs}`;
  await appendRows(ssId, AGT.CT, [[reqId, campName, actor.email, now.toISOString(), rows.length, 'IN_PROGRESS', 0, 0, 0, 0, 0, 0, Math.round(estMin * 10) / 10, now.toISOString()]]);

  // Seed Master_Tracker
  if (calls.length) {
    const mtH  = await _getSheetHeaders(ssId, AGT.MT);
    const seen = new Set();
    const mtRows = [];
    calls.forEach(c => {
      const cid = String(c.id || '').trim();
      if (!cid || seen.has(cid)) return;
      seen.add(cid);
      const row = new Array(mtH.length).fill('');
      const set = (n, v) => { const k = mtH.indexOf(n); if (k >= 0) row[k] = v; };
      set('Call ID', cid); set('Request ID', c.request_id || reqId);
      set('Callee Name', c.callee_name || ''); set('Mobile Number', c.mobile_number || '');
      set('Status', c.status || 'INITIATED'); set('Triggered By', actor.email);
      set('Created At', now.toISOString());
      mtRows.push(row);
    });
    if (mtRows.length) await appendRows(ssId, AGT.MT, mtRows);
  }

  // Trigger log
  const users = await getAllUsers();
  const actorFull = users.find(u => u.email === actor.email);
  await appendRows(MAIN_SS_ID, S.TLOG, [[now.toISOString(), actor.email, actorFull?.name || '', actor.team || '', agentCode, reqId, rows.length, estMin]]);
  audit(actor.email, 'trigger_campaign', `${agentCode}:${reqId}`, String(rows.length)).catch(() => {});
  return { ok: true, agentCode, requestId: reqId, contactsSubmitted: rows.length, contactsAccepted: calls.length, estimatedMinutes: Math.round(estMin * 100) / 100 };
}

async function _getSheetHeaders(ssId, sheetName) {
  try {
    const { headers } = await readSheet(ssId, sheetName);
    return headers;
  } catch (_) { return []; }
}

// ─── Leads ─────────────────────────────────────────────────────────────────────
async function handleGetLeads(actor, body) {
  const agents = await getAllAgents();
  const users2 = await getAllUsers();
  const vis    = agentsVisibleTo(actor, agents, users2);
  const users  = await getAllUsers();
  const visEmails = new Set(visibleUserEmails(actor, users).map(e => e.toLowerCase()));
  const agentCode = String(body.agentCode || '').trim();
  const filter    = body.filter || {};
  const targets   = agentCode ? vis.filter(a => a.agentCode === agentCode) : vis;
  let allLeads = [];
  let headers  = [];
  for (const agent of targets) {
    if (!agent.spreadsheetId) continue;
    try {
      const { headers: h, rows } = await readSheet(agent.spreadsheetId, AGT.QL);
      if (!h.length) continue;
      if (!headers.length) headers = h;
      let leads = rows.map(r => {
        const o = { _agent: agent.agentCode, _ssId: agent.spreadsheetId };
        h.forEach((hh, j) => { o[hh] = r[j]; });
        return o;
      });
      if (actor.role === 'recruiter' || actor.role === 'individual_contributor') {
        leads = leads.filter(l => String(l['Assigned To Email'] || '').toLowerCase() === actor.email);
      } else if (actor.role === 'team_lead') {
        leads = leads.filter(l => { const a = String(l['Assigned To Email'] || '').toLowerCase(); return !a || visEmails.has(a); });
      }
      if (filter.requestId) leads = leads.filter(l => String(l['Request ID'] || '') === String(filter.requestId));
      if (filter.search) {
        const s = String(filter.search).toLowerCase();
        leads = leads.filter(l => (String(l['Callee Name'] || '') + ' ' + String(l['Mobile Number'] || '')).toLowerCase().includes(s));
      }
      allLeads.push(...leads);
    } catch (_) {}
  }
  return { ok: true, leads: allLeads, headers, agentCode };
}

async function handleUpdateLead(actor, body) {
  const agentCode = String(body.agentCode || '').trim();
  const callId    = String(body.callId || body.leadId || '');
  if (!agentCode || !callId) return { ok: false, error: 'REQUIRED_FIELDS_MISSING' };
  const agent = await findAgent(agentCode);
  if (!agent || !agent.spreadsheetId) return { ok: false, error: 'AGENT_NOT_FOUND' };
  const { headers, rows } = await readSheet(agent.spreadsheetId, AGT.QL);
  const idCol = headers.indexOf('Call ID');
  if (idCol < 0) return { ok: false, error: 'CALL_ID_COL_MISSING' };
  const ALLOWED = ['Call Status','Feedback','Selection Process','Turnup Status','Remarks','Recruiter'];
  for (let i = 0; i < rows.length; i++) {
    if (String(rows[i][idCol] || '') !== callId) continue;
    const assigned = String(rows[i][headers.indexOf('Assigned To Email')] || '').toLowerCase();
    if ((actor.role === 'recruiter' || actor.role === 'individual_contributor') && assigned !== actor.email) return { ok: false, error: 'FORBIDDEN' };
    const newRow   = [...rows[i]];
    const rejected = [];
    const fields   = body.fields || {};
    Object.keys(fields).forEach(k => {
      if (!ALLOWED.includes(k)) { rejected.push(k); return; }
      const col = headers.indexOf(k);
      if (col < 0) return;
      newRow[col] = fields[k];
      if (k === 'Remarks') {
        const tc = headers.indexOf('Remarks Updated At');
        const bc = headers.indexOf('Remarks Updated By');
        if (tc >= 0) newRow[tc] = new Date().toISOString();
        if (bc >= 0) newRow[bc] = actor.name || actor.email;
      }
    });
    await writeRow(agent.spreadsheetId, AGT.QL, i + 2, newRow);
    // Lineup hook
    if (fields['Feedback'] && _isInterviewLinedUp(fields['Feedback'])) {
      _addToLineupFromAI(actor, agent, newRow, headers, callId).catch(() => {});
    }
    audit(actor.email, 'update_lead', `${agentCode}:${callId}`, Object.keys(fields).join(',')).catch(() => {});
    return { ok: true, rejected };
  }
  return { ok: false, error: 'NOT_FOUND' };
}

function _isInterviewLinedUp(val) {
  const low = String(val || '').toLowerCase().trim();
  return low.includes('interview lined up') || low.includes('interested: interview') || low.includes('interested - interview') || low.includes('interested – interview');
}

async function _addToLineupFromAI(actor, agent, row, headers, callId) {
  try {
    const users  = await getAllUsers();
    const actorF = users.find(u => u.email === actor.email);
    if (!actorF?.team) return;
    // Use central SS (LINEUP_SS_ID) if configured, else per-team SS
    if (LINEUP_SS_ID) {
      await _addToLineup(LINEUP_SS_ID, 'AI', { agent, row, headers, callId, lineupSheet: actorF.team });
    } else {
      const team = await findTeam(actorF.team);
      if (!team?.spreadsheetId) return;
      await _addToLineup(team.spreadsheetId, 'AI', { agent, row, headers, callId, lineupSheet: TEAM_SH.LINEUP });
    }
  } catch (_) {}
}

async function _addToLineup(ssId, source, payload) {
  // lineupSheet = tab name (team name for central SS, 'Interview_Lineup' for per-team SS)
  const sheetName = payload.lineupSheet || TEAM_SH.LINEUP;
  await ensureSheet(ssId, sheetName, LINEUP_H, '#5b21b6');
  const { headers: h } = await readSheet(ssId, sheetName);
  const out  = {};
  LINEUP_H.forEach(hh => { out[hh] = ''; });
  let lookupId = '';

  if (source === 'AI') {
    const { agent, row, headers: mh, callId } = payload;
    lookupId = callId;
    const g  = n => { const i = mh.indexOf(n); return i >= 0 ? row[i] : ''; };
    const go = n => g(`out.${n}`);
    const sa = g('Started At');
    let month = '';
    try { if (sa) month = new Date(sa).toISOString().slice(0, 7); } catch (_) {}
    Object.assign(out, {
      'Source': 'AI', 'Call ID': callId, 'Callee Name': g('Callee Name'),
      'Mobile Number': g('Mobile Number'), 'Agent Code': agent.agentCode,
      'Agent Name': agent.displayName, 'Request ID': g('Request ID'),
      'Started At': sa, 'Month': month,
      'Assigned Recruiter Email': g('Assigned To Email'), 'Assigned Recruiter Name': g('Recruiter'),
      'Client': agent.clientName || '', 'Date Added': new Date().toISOString(),
    });
    const pick = (...cs) => { for (const c of cs) { const v = go(c); if (v) return String(v); } return ''; };
    out['Email']           = pick('email','Email','email_id');
    out['DOB']             = pick('dob','DOB','date_of_birth');
    out['Qualification']   = pick('qualification','Qualification','education');
    out['Work Experience'] = pick('work_experience','experience','total_experience');
    out['Current CTC']     = pick('current_ctc','ctc');
    out['Expected CTC']    = pick('expected_ctc','expectedCtc');
    out['Notice Period']   = pick('notice_period','noticePeriod');
    out['Role']            = pick('role','Role','job_role');
    out['Location']        = pick('location','Location','city');
    out['Current Employer']= pick('current_employer','employer','company');
    out['CV Link']         = pick('cv_link','cv','resume');
  } else if (source === 'Manual') {
    const { entry, uniqueId } = payload;
    lookupId = `MT_${uniqueId}`;
    let month = '';
    try { if (entry['Date']) month = new Date(entry['Date']).toISOString().slice(0, 7); } catch (_) {}
    Object.assign(out, {
      'Source': 'Manual', 'Call ID': lookupId,
      'Callee Name': String(entry['Candidate Name'] || ''), 'Mobile Number': String(entry['Contact Number'] || ''),
      'Assigned Recruiter Email': String(entry['Added By Email'] || ''), 'Assigned Recruiter Name': String(entry['Added By Name'] || ''),
      'Client': String(entry['Client'] || ''), 'Role': String(entry['Role'] || ''),
      'Location': String(entry['Location'] || ''), 'Date Added': new Date().toISOString(), 'Month': month,
    });
  }

  // Idempotency check
  const { rows: existRows } = await readSheet(ssId, sheetName);
  const cc = h.indexOf('Call ID');
  if (cc >= 0 && existRows.some(r => String(r[cc] || '').trim() === lookupId)) return { ok: true, action: 'exists' };
  const rowVals = h.map(hh => out[hh] !== undefined ? out[hh] : '');
  await appendRows(ssId, sheetName, [rowVals]);
  return { ok: true, action: 'appended' };
}

async function handleAssignLead(actor, body) {
  if (actor.role === 'recruiter') return { ok: false, error: 'FORBIDDEN' };
  const agentCode     = String(body.agentCode || '').trim();
  const callId        = String(body.callId || body.leadId || '');
  const recruiterEmail = String(body.recruiterEmail || '').toLowerCase().trim();
  if (!callId || !recruiterEmail) return { ok: false, error: 'CALLID_AND_EMAIL_REQUIRED' };
  const [agent, target] = await Promise.all([findAgent(agentCode), findUser(recruiterEmail)]);
  if (!agent || !agent.spreadsheetId) return { ok: false, error: 'AGENT_NOT_FOUND' };
  if (!target) return { ok: false, error: 'RECRUITER_NOT_FOUND' };
  const { headers, rows } = await readSheet(agent.spreadsheetId, AGT.QL);
  const idCol = headers.indexOf('Call ID');
  for (let i = 0; i < rows.length; i++) {
    if (String(rows[i][idCol] || '') !== callId) continue;
    const newRow = [...rows[i]];
    const ec = headers.indexOf('Assigned To Email'); const rc = headers.indexOf('Recruiter');
    if (ec >= 0) newRow[ec] = recruiterEmail;
    if (rc >= 0) newRow[rc] = target.name;
    await writeRow(agent.spreadsheetId, AGT.QL, i + 2, newRow);
    audit(actor.email, 'assign_lead', `${agentCode}:${callId}`, recruiterEmail).catch(() => {});
    return { ok: true };
  }
  return { ok: false, error: 'NOT_FOUND' };
}

async function handlePassToQL(actor, body) {
  const agentCode = String(body.agentCode || '').trim();
  const callId    = String(body.callId || '').trim();
  if (!agentCode || !callId) return { ok: false, error: 'REQUIRED_FIELDS_MISSING' };
  const agent = await findAgent(agentCode);
  if (!agent || !agent.spreadsheetId) return { ok: false, error: 'AGENT_NOT_FOUND' };
  const ssId = agent.spreadsheetId;
  const [{ headers: qh, rows: qr }, { headers: mh, rows: mr }] = await Promise.all([
    readSheet(ssId, AGT.QL), readSheet(ssId, AGT.MT),
  ]);
  const qi = qh.indexOf('Call ID');
  if (qi >= 0 && qr.some(r => String(r[qi] || '').trim() === callId)) return { ok: false, error: 'ALREADY_IN_QL' };
  const mi = mh.indexOf('Call ID');
  const mrow = mr.find(r => String(r[mi] || '').trim() === callId);
  if (!mrow) return { ok: false, error: 'NOT_FOUND_IN_MT' };
  const qrow = new Array(qh.length).fill('');
  qh.forEach((h, k) => { const mi2 = mh.indexOf(h); if (mi2 >= 0) qrow[k] = mrow[mi2]; });
  const ac = qh.indexOf('Assigned To Email'); const rc2 = qh.indexOf('Recruiter'); const dc = qh.indexOf('Date Added');
  if (ac >= 0) { qrow[ac] = actor.email; if (rc2 >= 0) qrow[rc2] = actor.name || actor.email; }
  if (dc >= 0) qrow[dc] = new Date().toISOString();
  await appendRows(ssId, AGT.QL, [qrow]);
  audit(actor.email, 'pass_to_ql', `${agentCode}:${callId}`, '').catch(() => {});
  return { ok: true };
}

// ─── Master Tracker / Not Connected ───────────────────────────────────────────
async function handleGetMasterTracker(actor, body) {
  const agentCode = String(body.agentCode || '').trim();
  if (!agentCode) return { ok: false, error: 'AGENT_CODE_REQUIRED' };
  const agent = await findAgent(agentCode);
  if (!agent || !agent.spreadsheetId) return { ok: false, error: 'AGENT_NOT_FOUND' };
  const usersVis = await getAllUsers();
  const { headers, rows } = await readSheet(agent.spreadsheetId, AGT.MT);
  const reqId = String(body.requestId || '');
  let result  = rows.map(r => { const o = {}; headers.forEach((h, i) => { o[h] = r[i]; }); return o; });
  if (reqId) result = result.filter(r => String(r['Request ID'] || '') === reqId);
  return { ok: true, rows: result, headers };
}

async function handleGetNotConnected(actor, body) {
  const agentCode = String(body.agentCode || '').trim();
  if (!agentCode) return { ok: false, error: 'AGENT_CODE_REQUIRED' };
  const agent = await findAgent(agentCode);
  if (!agent || !agent.spreadsheetId) return { ok: false, error: 'AGENT_NOT_FOUND' };
  const usersVis = await getAllUsers();
  const { headers, rows } = await readSheet(agent.spreadsheetId, AGT.NC);
  const reqId = String(body.requestId || '');
  let result  = rows.map(r => { const o = {}; headers.forEach((h, i) => { o[h] = r[i]; }); return o; });
  if (reqId) result = result.filter(r => String(r['Request ID'] || '') === reqId);
  return { ok: true, rows: result, headers };
}

// ─── Campaigns ─────────────────────────────────────────────────────────────────
async function handleGetCampaigns(actor, body) {
  const agents = await getAllAgents();
  const users  = await getAllUsers();
  const vis    = agentsVisibleTo(actor, agents, users);
  const visEmails = new Set(visibleUserEmails(actor, users).map(e => e.toLowerCase()));
  const emailToTeam = {};
  users.forEach(u => { if (u.team) emailToTeam[u.email] = u.team; });
  const agentCode = String(body.agentCode || '').trim();
  const targets   = agentCode ? vis.filter(a => a.agentCode === agentCode) : vis;
  const campaigns = [];
  for (const a of targets) {
    if (!a.spreadsheetId) continue;
    try {
      const { rows } = await readSheet(a.spreadsheetId, AGT.CT);
      rows.forEach(r => {
        if (!r[0]) return;
        const by = String(r[2] || '').toLowerCase().trim();
        if (actor.role === 'recruiter' && by !== actor.email) return;
        if (actor.role === 'individual_contributor' && by !== actor.email) return;
        if (actor.role === 'team_lead' && !visEmails.has(by)) return;
        campaigns.push({
          agentCode: a.agentCode, agentName: a.displayName,
          requestId: String(r[0]), campaignName: String(r[1] || ''),
          triggeredBy: by, triggeredByTeam: emailToTeam[by] || '',
          triggeredAt: r[3], contactsCount: r[4], status: r[5],
          completed: r[6], connected: r[7], notConnected: r[8], failed: r[9],
          qualified: r[10], actualMinutes: Math.round(Number(r[11] || 0) * 100) / 100,
          estimatedMinutes: r[12], lastUpdated: r[13],
        });
      });
    } catch (_) {}
  }
  campaigns.sort((a, b) => (a.triggeredAt < b.triggeredAt ? 1 : -1));
  return { ok: true, campaigns };
}

// ─── Dashboard ────────────────────────────────────────────────────────────────
async function handleGetDashboard(actor, body) {
  const range  = body.range || '7d';
  const days   = range === 'today' ? 0 : range === '30d' ? 30 : 7;
  const agents = await getAllAgents();
  const users  = await getAllUsers();
  const vis    = agentsVisibleTo(actor, agents, users);
  const visEmails = new Set(visibleUserEmails(actor, users).map(e => e.toLowerCase()));

  // Build trigger set
  let trigSet = new Set();
  if (actor.role !== 'super_admin') {
    try {
      const { headers: th, rows: tr } = await readSheet(MAIN_SS_ID, S.TLOG);
      if (th.length) {
        const ei = th.indexOf('User Email'); const ai = th.indexOf('Agent Code'); const ri = th.indexOf('Request ID');
        tr.forEach(r => { if (visEmails.has(String(r[ei] || '').toLowerCase())) trigSet.add(`${r[ai]}|${r[ri]}`); });
      }
    } catch (_) {}
  }

  let totalCalls = 0, totalMins = 0, qualCount = 0, lineupCount = 0;
  const byDay = {};
  const agentFilter = String(body.agentCode || '');
  const targets = agentFilter ? vis.filter(a => a.agentCode === agentFilter) : vis;

  const sinceDate = range === 'today'
    ? new Date(new Date().toLocaleDateString('en-CA', { timeZone: IST_TZ }) + 'T00:00:00+05:30')
    : new Date(Date.now() - days * 86400_000);

  for (const a of targets) {
    if (!a.spreadsheetId) continue;
    try {
      const { headers: mh, rows: mr } = await readSheet(a.spreadsheetId, AGT.MT);
      if (!mh.length) continue;
      const ri = mh.indexOf('Request ID'); const di = mh.indexOf('Duration (Minutes)');
      const si = mh.indexOf('Started At');  const ci = mh.indexOf('Created At');
      mr.forEach(r => {
        const rid = String(r[ri] || '');
        if (actor.role !== 'super_admin' && !trigSet.has(`${a.agentCode}|${rid}`)) return;
        const dv = r[si] || r[ci]; if (!dv) return;
        const d = new Date(dv); if (isNaN(d.getTime()) || d < sinceDate) return;
        const day = d.toLocaleDateString('en-CA', { timeZone: IST_TZ });
        totalCalls++;
        const dur = Math.round(Number(r[di] || 0) * 100) / 100;
        totalMins += dur;
        byDay[day] = byDay[day] || { calls: 0, minutes: 0, qualified: 0 };
        byDay[day].calls++; byDay[day].minutes += dur;
      });

      const { headers: qh, rows: qr } = await readSheet(a.spreadsheetId, AGT.QL);
      if (!qh.length) continue;
      const aec = qh.indexOf('Assigned To Email'); const fbc = qh.indexOf('Feedback'); const dac = qh.indexOf('Date Added');
      qr.forEach(r => {
        const assigned = String(r[aec] || '').toLowerCase();
        if ((actor.role === 'recruiter' || actor.role === 'individual_contributor') && assigned !== actor.email) return;
        if (actor.role === 'team_lead' && assigned && !visEmails.has(assigned)) return;
        qualCount++;
        const fb = String(r[fbc] || '').toLowerCase();
        if (_isInterviewLinedUp(fb)) lineupCount++;
        if (dac >= 0 && r[dac]) {
          const d = new Date(r[dac]);
          if (!isNaN(d.getTime()) && d >= sinceDate) {
            const day = d.toLocaleDateString('en-CA', { timeZone: IST_TZ });
            byDay[day] = byDay[day] || { calls: 0, minutes: 0, qualified: 0 };
            byDay[day].qualified = (byDay[day].qualified || 0) + 1;
          }
        }
      });
    } catch (_) {}
  }

  // ── Manual Tracker stats (from central SS) ───────────────────────────────
  let manualTotal = 0, manualConnected = 0, manualLinedUp = 0;
  const manualByTeam = {};

  if (MANUAL_TRACKER_SS_ID) {
    try {
      const users = await getAllUsers();
      const visTeams = actor.role === 'super_admin'
        ? (await getAllTeams()).map(t => t.name)
        : [actor.team].filter(Boolean);

      for (const teamName of visTeams) {
        try {
          const { headers, rows } = await readSheet(MANUAL_TRACKER_SS_ID, teamName);
          if (!headers.length) continue;
          const csi = headers.indexOf('Call Status');
          const lui = headers.indexOf('Lined-up');
          const dti = headers.indexOf('Date');
          const aei = headers.indexOf('Added By Email');

          let tTotal = 0, tConn = 0, tLined = 0;
          rows.forEach(r => {
            // date filter
            if (dti >= 0 && r[dti]) {
              const d = new Date(r[dti]);
              if (!isNaN(d.getTime()) && d < sinceDate) return;
            }
            // role filter — recruiter sees only their own
            if ((actor.role === 'recruiter' || actor.role === 'individual_contributor') && aei >= 0) {
              if (String(r[aei] || '').toLowerCase() !== actor.email) return;
            }
            tTotal++;
            if (csi >= 0 && String(r[csi] || '').toLowerCase().includes('connected')) tConn++;
            if (lui >= 0 && String(r[lui] || '').toLowerCase() === 'yes') tLined++;
          });

          manualTotal    += tTotal;
          manualConnected += tConn;
          manualLinedUp   += tLined;
          manualByTeam[teamName] = { total: tTotal, connected: tConn, linedUp: tLined };
        } catch (_) {}
      }
    } catch (_) {}
  }

  // ── Lineup stats (from central SS) ────────────────────────────────────────
  let lineupTotal = 0, lineupByTeam = {};

  if (LINEUP_SS_ID) {
    try {
      const visTeams = actor.role === 'super_admin'
        ? (await getAllTeams()).map(t => t.name)
        : [actor.team].filter(Boolean);

      for (const teamName of visTeams) {
        try {
          const { headers, rows } = await readSheet(LINEUP_SS_ID, teamName);
          if (!headers.length) continue;
          const aei = headers.indexOf('Assigned Recruiter Email');
          const dti = headers.indexOf('Date Added');
          let count = 0;
          rows.forEach(r => {
            if (dti >= 0 && r[dti]) {
              const d = new Date(r[dti]);
              if (!isNaN(d.getTime()) && d < sinceDate) return;
            }
            if ((actor.role === 'recruiter' || actor.role === 'individual_contributor') && aei >= 0) {
              if (String(r[aei] || '').toLowerCase() !== actor.email) return;
            }
            count++;
          });
          lineupTotal += count;
          lineupByTeam[teamName] = count;
        } catch (_) {}
      }
    } catch (_) {}
  }

  const timeSeries = Object.keys(byDay).sort().map(d => ({
    day: d, calls: byDay[d].calls, minutes: Math.round(byDay[d].minutes * 100) / 100, qualified: byDay[d].qualified || 0,
  }));
  return {
    ok: true, range,
    stats: {
      // AI call stats
      totalCalls, totalMinutes: Math.round(totalMins * 100) / 100,
      qualifiedLeads: qualCount, lineupCount,
      conversionRate: qualCount > 0 ? Math.round(lineupCount / qualCount * 1000) / 10 : 0,
      // Manual tracker stats
      manual: {
        total: manualTotal,
        connected: manualConnected,
        linedUp: manualLinedUp,
        byTeam: manualByTeam,
      },
      // Interview lineup stats
      lineup: {
        total: lineupTotal,
        byTeam: lineupByTeam,
      },
      // Combined
      combined: {
        totalLeads:   qualCount + manualTotal,
        totalLinedUp: lineupCount + manualLinedUp,
      },
    },
    timeSeries,
  };
}

async function handleGetUsage(actor) {
  const users = await getAllUsers();
  const vis   = new Set(visibleUserEmails(actor, users));
  try {
    const { headers: th, rows: tr } = await readSheet(MAIN_SS_ID, S.TLOG);
    if (!th.length) return { ok: true, recruiterMinutes: [] };
    const ei = th.indexOf('User Email'); const ti = th.indexOf('Timestamp');
    const mi = th.indexOf('Estimated Minutes'); const ci = th.indexOf('Contacts Count');
    const today   = istDateStr();
    const mtdFrom = new Date(new Date().getFullYear(), new Date().getMonth(), 1);
    const mbd = {}, mtu = {}, cbd = {}, ctu = {};
    tr.forEach(r => {
      const em = String(r[ei] || '').toLowerCase().trim();
      if (!em || !vis.has(em)) return;
      const d = new Date(r[ti] || 0); if (isNaN(d.getTime())) return;
      const day = d.toLocaleDateString('en-CA', { timeZone: IST_TZ });
      const mins = Number(r[mi] || 0); const calls = Number(r[ci] || 0);
      const dk = `${em}|${day}`;
      mbd[dk] = (mbd[dk] || 0) + mins; cbd[dk] = (cbd[dk] || 0) + calls;
      if (d >= mtdFrom) { mtu[em] = (mtu[em] || 0) + mins; ctu[em] = (ctu[em] || 0) + calls; }
    });
    const ub = {};
    users.forEach(u => { ub[u.email] = u; });
    const recruiterMinutes = [...vis].map(em => {
      const u = ub[em]; if (!u) return null;
      const tm = mbd[`${em}|${today}`] || 0;
      return {
        email: em, name: u.name, team: u.team, role: u.role,
        dailyLimit: u.dailyMinuteLimit,
        todayMinutes: Math.round(tm * 100) / 100,
        mtdMinutes:   Math.round((mtu[em] || 0) * 100) / 100,
        todayCalls:   cbd[`${em}|${today}`] || 0,
        mtdCalls:     ctu[em] || 0,
        todayUsagePct: u.dailyMinuteLimit > 0 ? Math.round(tm / u.dailyMinuteLimit * 100) : 0,
      };
    }).filter(Boolean).filter(r => r.mtdMinutes > 0 || r.todayMinutes > 0);
    recruiterMinutes.sort((a, b) => b.mtdMinutes - a.mtdMinutes);
    return { ok: true, recruiterMinutes };
  } catch (e) { return { ok: false, error: e.message }; }
}

// ─── Manual Tracker ────────────────────────────────────────────────────────────
async function handleGetManualTracker(actor, body) {
  const teamName = actor.role === 'super_admin' ? String(body.team || '') : actor.team;
  if (!teamName && actor.role !== 'super_admin') return { ok: true, rows: [] };

  // ── Central SS path (MANUAL_TRACKER_SS_ID env var set) ───────────────────
  // Data lives in Voxa Central Manual Tracker, one tab per team name.
  // This matches how handleGetDashboard already reads manual stats.
  if (MANUAL_TRACKER_SS_ID) {
    const visTeams = teamName
      ? [teamName]
      : (await getAllTeams()).map(t => t.name);
    const all = [];
    for (const tn of visTeams) {
      try {
        const { headers, rows } = await readSheet(MANUAL_TRACKER_SS_ID, tn);
        if (!headers.length) continue;
        rows.forEach(r => {
          const o = { _team: tn };
          headers.forEach((h, i) => { o[h] = r[i]; });
          if (o['Unique ID']) all.push(o);
        });
      } catch (_) {}
    }
    let data = all;
    if (actor.role === 'recruiter' || actor.role === 'individual_contributor') {
      data = data.filter(r => String(r['Added By Email'] || '').toLowerCase() === actor.email);
    }
    return { ok: true, rows: data };
  }

  // ── Per-team SS fallback (no central SS configured) ──────────────────────
  if (!teamName) {
    const teams = await getAllTeams(); const all = [];
    for (const t of teams) {
      if (!t.spreadsheetId) continue;
      try {
        const { headers, rows } = await readSheet(t.spreadsheetId, TEAM_SH.MANUAL);
        rows.forEach(r => { const o = { _team: t.name }; headers.forEach((h, i) => { o[h] = r[i]; }); if (o['Unique ID']) all.push(o); });
      } catch (_) {}
    }
    return { ok: true, rows: all };
  }
  const team = await findTeam(teamName);
  if (!team?.spreadsheetId) return { ok: true, rows: [], _warn: 'team has no spreadsheetId' };
  const { headers, rows } = await readSheet(team.spreadsheetId, TEAM_SH.MANUAL);
  let data = rows.map(r => { const o = {}; headers.forEach((h, i) => { o[h] = r[i]; }); return o; }).filter(r => r['Unique ID']);
  if (actor.role === 'recruiter') data = data.filter(r => String(r['Added By Email'] || '').toLowerCase() === actor.email);
  return { ok: true, rows: data };
}

async function handleAddManualEntry(actor, body) {
  const entry = body.entry || {};
  const name  = String(entry.candidateName || '').trim();
  const phone = String(entry.contactNumber || '').replace(/\D/g, '');
  if (!name)             return { ok: false, error: 'CANDIDATE_NAME_REQUIRED' };
  if (phone.length < 10) return { ok: false, error: 'INVALID_PHONE' };
  const teamName = actor.role === 'super_admin' ? String(body.team || entry.team || '') : actor.team;
  if (!teamName) return { ok: false, error: 'NO_TEAM' };

  // Resolve write target: central SS (one tab per team) or per-team SS
  let writeSSId, writeSheet;
  if (MANUAL_TRACKER_SS_ID) {
    writeSSId  = MANUAL_TRACKER_SS_ID;
    writeSheet = teamName; // tab named after team in the central SS
  } else {
    const team = await findTeam(teamName);
    if (!team?.spreadsheetId) return { ok: false, error: 'TEAM_NO_SPREADSHEET' };
    writeSSId  = team.spreadsheetId;
    writeSheet = TEAM_SH.MANUAL;
  }

  await ensureSheet(writeSSId, writeSheet, MANUAL_H, '#0369a1');
  const now = new Date();
  const uid = `MT_${now.toISOString().slice(0,19).replace(/[-:T]/g,'')}_ ${actor.email.split('@')[0].slice(0,6).toUpperCase()}`.replace(/\s/g,'');
  let dv = now;
  try { if (entry.date) dv = new Date(entry.date); } catch (_) {}
  const row = [uid, dv.toISOString(), name, phone, entry.location || '', entry.client || '', entry.role || '', entry.source || '', '', '', '', actor.email, actor.name || actor.email, teamName, false, now.toISOString()];
  await appendRows(writeSSId, writeSheet, [row]);
  audit(actor.email, 'add_manual_entry', uid, name).catch(() => {});
  return { ok: true, uniqueId: uid };
}

async function handleUpdateManualEntry(actor, body) {
  const uid = String(body.uniqueId || '').trim();
  if (!uid) return { ok: false, error: 'UNIQUE_ID_REQUIRED' };
  const teamName = actor.role === 'super_admin' ? String(body.team || '') : actor.team;
  if (!teamName) return { ok: false, error: 'NO_TEAM' };

  // Resolve SS + sheet (central or per-team)
  let ssId, sheetName;
  if (MANUAL_TRACKER_SS_ID) {
    ssId = MANUAL_TRACKER_SS_ID; sheetName = teamName;
  } else {
    const team = await findTeam(teamName);
    if (!team?.spreadsheetId) return { ok: false, error: 'TEAM_NOT_FOUND' };
    ssId = team.spreadsheetId; sheetName = TEAM_SH.MANUAL;
  }

  const { headers, rows } = await readSheet(ssId, sheetName);
  const idCol = headers.indexOf('Unique ID');
  if (idCol < 0) return { ok: false, error: 'MISSING_ID_COL' };
  const ALLOWED = ['Call Status','Lined-up','Remarks','Candidate Name','Contact Number','Client','Role','Source','Location','Date'];
  for (let i = 0; i < rows.length; i++) {
    if (String(rows[i][idCol] || '').trim() !== uid) continue;
    const newRow   = [...rows[i]];
    const rejected = [];
    const fields   = body.fields || {};
    Object.keys(fields).forEach(k => {
      if (!ALLOWED.includes(k)) { rejected.push(k); return; }
      const col = headers.indexOf(k); if (col < 0) return;
      let v = fields[k];
      if (k === 'Date' && v) { try { v = new Date(v).toISOString(); } catch (_) {} }
      newRow[col] = v;
    });
    await writeRow(ssId, sheetName, i + 2, newRow);
    // Lineup hook
    if (String(fields['Lined-up'] || '').toLowerCase().trim() === 'yes') {
      const entry = {};
      headers.forEach((h, j) => { entry[h] = newRow[j]; });
      const lineupSsId = LINEUP_SS_ID || ssId;
      const lineupSheet = LINEUP_SS_ID ? teamName : TEAM_SH.LINEUP;
      _addToLineup(lineupSsId, 'Manual', { entry, uniqueId: uid, lineupSheet }).catch(() => {});
      const ilCol = headers.indexOf('In Lineup');
      if (ilCol >= 0) { newRow[ilCol] = true; await writeRow(ssId, sheetName, i + 2, newRow); }
    }
    return { ok: true, rejected };
  }
  return { ok: false, error: 'NOT_FOUND' };
}

// ─── Interview Lineup ─────────────────────────────────────────────────────────
async function handleGetInterviewLineup(actor, body) {
  const teamName = actor.role === 'super_admin' ? String(body.team || '') : actor.team;
  if (!teamName && actor.role !== 'super_admin') return { ok: true, rows: [], headers: [] };

  // ── Central SS path (LINEUP_SS_ID env var set) ───────────────────────────
  if (LINEUP_SS_ID) {
    const visTeams = teamName
      ? [teamName]
      : (await getAllTeams()).map(t => t.name);
    const all = []; let firstHeaders = [];
    for (const tn of visTeams) {
      try {
        const { headers: h, rows } = await readSheet(LINEUP_SS_ID, tn);
        if (!h.length) continue;
        if (!firstHeaders.length) firstHeaders = h;
        rows.forEach(r => {
          const o = { _team: tn };
          h.forEach((hh, i) => { o[hh] = r[i]; });
          if (o['Call ID']) all.push(o);
        });
      } catch (_) {}
    }
    let data = all;
    if (actor.role === 'recruiter' || actor.role === 'individual_contributor') {
      data = data.filter(r => String(r['Assigned Recruiter Email'] || '').toLowerCase() === actor.email);
    }
    return { ok: true, rows: data, headers: firstHeaders };
  }

  // ── Per-team SS fallback ─────────────────────────────────────────────────
  if (!teamName) {
    const teams = await getAllTeams(); const all = []; let headers = [];
    for (const t of teams) {
      if (!t.spreadsheetId) continue;
      try {
        const { headers: h, rows } = await readSheet(t.spreadsheetId, TEAM_SH.LINEUP);
        if (!headers.length) headers = h;
        rows.forEach(r => { const o = { _team: t.name }; h.forEach((hh, i) => { o[hh] = r[i]; }); if (o['Call ID']) all.push(o); });
      } catch (_) {}
    }
    return { ok: true, rows: all, headers };
  }
  const team = await findTeam(teamName);
  if (!team?.spreadsheetId) return { ok: true, rows: [], headers: [], _warn: 'team has no spreadsheetId' };
  const { headers, rows } = await readSheet(team.spreadsheetId, TEAM_SH.LINEUP);
  let data = rows.map(r => { const o = {}; headers.forEach((h, i) => { o[h] = r[i]; }); return o; }).filter(r => r['Call ID']);
  if (actor.role === 'recruiter') data = data.filter(r => String(r['Assigned Recruiter Email'] || '').toLowerCase() === actor.email);
  return { ok: true, rows: data, headers };
}

async function handleUpdateInterviewLead(actor, body) {
  const callId   = String(body.callId || '').trim();
  if (!callId) return { ok: false, error: 'CALL_ID_REQUIRED' };
  const teamName = actor.role === 'super_admin' ? String(body.team || '') : actor.team;
  if (!teamName) return { ok: false, error: 'NO_TEAM' };

  // Resolve SS + sheet
  let ssId, sheetName;
  if (LINEUP_SS_ID) {
    ssId = LINEUP_SS_ID; sheetName = teamName;
  } else {
    const team = await findTeam(teamName);
    if (!team?.spreadsheetId) return { ok: false, error: 'NO_TEAM_SS' };
    ssId = team.spreadsheetId; sheetName = TEAM_SH.LINEUP;
  }

  const { headers, rows } = await readSheet(ssId, sheetName);
  const cc = headers.indexOf('Call ID');
  if (cc < 0) return { ok: false, error: 'NO_CALL_ID_COL' };
  const ALLOWED = ['Selection Process','Turnup Status','Email','DOB','Qualification','Work Experience','Current CTC','Expected CTC','Notice Period','Role','Location','CIBIL Score','SPOC Name','Current Employer','CV Link'];
  for (let i = 0; i < rows.length; i++) {
    if (String(rows[i][cc] || '').trim() !== callId) continue;
    const newRow   = [...rows[i]];
    const rejected = [];
    Object.keys(body.fields || {}).forEach(k => {
      if (!ALLOWED.includes(k)) { rejected.push(k); return; }
      const col = headers.indexOf(k); if (col >= 0) newRow[col] = body.fields[k];
    });
    await writeRow(ssId, sheetName, i + 2, newRow);
    return { ok: true, rejected };
  }
  return { ok: false, error: 'NOT_FOUND' };
}

// ─── Callbacks ────────────────────────────────────────────────────────────────
async function handleGetCallbacks(actor, body) {
  const agents = await getAllAgents();
  const usersForVis = await getAllUsers();
  const vis    = agentsVisibleTo(actor, agents, usersForVis);
  const agentCode = String(body.agentCode || '');
  const targets   = agentCode ? vis.filter(a => a.agentCode === agentCode) : vis;
  const all = [];
  for (const a of targets) {
    if (!a.spreadsheetId) continue;
    try {
      const { headers, rows } = await readSheet(a.spreadsheetId, AGT.CB);
      const ae = headers.indexOf('Assigned To Email');
      rows.forEach(r => {
        if ((actor.role === 'recruiter' || actor.role === 'individual_contributor') && String(r[ae] || '').toLowerCase() !== actor.email) return;
        const o = { _agent: a.agentCode }; headers.forEach((h, i) => { o[h] = r[i]; }); all.push(o);
      });
    } catch (_) {}
  }
  return { ok: true, callbacks: all };
}

// ─── Team Lists ───────────────────────────────────────────────────────────────
async function handleGetTeamLists(actor, body) {
  const team = actor.role === 'super_admin' ? String(body.team || '') : actor.team || '';
  const { headers, rows } = await readSheet(MAIN_SS_ID, S.TEAM_LST).catch(() => ({ headers: [], rows: [] }));
  if (!headers.length) return { ok: true, team, clients: [], roles: [] };
  const idx = h => headers.indexOf(h);
  const all = rows.map(r => ({
    team:  String(r[idx('Team')]  || ''), type: String(r[idx('Type')] || '').toLowerCase(),
    value: String(r[idx('Value')] || ''),
    addedBy: String(r[idx('Added By Name')] || r[idx('Added By Email')] || ''),
    addedAt: r[idx('Added At')] || '',
  })).filter(r => r.team && r.type && r.value);
  const scoped = team ? all.filter(r => r.team === team) : all;
  const clients = [], roles = [], sc = new Set(), sr = new Set();
  scoped.forEach(r => {
    if (r.type === 'client' && !sc.has(r.value.toLowerCase())) { sc.add(r.value.toLowerCase()); clients.push({ value: r.value, addedBy: r.addedBy, addedAt: r.addedAt }); }
    else if (r.type === 'role' && !sr.has(r.value.toLowerCase())) { sr.add(r.value.toLowerCase()); roles.push({ value: r.value, addedBy: r.addedBy, addedAt: r.addedAt }); }
  });
  return { ok: true, team, clients: clients.sort((a, b) => a.value.localeCompare(b.value)), roles: roles.sort((a, b) => a.value.localeCompare(b.value)) };
}

async function handleAddTeamListValue(actor, body) {
  if (!isTLLike(actor.role)) return { ok: false, error: 'FORBIDDEN' };
  const type  = String(body.type  || '').toLowerCase().trim();
  const value = String(body.value || '').trim();
  let team    = String(body.team  || '').trim();
  if (actor.role !== 'super_admin') team = actor.team || '';
  if (!team)  return { ok: false, error: 'NO_TEAM' };
  if (!['client', 'role'].includes(type)) return { ok: false, error: 'INVALID_TYPE' };
  if (!value) return { ok: false, error: 'VALUE_REQUIRED' };
  const { headers, rows } = await readSheet(MAIN_SS_ID, S.TEAM_LST).catch(() => ({ headers: [], rows: [] }));
  if (headers.length) {
    const ti = headers.indexOf('Team'); const yi = headers.indexOf('Type'); const vi = headers.indexOf('Value');
    if (rows.some(r => String(r[ti] || '') === team && String(r[yi] || '').toLowerCase() === type && String(r[vi] || '').toLowerCase() === value.toLowerCase())) {
      return { ok: true, duplicate: true };
    }
  }
  await appendRows(MAIN_SS_ID, S.TEAM_LST, [[team, type, value, actor.email, actor.name || actor.email, new Date().toISOString()]]);
  return { ok: true, added: true };
}

// ─── Support Queries ──────────────────────────────────────────────────────────
async function handleGetSupportQueries(actor) {
  const { headers, rows } = await readSheet(MAIN_SS_ID, S.SQ).catch(() => ({ headers: [], rows: [] }));
  if (!headers.length) return { ok: true, queries: [] };
  const idx = h => headers.indexOf(h);
  let data = rows.map(r => ({
    _id:           String(r[idx('Query ID')]      || ''),
    title:         String(r[idx('Title')]         || ''),
    description:   String(r[idx('Description')]   || ''),
    raisedByEmail: String(r[idx('Raised By Email')]|| ''),
    raisedByName:  String(r[idx('Raised By Name')] || ''),
    raisedAt:      r[idx('Raised At')] || '',
    status:        String(r[idx('Status')]         || 'Open'),
    resolution:    String(r[idx('Resolution')]     || ''),
    resolvedAt:    r[idx('Resolved At')] || '',
  })).filter(q => q._id);
  if (actor.role !== 'super_admin') data = data.filter(q => q.raisedByEmail.toLowerCase() === actor.email);
  data.sort((a, b) => (a.raisedAt < b.raisedAt ? 1 : -1));
  return { ok: true, queries: data };
}

async function handleRaiseSupportQuery(actor, body) {
  const title = String(body.title || '').trim();
  const desc  = String(body.description || '').trim();
  if (!title) return { ok: false, error: 'TITLE_REQUIRED' };
  if (!desc)  return { ok: false, error: 'DESCRIPTION_REQUIRED' };
  const now = new Date();
  const qid = `SQ_${now.toISOString().slice(0,19).replace(/[-:T]/g,'')}`;
  await appendRows(MAIN_SS_ID, S.SQ, [[qid, title, desc, '', '', actor.email, actor.name || actor.email, now.toISOString(), 'Open', '', '']]);
  const adminEmail = process.env.SUPER_ADMIN_EMAIL || 'vanshika@hunar.ai';
  sendEmail(adminEmail, `[Support] ${title}`, `<p><b>From:</b> ${actor.email}</p><p>${desc}</p>`).catch(() => {});
  return { ok: true, queryId: qid };
}

async function handleResolveSupportQuery(actor, body) {
  if (actor.role !== 'super_admin') return { ok: false, error: 'FORBIDDEN' };
  const qid = String(body.queryId || '').trim();
  const res = String(body.resolution || '').trim();
  if (!qid || !res) return { ok: false, error: 'REQUIRED' };
  const { headers, rows } = await readSheet(MAIN_SS_ID, S.SQ);
  const ic = headers.indexOf('Query ID');
  for (let i = 0; i < rows.length; i++) {
    if (String(rows[i][ic] || '').trim() !== qid) continue;
    const newRow = [...rows[i]];
    const sc = headers.indexOf('Status'); const rc = headers.indexOf('Resolution'); const xc = headers.indexOf('Resolved At');
    if (sc >= 0) newRow[sc] = body.status || 'Resolved';
    if (rc >= 0) newRow[rc] = res;
    if (xc >= 0) newRow[xc] = new Date().toISOString();
    await writeRow(MAIN_SS_ID, S.SQ, i + 2, newRow);
    const rbe = headers.indexOf('Raised By Email');
    const rEmail = rbe >= 0 ? String(rows[i][rbe] || '') : '';
    if (rEmail) sendEmail(rEmail, `[Support] Resolved`, `<p>Your query has been resolved: ${res}</p>`).catch(() => {});
    return { ok: true };
  }
  return { ok: false, error: 'NOT_FOUND' };
}

// ─── Admin actions ────────────────────────────────────────────────────────────
async function handleSetupSheets(actor) {
  if (actor.role !== 'super_admin') return { ok: false, error: 'FORBIDDEN' };
  const USERS_H   = ['Email','Name','Role','Team','Daily Minute Limit','Active','Password Hash','Password Salt','Setup Token','Setup Token Expires','Created On','Created By'];
  const TEAMS_H   = ['Team ID','Team Name','Created On','Spreadsheet ID'];
  const AGENTS_H  = ['Agent Code','Agent ID','Display Name','Description','Language','Voice Persona','Custom Variables','Result Schema','Qualification Field','Qualification Values','Qualification Rules','Est Seconds Per Call','Active','Last Synced','Created On','Created By','Added By ID','Agent Prompt','Result Prompt','Introduction','Client Name','Spreadsheet ID'];
  const SESS_H    = ['Token','Email','Created At','Expires At'];
  const AUDIT_H   = ['Timestamp','Actor Email','Action','Target','Details'];
  const TLOG_H    = ['Timestamp','User Email','User Name','Team','Agent Code','Request ID','Contacts Count','Estimated Minutes'];
  const SQ_H      = ['Query ID','Title','Description','Screenshot','Screenshot Name','Raised By Email','Raised By Name','Raised At','Status','Resolution','Resolved At'];
  const TLST_H    = ['Team','Type','Value','Added By Email','Added By Name','Added At'];
  const CBQ_H     = ['Queue ID','Agent Code','Agent ID','Call ID','Request ID','Callee Name','Mobile Number','Callback Field','Callback Value','Assigned To Email','Recruiter Name','Team','Scheduled Date','Status','New Request ID','Created At','Triggered At'];
  const RTQ_H     = ['Queue ID','Agent Code','Agent ID','Original Request ID','Team','Retry After Date','Status','Lead Count','New Request ID','Created At','Triggered At'];
  await Promise.all([
    ensureSheet(MAIN_SS_ID, S.USERS,    USERS_H,  '#2c3e50'),
    ensureSheet(MAIN_SS_ID, S.TEAMS,    TEAMS_H,  '#2c3e50'),
    ensureSheet(MAIN_SS_ID, S.AGENTS,   AGENTS_H, '#1a6fdc'),
    ensureSheet(MAIN_SS_ID, S.TLOG,     TLOG_H,   '#34495e'),
    ensureSheet(MAIN_SS_ID, S.SESSIONS, SESS_H,   '#7f8c8d'),
    ensureSheet(MAIN_SS_ID, S.AUDIT,    AUDIT_H,  '#7f8c8d'),
    ensureSheet(MAIN_SS_ID, S.CB_Q,     CBQ_H,    '#6739b7'),
    ensureSheet(MAIN_SS_ID, S.RETRY_Q,  RTQ_H,    '#b74e39'),
    ensureSheet(MAIN_SS_ID, S.TEAM_LST, TLST_H,   '#5b21b6'),
    ensureSheet(MAIN_SS_ID, S.SQ,       SQ_H,     '#be185d'),
  ]);
  // Bootstrap super admin if missing
  const adminEmail = (process.env.SUPER_ADMIN_EMAIL || 'vanshika@hunar.ai').toLowerCase();
  const users = await getAllUsers(true);
  if (!users.find(u => u.email === adminEmail)) {
    const bootstrapPw   = process.env.BOOTSTRAP_PASSWORD || 'ChangeMe@2026';
    const salt = crypto.randomUUID().replace(/-/g, '');
    const hash = hashPassword(bootstrapPw, salt);
    await appendRows(MAIN_SS_ID, S.USERS, [[adminEmail, adminEmail.split('@')[0], 'super_admin', '', 10000, true, hash, salt, '', '', new Date().toISOString(), 'system']]);
    _usersCache = null;
  }
  return { ok: true, message: 'Main SS sheets ready.' };
}

async function handleDedupeNow(actor) {
  if (actor.role !== 'super_admin') return { ok: false, error: 'FORBIDDEN' };
  try { const r = await dedupeAllSheets(); return { ok: true, ...r }; } catch (e) { return { ok: false, error: e.message }; }
}

// ═══════════════════════════════════════════════════════════════════════════════
// MAIN DISPATCH
// ═══════════════════════════════════════════════════════════════════════════════

async function handleAction(body) {
  const action = String(body.action || '').toLowerCase();

  // ── Public actions (no session) ──
  if (action === 'login')         return handleLogin(body);
  if (action === 'verifytoken')   return handleVerifyToken(body);
  if (action === 'completesetup') return handleCompleteSetup(body);
  if (action === 'requestreset')  return handleRequestReset(body);
  if (action === 'ping')          return { ok: true, t: new Date().toISOString() };

  // ── Authenticated actions ──
  const sess = await validateSession(body.session);
  if (!sess) return { ok: false, error: 'UNAUTHENTICATED' };
  const actor = await findUser(sess.email);
  if (!actor || !actor.active) return { ok: false, error: 'USER_INACTIVE' };

  switch (action) {
    case 'me':                   return handleMe(actor);
    case 'logout':               return handleLogout(body);
    case 'changepassword':       return handleChangePassword(actor, body);
    case 'listusers':            return handleListUsers(actor);
    case 'upsertuser':           return handleUpsertUser(actor, body);
    case 'resendinvite':         return handleResendInvite(actor, body);
    case 'deleteuser':           return handleDeleteUser(actor, body);
    case 'setlimit':             return handleSetLimit(actor, body);
    case 'listteams':            return handleListTeams(actor);
    case 'upsertteam':           return handleUpsertTeam(actor, body);
    case 'listagents':           return handleListAgents(actor);
    case 'syncagents':           return handleSyncAgents(actor, body);
    case 'upsertagent':
    case 'upsertmyagent':        return handleUpsertAgent(actor, body);
    case 'addagentbyid':         return handleAddAgentById(actor, body);
    case 'deleteagent':          return handleDeleteAgent(actor, body);
    case 'repairagentsheets':    return handleRepairAgentSheets(actor);
    case 'uploadcontacts':
    case 'triggercampaign':      return handleUploadContacts(actor, body);
    case 'getleads':             return handleGetLeads(actor, body);
    case 'updatelead':           return handleUpdateLead(actor, body);
    case 'assignlead':           return handleAssignLead(actor, body);
    case 'passtoqualifiedleads': return handlePassToQL(actor, body);
    case 'getdashboard':         return handleGetDashboard(actor, body);
    case 'getusage':             return handleGetUsage(actor);
    case 'getcampaigns':         return handleGetCampaigns(actor, body);
    case 'getmastertracker':     return handleGetMasterTracker(actor, body);
    case 'getnotconnected':      return handleGetNotConnected(actor, body);
    case 'getcampaignstats':     return { ok: true, stats: {} };
    case 'getmanualtracker':     return handleGetManualTracker(actor, body);
    case 'addmanualentry':       return handleAddManualEntry(actor, body);
    case 'updatemanualentry':    return handleUpdateManualEntry(actor, body);
    case 'getinterviewlineup':   return handleGetInterviewLineup(actor, body);
    case 'updateinterviewlead':  return handleUpdateInterviewLead(actor, body);
    case 'getcallbacks':         return handleGetCallbacks(actor, body);
    case 'getteamlists':         return handleGetTeamLists(actor, body);
    case 'addteamlistvalue':     return handleAddTeamListValue(actor, body);
    case 'getsupportqueries':    return handleGetSupportQueries(actor);
    case 'raisesupportquery':    return handleRaiseSupportQuery(actor, body);
    case 'resolvesupportquery':  return handleResolveSupportQuery(actor, body);
    case 'setupsheets':          return handleSetupSheets(actor);
    case 'dedupeleadsnow':       return handleDedupeNow(actor);
    case 'pollnow':              return actor.role === 'super_admin' ? (pollActiveBatches().catch(() => {}), { ok: true, message: 'Poll triggered.' }) : { ok: false, error: 'FORBIDDEN' };
    case 'backfillnow':          return actor.role === 'super_admin' ? (backfillMissingOutputs().catch(() => {}), { ok: true, message: 'Backfill triggered.' }) : { ok: false, error: 'FORBIDDEN' };
    case 'killjobs':             return { ok: true, message: 'Use Render dashboard to stop the server.' };
    case 'installtriggers':      return { ok: true, message: 'Node handles all background jobs automatically.' };
    case 'fixallsheets':         return handleRepairAgentSheets(actor);
    case 'runcallbacknow':       return { ok: true, message: 'Callbacks run automatically daily at 11am IST.' };
    case 'runretrynow':          return { ok: true, message: 'Retries run automatically daily at 11am IST.' };
    default:                     return { ok: false, error: `UNKNOWN_ACTION: ${action}` };
  }
}

// ═══════════════════════════════════════════════════════════════════════════════
// EXPRESS ROUTES
// ═══════════════════════════════════════════════════════════════════════════════

// Main API endpoint — ALL actions handled here
app.post('/api', async (req, res) => {
  try {
    const result = await handleAction(req.body || {});
    res.json(result);
  } catch (err) {
    console.error('[api] Unhandled error:', err.message);
    res.status(500).json({ ok: false, error: err.message });
  }
});

// Alias: bare / also hits the same handler (for legacy compatibility)
app.post('/', async (req, res) => {
  try {
    const result = await handleAction(req.body || {});
    res.json(result);
  } catch (err) {
    res.status(500).json({ ok: false, error: err.message });
  }
});

// ─── Poller auth middleware ───────────────────────────────────────────────────
function requirePollerToken(req, res, next) {
  const auth = (req.headers['authorization'] || '').replace('Bearer ', '').trim();
  if (auth !== POLLER_TOKEN) return res.status(401).json({ ok: false, error: 'UNAUTHORIZED' });
  next();
}

app.get('/poller/status', requirePollerToken, (req, res) => res.json({ ok: true, ...getStatus() }));

app.post('/poller/force-refresh', requirePollerToken, async (req, res) => {
  const { agentCode } = req.body || {};
  try {
    await pollActiveBatches(agentCode || null);
    res.json({ ok: true, message: agentCode ? `Refreshed ${agentCode}` : 'Refreshed all agents' });
  } catch (err) { res.status(500).json({ ok: false, error: err.message }); }
});

const JOB_MAP = {
  poll:      () => pollActiveBatches(),
  backfill:  () => backfillMissingOutputs(),
  repair:    () => repairUnassignedLeads(),
  sessions:  () => cleanupExpiredSessions(),
  dedupe:    () => dedupeAllSheets(),
  archLeads: () => archiveCompletedLeads(),
  archMT:    () => archiveCompletedMT(),
  archManual:() => archiveManualTracker(),
  callbacks: () => processCallbackQueue(),
  retries:   () => processRetryQueue(),
};
app.post('/poller/run/:job', requirePollerToken, async (req, res) => {
  const fn = JOB_MAP[req.params.job];
  if (!fn) return res.status(400).json({ ok: false, error: `Unknown job: ${req.params.job}`, available: Object.keys(JOB_MAP) });
  try { const result = await fn(); res.json({ ok: true, job: req.params.job, result: result || 'done' }); }
  catch (err) { res.status(500).json({ ok: false, error: err.message }); }
});

// ─── Archive endpoints ────────────────────────────────────────────────────────
async function archiveAuth(req, res) {
  const token = req.body?.session || req.headers['x-session'];
  const sess  = await validateSession(token);
  if (!sess) { res.status(401).json({ ok: false, error: 'UNAUTHENTICATED' }); return null; }
  return await findUser(sess.email);
}

app.post('/api/archive/leads', async (req, res) => {
  const user = await archiveAuth(req, res); if (!user) return;
  const team = user.role === 'super_admin' ? req.body?.team : user.team;
  try {
    const rows = await getArchivedLeads(team);
    let all = rows;
    if (user.role === 'recruiter') all = all.filter(r => String(r['Assigned To Email'] || '').toLowerCase() === user.email);
    res.json({ ok: true, leads: all, count: all.length, source: 'archive' });
  } catch (err) { res.status(500).json({ ok: false, error: err.message }); }
});

app.post('/api/archive/mt', async (req, res) => {
  const user = await archiveAuth(req, res); if (!user) return;
  const team = user.role === 'super_admin' ? req.body?.team : user.team;
  if (!team) return res.json({ ok: true, rows: [], count: 0 });
  try { const rows = await getArchivedMT(team); res.json({ ok: true, rows, count: rows.length, source: 'archive' }); }
  catch (err) { res.status(500).json({ ok: false, error: err.message }); }
});

app.post('/api/archive/manual', async (req, res) => {
  const user = await archiveAuth(req, res); if (!user) return;
  const team = user.role === 'super_admin' ? req.body?.team : user.team;
  if (!team) return res.json({ ok: true, rows: [], count: 0 });
  try {
    let rows = await getArchivedManual(team);
    if (user.role === 'recruiter') rows = rows.filter(r => String(r['Added By Email'] || '').toLowerCase() === user.email);
    res.json({ ok: true, rows, count: rows.length, source: 'archive' });
  } catch (err) { res.status(500).json({ ok: false, error: err.message }); }
});

// ─── Health ───────────────────────────────────────────────────────────────────
app.get('/health', (req, res) => res.json({ ok: true, uptime: Math.round(process.uptime()), ts: new Date().toISOString() }));

// ─── Frontend SPA catch-all ───────────────────────────────────────────────────
app.get('*', (req, res) => {
  const idx = path.join(__dirname, 'public', 'index.html');
  res.sendFile(idx, err => { if (err) res.status(404).send('Not found'); });
});

// ─── Start ────────────────────────────────────────────────────────────────────
app.listen(PORT, () => {
  console.log(`[server] Voxa Portal running on port ${PORT} — all logic in Node, no GAS proxy`);
  startPoller();

  // Keepalive: self-ping every 5 min so Render free tier never spins down
  // After 6pm when Hunar stops calls, light traffic would trigger sleep without this
  const cron = require('node-cron');
  cron.schedule('*/5 * * * *', async () => {
    try {
      await axios.get(`http://localhost:${PORT}/health`, { timeout: 5000 });
    } catch (_) {}
  });
  console.log('[server] Keepalive ping scheduled (every 5 min) ✓');
});