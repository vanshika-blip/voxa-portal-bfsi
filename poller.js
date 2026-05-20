/**
 * poller.js — All background jobs for Voxa Portal
 * 
 * Jobs:
 *   - pollActiveBatches      every 2 min  (concurrent fetches, 0-completed campaigns first)
 *   - autoQualifyLeads       every 10 min (DB-driven rules, no restart needed)
 *   - backfillMissingOutputs every 15 min (staggered)
 *   - repairUnassignedLeads  every 20 min
 *   - cleanupExpiredSessions every hour
 *   - dedupeAllSheets        daily 1am IST
 *   - archiveCompletedLeads  daily 2am IST → team spreadsheet
 *   - archiveCompletedMT     daily 3am IST → team spreadsheet
 *   - archiveManualTracker   daily 4am IST → team spreadsheet
 *   - processCallbackQueue   daily 11am IST
 *   - processRetryQueue      daily 11am IST
 *
 * MEMORY FIXES (v2.1):
 *   1. Trigger Log cached for 10 min — was re-read every 2 min poll cycle
 *   2. _refreshCampaignTracker merge uses Map lookup O(n) — was O(n²) .find() inside .map()
 *   3. Large merged array explicitly cleared after use to aid GC
 *   4. Fixed dedupe bug: was referencing undefined `dedupeSsId` variable
 *
 * POLLING FIXES (v2.2):
 *   5. Time gate: only poll between 8:00am–9:00pm IST (Hunar operates 8am–8pm, buffer till 9pm)
 *   6. New priority order: COMPLETED(no eval) → IN_PROGRESS → INITIATED → SCHEDULED → NOT_STARTED
 *      Terminal statuses (NOT_CONNECTED, FAILED, CANCELLED) are skipped entirely — Hunar never updates them again
 */

const cron = require('node-cron');
const axios = require('axios');
const {
  readSheet, readSheetAsObjects, writeRow, writeRows, appendRows,
  deleteRows, ensureSheet, testConnection, batchWriteRows, sleep, withRetry,
} = require('./sheets');

// ─── Config ──────────────────────────────────────────────────────────────────

const MAIN_SS_ID   = process.env.SPREADSHEET_ID;
const HUNAR_BASE   = 'https://api.voice.hunar.ai';
const HUNAR_KEY    = process.env.HUNAR_API_KEY;
const IST_OFFSET   = 5.5 * 60 * 60 * 1000; // ms

// Sheet name constants
const PORTAL = {
  USERS:        'Users',
  TEAMS:        'Teams',
  AGENTS:       'Agents',
  TRIGGER_LOG:  'Trigger Log',
  SESSIONS:     'Sessions',
  AUDIT:        'Audit Log',
};
const AGT = {
  CALL_INPUT:       'Call_Input',
  CAMPAIGN_TRACKER: 'Campaign_Tracker',
  MASTER_TRACKER:   'Master_Tracker',
  QUALIFIED_LEADS:  'Qualified_Leads',
  NOT_CONNECTED:    'Not_Connected',
  CALLBACKS:        'Callbacks',
};
const QUEUE = {
  CALLBACK:         '_Callback_Queue',
  RETRY:            '_Retry_Queue',
  MANUAL_TRACKER:   '_Manual_Tracker',
  INTERVIEW_LINEUP: '_Interview_Lineup',
};
const ARCHIVE = {
  LEADS:   '_Completed_Leads',
  MT:      '_Completed_MT',
  MANUAL:  '_Completed_Manual',
};

const FINAL_STATUSES = new Set(['COMPLETED', 'NOT_CONNECTED', 'CANCELLED', 'FAILED']);
const CB_KEYWORDS = ['call back', 'callback', 'call-back', 'ring back', 'follow up', 'followup', 'follow-up', 'reschedule'];

// ─── Runtime state ────────────────────────────────────────────────────────────

let pollRunning   = false;
let _pollCycleCount = 0; // increments each poll run, used for SCHEDULED throttling
let lastPollTime  = null;
let lastPollStats = {};
let jobStats      = {};

// ─── Adaptive poll budget ─────────────────────────────────────────────────────
//
// Each poll cycle the system scans every agent's Master Tracker (Sheets reads
// only — zero Hunar API calls) and categorises every row into one of two work
// buckets:
//
//   pollNeeded      — live calls that need a status check:
//                     INITIATED / IN_PROGRESS / SCHEDULED / NOT_STARTED
//
//   backfillNeeded  — calls that finished (COMPLETED) but are still missing
//                     result/evaluation data in the out.* columns
//
// The two budgets are then allocated proportionally across all agents.
// An agent with ZERO in both buckets is skipped entirely — no API call, no
// sleep delay.  The moment someone triggers a campaign the agent reappears
// in the next cycle's scan with a real pendingCount and gets a proper cap.
//
// ── Tuning knobs (only these need changing) ───────────────────────────────────

const POLL_BUDGET = {
  // ── Live-poll budget (INITIATED / IN_PROGRESS / SCHEDULED / NOT_STARTED) ──
  // Reduced from 400/300 → quota was being fully exhausted every cycle,
  // blocking user-facing login/API requests which share the same Sheets quota.
  POLL_GLOBAL:      80,   // total Hunar API slots for live polling across all agents/cycle
  POLL_MAX_CAP:     60,   // hard ceiling per single agent for live polling

  // ── Backfill budget (COMPLETED rows missing result data) ──────────────────
  // Reduced from 200/150 → backfill runs on its own 15-min cron, doesn't need large caps
  BACKFILL_GLOBAL:  30,   // total Hunar API slots for backfill across all agents/cycle
  BACKFILL_MAX_CAP: 25,   // hard ceiling per single agent for backfill

  // ── Shared ────────────────────────────────────────────────────────────────
  // No MIN_CAP — zero means zero.  Agents only get a slot if they have work.
};

// ── Internal helpers ──────────────────────────────────────────────────────────

/**
 * Pure proportional allocation — no MIN_CAP, no rounding up.
 * Returns Map<agentCode, cap> where sum(caps) <= globalBudget.
 * Agents with count === 0 are omitted from the map entirely.
 *
 * @param {{ agentCode: string, count: number }[]} list
 * @param {number} globalBudget
 * @param {number} maxCap
 */
function _allocateBudget(list, globalBudget, maxCap) {
  const active = list.filter(a => a.count > 0);
  if (!active.length) return new Map();

  const total = active.reduce((s, a) => s + a.count, 0);
  const caps  = new Map();
  let allocated = 0;

  active.forEach(a => {
    const raw = Math.ceil((a.count / total) * globalBudget);
    const cap = Math.min(maxCap, raw);
    if (cap > 0) { caps.set(a.agentCode, cap); allocated += cap; }
  });

  // Rare: rounding pushed us over budget — trim fattest first
  if (allocated > globalBudget) {
    let overflow = allocated - globalBudget;
    const sorted = [...caps.entries()].sort((a, b) => b[1] - a[1]);
    for (const [code, cur] of sorted) {
      if (overflow <= 0) break;
      const cut = Math.min(cur, overflow);
      const newCap = cur - cut;
      if (newCap > 0) caps.set(code, newCap); else caps.delete(code);
      overflow -= cut;
    }
  }

  return caps;
}

/**
 * Scan an agent's Master Tracker (Sheets-only, no Hunar calls) and return
 * how many rows fall into each work bucket.
 *
 * @returns {{ pollNeeded: number, backfillNeeded: number }}
 */
async function _scanAgentWork(agent) {
  const result = { pollNeeded: 0, backfillNeeded: 0 };
  try {
    const ssId   = agent.spreadsheetId || MAIN_SS_ID;
    const mtName = agent.spreadsheetId ? AGT.MASTER_TRACKER : (agent.agentCode + AGT.MASTER_TRACKER);
    const { headers, rows } = await readSheet(ssId, mtName);
    if (!headers.length || !rows.length) return result;

    const statusCol    = headers.indexOf('Status');
    const reqIdColIdx  = headers.indexOf('Request ID');
    if (statusCol < 0) return result;

    const LIVE_STATUSES = new Set(['INITIATED', 'IN_PROGRESS', 'SCHEDULED', 'NOT_STARTED']);
    const resultFields  = resultFieldNames(agent.resultSchema);

    for (const row of rows) {
      const status = String(row[statusCol] || '').toUpperCase();

      // Terminal — Hunar will never update these again
      if (status === 'NOT_CONNECTED' || status === 'FAILED' || status === 'CANCELLED') continue;

      if (LIVE_STATUSES.has(status)) {
        result.pollNeeded++;
        continue;
      }

      if (status === 'COMPLETED') {
        const hasResult = resultFields.length === 0 || resultFields.some(f => {
          const col = headers.indexOf('out.' + f);
          return col >= 0 && String(row[col] || '').trim() !== '';
        });
        if (!hasResult) result.backfillNeeded++;
        // COMPLETED + has results → fully done, skip
      }
    }

    // Also build the completedPerCampaign map for the sort inside _pollAgent
    // (cheaper to compute here once rather than inside _pollAgent again)
    result.completedPerCampaign = new Map();
    for (const row2 of rows) {
      const s2 = String(row2[statusCol] || '').toUpperCase();
      const ri  = reqIdColIdx >= 0 ? String(row2[reqIdColIdx] || '') : '';
      if (s2 === 'COMPLETED' && ri) {
        result.completedPerCampaign.set(ri, (result.completedPerCampaign.get(ri) || 0) + 1);
      }
    }

  } catch { /* sheet unreadable — treat as idle */ }
  return result;
}

/**
 * Compute per-agent { pollCap, backfillCap } purely from live scan counts.
 * No database columns, no overrides — cap is 100% self-calculated every cycle.
 *
 * Each agent's share = proportional to its pending work out of the global budget.
 * Agents with zero work in both buckets are absent from the map → skipped.
 *
 * Returns Map<agentCode, { pollCap, backfillCap }>
 */
function computeAgentCaps(scanResults) {
  const { POLL_GLOBAL, POLL_MAX_CAP, BACKFILL_GLOBAL, BACKFILL_MAX_CAP } = POLL_BUDGET;

  const pollCaps     = _allocateBudget(
    scanResults.map(r => ({ agentCode: r.agentCode, count: r.pollNeeded })),
    POLL_GLOBAL, POLL_MAX_CAP
  );
  const backfillCaps = _allocateBudget(
    scanResults.map(r => ({ agentCode: r.agentCode, count: r.backfillNeeded })),
    BACKFILL_GLOBAL, BACKFILL_MAX_CAP
  );

  const combined = new Map();
  for (const r of scanResults) {
    const pollCap     = pollCaps.get(r.agentCode)     || 0;
    const backfillCap = backfillCaps.get(r.agentCode) || 0;
    if (pollCap > 0 || backfillCap > 0) {
      combined.set(r.agentCode, { pollCap, backfillCap });
    }
  }
  return combined;
}

// ─── Hunar API helpers ────────────────────────────────────────────────────────

function hunarHeaders() {
  return { 'X-API-Key': HUNAR_KEY, 'Content-Type': 'application/json' };
}

async function hunarGet(path) {
  try {
    const res = await axios.get(`${HUNAR_BASE}${path}`, {
      headers: hunarHeaders(), timeout: 15000,
    });
    return { ok: true, data: res.data };
  } catch (e) {
    const msg = e.response?.data ? JSON.stringify(e.response.data).slice(0, 200) : e.message;
    return { ok: false, error: msg };
  }
}

async function hunarPost(path, body) {
  try {
    const res = await axios.post(`${HUNAR_BASE}${path}`, body, {
      headers: hunarHeaders(), timeout: 30000,
    });
    return { ok: true, data: res.data };
  } catch (e) {
    const msg = e.response?.data ? JSON.stringify(e.response.data).slice(0, 200) : e.message;
    return { ok: false, error: msg };
  }
}

async function getCall(callId) {
  return hunarGet(`/external/v1/calls/${encodeURIComponent(callId)}/`);
}

async function bulkCall(body) {
  return hunarPost('/external/v1/calls/bulk/', body);
}

// ─── Sheet data loaders ───────────────────────────────────────────────────────

let _agentsCache  = null;
let _agentsCacheAt = 0;
let _usersCache   = null;
let _usersCacheAt = 0;
let _teamsCache   = null;
let _teamsCacheAt = 0;

// FIX 1: Cache Trigger Log — was re-read every 2 min, can grow very large
let _trigCache    = null;
let _trigCacheAt  = 0;
const TRIG_TTL_MS = 10 * 60 * 1000; // 10 minutes

async function _getTriggerLog(force = false) {
  if (!force && _trigCache && Date.now() - _trigCacheAt < TRIG_TTL_MS) {
    return _trigCache;
  }
  const res = await readSheet(MAIN_SS_ID, PORTAL.TRIGGER_LOG);
  _trigCache = res;
  _trigCacheAt = Date.now();
  return _trigCache;
}

async function getAllAgents(force = false) {
  if (!force && _agentsCache && Date.now() - _agentsCacheAt < 5 * 60 * 1000) return _agentsCache;
  const { headers, rows } = await readSheet(MAIN_SS_ID, PORTAL.AGENTS);
  if (!headers.length) return [];

  const idx = h => headers.indexOf(h);
  _agentsCache = rows.map(r => {
    let customVars = [], resultSchema = {}, qualValues = [], qualRules = [];
    try { customVars = JSON.parse(r[idx('Custom Variables')] || '[]'); } catch (_) {}
    try { resultSchema = JSON.parse(r[idx('Result Schema')] || '{}'); } catch (_) {}
    try {
      const raw = r[idx('Qualification Values')];
      if (typeof raw === 'string' && raw.trim().startsWith('[')) qualValues = JSON.parse(raw);
      else if (raw) qualValues = [String(raw)];
    } catch (_) {}
    try {
      const raw = r[idx('Qualification Rules')];
      if (typeof raw === 'string' && raw.trim().startsWith('[')) qualRules = JSON.parse(raw);
    } catch (_) {}

    return {
      agentCode:          String(r[idx('Agent Code')] || '').trim(),
      agentId:            String(r[idx('Agent ID')] || '').trim(),
      displayName:        String(r[idx('Display Name')] || '').trim(),
      customVariables:    Array.isArray(customVars) ? customVars : [],
      resultSchema:       resultSchema || {},
      qualificationField: String(r[idx('Qualification Field')] || '').trim(),
      qualificationValues: Array.isArray(qualValues) ? qualValues.filter(Boolean) : [],
      qualificationRules:  Array.isArray(qualRules) ? qualRules : [],
      estSecondsPerCall:  Number(r[idx('Est Seconds Per Call')] || 60),
      active:             r[idx('Active')] === true || r[idx('Active')] === 'TRUE',
      createdBy:          String(r[idx('Created By')] || '').trim(),
      clientName:         String(r[idx('Client Name')] || '').trim(),
      spreadsheetId:      String(r[idx('Spreadsheet ID')] || '').trim(),
    };
  }).filter(a => a.agentCode);

  _agentsCacheAt = Date.now();
  return _agentsCache;
}

async function getAllUsers(force = false) {
  if (!force && _usersCache && Date.now() - _usersCacheAt < 5 * 60 * 1000) return _usersCache;
  const { headers, rows } = await readSheet(MAIN_SS_ID, PORTAL.USERS);
  if (!headers.length) return [];
  const idx = h => headers.indexOf(h);
  _usersCache = rows.map(r => ({
    email:  String(r[idx('Email')] || '').toLowerCase().trim(),
    name:   String(r[idx('Name')] || '').trim(),
    role:   String(r[idx('Role')] || '').trim(),
    team:   String(r[idx('Team')] || '').trim(),
    active: r[idx('Active')] === true || r[idx('Active')] === 'TRUE',
  })).filter(u => u.email);
  _usersCacheAt = Date.now();
  return _usersCache;
}

async function getAllTeams(force = false) {
  if (!force && _teamsCache && Date.now() - _teamsCacheAt < 10 * 60 * 1000) return _teamsCache;
  const { headers, rows } = await readSheet(MAIN_SS_ID, PORTAL.TEAMS);
  if (!headers.length) return [];
  const idx = h => headers.indexOf(h);
  _teamsCache = rows.map(r => ({
    id:            String(r[idx('Team ID')] || '').trim(),
    name:          String(r[idx('Team Name')] || '').trim(),
    spreadsheetId: String(r[idx('Spreadsheet ID')] || '').trim(),
  })).filter(t => t.name);
  _teamsCacheAt = Date.now();
  return _teamsCache;
}

function buildUserRoleMap(users) {
  const map = {};
  users.forEach(u => { map[u.email] = { role: u.role, name: u.name, team: u.team }; });
  return map;
}

function buildTriggerMap(triggerRows, triggerHeaders) {
  const map = {};
  const reqIdx = triggerHeaders.indexOf('Request ID');
  const emailIdx = triggerHeaders.indexOf('User Email');
  const agentIdx = triggerHeaders.indexOf('Agent Code');
  triggerRows.forEach(r => {
    const reqId = String(r[reqIdx] || '').trim();
    const email = String(r[emailIdx] || '').toLowerCase().trim();
    const agentCode = String(r[agentIdx] || '').trim();
    if (reqId && email) map[`${agentCode}|${reqId}`] = email;
  });
  return map;
}

function resultFieldNames(schema) {
  if (!schema || typeof schema !== 'object') return [];
  if (schema.properties) return Object.keys(schema.properties);
  return Object.keys(schema).filter(k => k !== 'type' && k !== 'required');
}

function isQualified(agent, result) {
  const rules = agent.qualificationRules;
  if (rules && Array.isArray(rules) && rules.length > 0) {
    return rules.every(rule => {
      if (!rule.field) return true;
      const val = result[rule.field];
      if (!val) return false;
      const keywords = Array.isArray(rule.keywords) ? rule.keywords.filter(Boolean) : [];
      if (!keywords.length) return !!val;
      const lower = String(val).toLowerCase();
      return keywords.some(kw => lower.includes(String(kw).toLowerCase()));
    });
  }
  if (!agent.qualificationField) return false;
  const val = result[agent.qualificationField];
  if (!val) return false;
  const vals = agent.qualificationValues || [];
  if (!vals.length) return !!val;
  const lower = String(val).toLowerCase().trim();
  return vals.some(v => lower.includes(String(v).toLowerCase().trim()));
}

function detectCallbackField(agent, result) {
  const matchesCB = val => {
    if (!val) return false;
    const lower = String(val).toLowerCase();
    return CB_KEYWORDS.some(kw => lower.includes(kw));
  };
  const rules = agent.qualificationRules;
  if (rules?.length) {
    for (const rule of rules) {
      if (rule.field && matchesCB(result[rule.field])) return rule.field;
    }
  }
  if (agent.qualificationField && matchesCB(result[agent.qualificationField])) return agent.qualificationField;
  for (const key of Object.keys(result || {})) {
    if (matchesCB(result[key])) return key;
  }
  return null;
}

function resolveLeadAssignment(reqId, agentCode, mobileNumber, mtRow, mtHeaders, userRoleMap, triggerMap) {
  const triggeredBy = triggerMap[`${agentCode}|${reqId}`];
  if (triggeredBy) {
    const u = userRoleMap[triggeredBy];
    if (u) return { assignEmail: triggeredBy, recruiterName: u.name };
  }
  const trigByCol = mtHeaders.indexOf('Triggered By');
  const email = trigByCol >= 0 ? String(mtRow[trigByCol] || '').toLowerCase().trim() : '';
  if (email) {
    const u = userRoleMap[email];
    if (u) return { assignEmail: email, recruiterName: u.name };
  }
  return { assignEmail: '', recruiterName: '' };
}

function istNow() {
  return new Date(Date.now() + IST_OFFSET);
}

function istDateStr(date = new Date()) {
  const ist = new Date(date.getTime() + IST_OFFSET);
  return ist.toISOString().slice(0, 10);
}

/**
 * Returns true only between 08:00 and 23:30 IST.
 * Hunar operates 8am–8pm; we buffer to 11:30pm to catch all late completions.
 */
function isPollingHours() {
  const ist = istNow();
  const hours   = ist.getUTCHours();
  const minutes = ist.getUTCMinutes();
  const timeMin = hours * 60 + minutes;
  return timeMin >= 8 * 60 && timeMin < 23 * 60 + 30; // 08:00 → 23:30 IST
}

// ─────────────────────────────────────────────────────────────────────────────
// JOB 1: POLL ACTIVE BATCHES
// Fetches call statuses from Hunar API, updates Master Tracker,
// pushes qualified leads to Qualified Leads sheet
// ─────────────────────────────────────────────────────────────────────────────

async function pollActiveBatches(agentCodeFilter = null) {
  if (pollRunning) {
    console.log('[poll] Skipping — still running.');
    return;
  }
  // Time gate: only poll 8am–9pm IST
  if (!agentCodeFilter && !isPollingHours()) {
    console.log('[poll] Outside polling hours (8am–9pm IST) — skipping.');
    return;
  }
  pollRunning = true;
  _pollCycleCount++;
  const start = Date.now();

  try {
    const agents = (await getAllAgents()).filter(a => a.active);
    const users = await getAllUsers();
    const userRoleMap = buildUserRoleMap(users);

    // FIX 1: Use cached Trigger Log instead of re-reading every 2 minutes
    const { headers: trigHeaders, rows: trigRows } = await _getTriggerLog();
    const triggerMap = trigHeaders.length ? buildTriggerMap(trigRows, trigHeaders) : {};

    const targets = agentCodeFilter ? agents.filter(a => a.agentCode === agentCodeFilter) : agents;

    // ── Adaptive cap calculation ─────────────────────────────────────────────
    // Scan every agent's Master Tracker in parallel (Sheets reads only, zero
    // Hunar API cost) to count:
    //   pollNeeded     — live calls (INITIATED / IN_PROGRESS / SCHEDULED / NOT_STARTED)
    //   backfillNeeded — COMPLETED calls still missing result data
    //
    // Budget is then allocated proportionally across agents.
    // Agents with 0 in both buckets are skipped entirely this cycle.
    // The moment a campaign is triggered the agent appears in the next scan.
    let agentCaps;
    let scanSummary = [];

    if (agentCodeFilter) {
      // Forced single-agent poll: use the full budget caps for both buckets
      agentCaps = new Map([[agentCodeFilter, {
        pollCap:     POLL_BUDGET.POLL_MAX_CAP,
        backfillCap: POLL_BUDGET.BACKFILL_MAX_CAP,
      }]]);
    } else {
      // ── Sequential scan with small gaps ─────────────────────────────────
      // Previously used Promise.all which fired 9 Sheets reads simultaneously,
      // creating a quota burst at the start of every cycle and blocking login
      // requests that share the same Sheets API quota pool.
      // Sequential with 300ms gaps spreads the reads over ~3s instead of 0s.
      console.log(`[poll] Scanning work queues across ${targets.length} agents…`);
      const scanResults = [];
      for (const a of targets) {
        const r = await _scanAgentWork(a);
        scanResults.push({
          agentCode:      a.agentCode,
          pollNeeded:     r.pollNeeded,
          backfillNeeded: r.backfillNeeded,
        });
        await sleep(300); // spread Sheets reads — prevents quota burst
      }
      agentCaps = computeAgentCaps(scanResults);

      // Log: show each agent's scan count → calculated cap
      scanSummary = scanResults.map(r => {
        const caps = agentCaps.get(r.agentCode);
        if (!caps) return `${r.agentCode}: IDLE`;
        return `${r.agentCode}: poll=${r.pollNeeded}→${caps.pollCap}  backfill=${r.backfillNeeded}→${caps.backfillCap}`;
      });
      console.log('[poll] Budget allocation (auto-calc from live scan):');
      scanSummary.forEach(s => console.log('  ' + s));
    }
    // ── End adaptive cap ─────────────────────────────────────────────────────

    for (const agent of targets) {
      const caps = agentCaps.get(agent.agentCode);
      if (!caps) {
        // Truly idle — no pending poll or backfill work
        continue;
      }
      try {
        const stats = await _pollAgent(agent, userRoleMap, triggerMap, caps.pollCap, caps.backfillCap);
        lastPollStats[agent.agentCode] = { ...stats, pollCap: caps.pollCap, backfillCap: caps.backfillCap };
        console.log(`[poll] ${agent.agentCode}: pollCap=${caps.pollCap} backfillCap=${caps.backfillCap} fetched=${stats.fetched} updated=${stats.updated} errors=${stats.errors}`);
        // Increased from 1200ms → 2500ms: more breathing room between agents
        // so Sheets quota recovers before the next agent starts its reads.
        await sleep(2500);
      } catch (err) {
        console.error(`[poll] Error on ${agent.agentCode}:`, err.message);
      }
    }
    lastPollTime = new Date();

    // QL sync is handled entirely by the autoQualifyLeads cron (every 10 min).
    // pollActiveBatches only writes Master Tracker rows — nothing else.

  } finally {
    pollRunning = false;
    const elapsed = ((Date.now() - start) / 1000).toFixed(1);
    console.log(`[poll] Complete in ${elapsed}s`);
  }
}

async function _pollAgent(agent, userRoleMap, triggerMap, pollCap = POLL_BUDGET.POLL_MAX_CAP, backfillCap = POLL_BUDGET.BACKFILL_MAX_CAP) {
  // poll does ONE thing: fetch Hunar status → write Master Tracker row.
  // Qualified Leads sync is fully handled by autoQualifyLeads cron (every 10 min).
  const stats = { fetched: 0, updated: 0, errors: 0 };
  const agentSsId = agent.spreadsheetId || MAIN_SS_ID;
  const mtName = agent.spreadsheetId ? AGT.MASTER_TRACKER : (agent.agentCode + AGT.MASTER_TRACKER);
  const ncName = agent.spreadsheetId ? AGT.NOT_CONNECTED   : (agent.agentCode + AGT.NOT_CONNECTED);

  const { headers: mtHeaders, rows: mtRows } = await readSheet(agentSsId, mtName);
  if (!mtHeaders.length || !mtRows.length) return stats;

  const callIdCol = mtHeaders.indexOf('Call ID');
  const statusCol  = mtHeaders.indexOf('Status');
  const reqIdCol   = mtHeaders.indexOf('Request ID');
  if (callIdCol < 0 || statusCol < 0) return stats;

  const resultFields = resultFieldNames(agent.resultSchema);
  const customVars   = agent.customVariables || [];

  // Load NC existing IDs
  const { rows: ncRows } = await readSheet(agentSsId, ncName);
  const ncExistingIds = new Set(ncRows.map(r => String(r[0] || '').trim()).filter(Boolean));

  // Load campaign statuses + triggered timestamps
  const ctSheetName = agent.spreadsheetId ? AGT.CAMPAIGN_TRACKER : (agent.agentCode + AGT.CAMPAIGN_TRACKER);
  const { headers: ctHeaders, rows: ctRows } = await readSheet(agentSsId, ctSheetName);
  const ctReqCol        = ctHeaders.indexOf('Request ID');
  const ctStatusCol     = ctHeaders.indexOf('Status');
  const ctTriggeredAtCol = ctHeaders.indexOf('Triggered At');
  const campaignStatus      = new Map(); // reqId → status string
  const campaignTriggeredAt = new Map(); // reqId → timestamp ms
  if (ctReqCol >= 0) {
    ctRows.forEach(r => {
      const rid = String(r[ctReqCol] || '').trim();
      if (!rid) return;
      if (ctStatusCol >= 0) {
        const s = String(r[ctStatusCol] || 'IN_PROGRESS').toUpperCase();
        campaignStatus.set(rid, s);
      }
      if (ctTriggeredAtCol >= 0 && r[ctTriggeredAtCol]) {
        const ms = new Date(r[ctTriggeredAtCol]).getTime();
        if (!isNaN(ms)) campaignTriggeredAt.set(rid, ms);
      }
    });
  }

  const todayStr = istDateStr(); // 'YYYY-MM-DD' in IST, used for today-first sorting

  // Rows to write back
  const rowUpdates = []; // { rowIndex, values }
  // qlAppends removed — QL sync is separate
  const ncAppends  = []; // arrays to append
  const ncDeletes  = []; // row indices to delete from NC

  // ── Priority-sorted processing ───────────────────────────────────────────
  // Sort order (outermost → innermost):
  //   1. TODAY's campaigns before previous days — ensures fresh triggers are never starved
  //   2. Newest triggered campaign first — "last triggered → polled first → then previous"
  //   3. Status urgency within the same campaign:
  //        COMPLETED (missing results) → IN_PROGRESS → INITIATED → SCHEDULED → NOT_STARTED
  //   4. Row index DESC (newest row in same campaign processed first)
  //
  // SCHEDULED/NOT_STARTED throttle: previous-day rows only (every 10th cycle).
  //   Today's SCHEDULED/NOT_STARTED are always included so fresh campaigns aren't delayed.
  // Cap at pollCap / backfillCap (adaptive — computed per cycle via _scanAgentWork).

  const rowPriority = (status, hasResult) => {
    if (status === 'COMPLETED' && !hasResult) return 0; // urgent — get eval data
    if (status === 'IN_PROGRESS')             return 1; // call ongoing
    if (status === 'NOT_STARTED')             return 2; // fires immediately on trigger
    if (status === 'INITIATED')               return 3;
    if (status === 'SCHEDULED')               return 4;
    return 99; // terminal status — skip
  };

  // Build candidate list
  const candidates = [];
  for (let i = 0; i < mtRows.length; i++) {
    const row    = mtRows[i];
    const callId = String(row[callIdCol] || '').trim();
    if (!callId) continue;

    const status = String(row[statusCol] || '').toUpperCase();
    const reqId  = reqIdCol >= 0 ? String(row[reqIdCol] || '') : '';
    const campaignDone = reqId ? campaignStatus.get(reqId) === 'COMPLETED' : false;

    // Skip ALL terminal statuses — NOT_CONNECTED, FAILED, CANCELLED never get updated by Hunar again
    // We discover these by polling SCHEDULED/INITIATED/IN_PROGRESS rows instead
    if (status === 'NOT_CONNECTED' || status === 'FAILED' || status === 'CANCELLED') continue;

    const hasResult = status === 'COMPLETED' && resultFields.some(f => {
      const col = mtHeaders.indexOf('out.' + f);
      return col >= 0 && String(row[col] || '').trim() !== '';
    });

    // Skip COMPLETED rows that already have full result data
    if (status === 'COMPLETED' && hasResult) continue;

    const priority = rowPriority(status, hasResult);

    // Resolve which day/campaign this row belongs to
    const triggeredAtMs = reqId ? (campaignTriggeredAt.get(reqId) || 0) : 0;
    const campaignDate  = triggeredAtMs ? istDateStr(new Date(triggeredAtMs)) : '';
    const isToday       = campaignDate === todayStr;

    // SCHEDULED: throttle previous-day campaigns to every 20th cycle (~40 min)
    // Today's SCHEDULED are always included so fresh triggers aren't delayed.
    // NOT_STARTED is always included regardless of day (fires immediately on trigger).
    if (priority === 4 && !isToday) {
      if ((_pollCycleCount % 20) !== (i % 20)) continue;
    }

    candidates.push({ i, row, callId, status, reqId, priority, campaignDone, isToday, triggeredAtMs });
  }

  // ── Count COMPLETED calls per campaign — drives the "0-completed first" sort ─
  // Campaigns where the AI hasn't finished a single call yet are most urgent:
  // their data is completely unknown. We serve those first, then campaigns with
  // some completions, then campaigns that are nearly done.
  // Within the same completion tier we fall back to the existing priority order.
  const completedPerCampaign = new Map(); // reqId → number of COMPLETED rows in MT
  for (const row of mtRows) {
    const status = String(row[statusCol] || '').toUpperCase();
    const rid    = reqIdCol >= 0 ? String(row[reqIdCol] || '') : '';
    if (status === 'COMPLETED' && rid) {
      completedPerCampaign.set(rid, (completedPerCampaign.get(rid) || 0) + 1);
    }
  }

  // Sort:
  //   1. Campaigns with FEWEST completed calls first (0-completed → top priority)
  //   2. Today's campaigns before previous days
  //   3. Newest triggered campaign first (within same completion tier)
  //   4. Status urgency (IN_PROGRESS > INITIATED > SCHEDULED)
  //   5. Newest row in same campaign (row index DESC)
  candidates.sort((a, b) => {
    const aDone = completedPerCampaign.get(a.reqId) || 0;
    const bDone = completedPerCampaign.get(b.reqId) || 0;
    if (aDone !== bDone)                 return aDone - bDone;                         // 0-completed first
    if (a.isToday !== b.isToday)         return a.isToday ? -1 : 1;                   // today before prev days
    if (a.triggeredAtMs !== b.triggeredAtMs) return b.triggeredAtMs - a.triggeredAtMs; // newest campaign first
    if (a.priority !== b.priority)       return a.priority - b.priority;              // status urgency
    return b.i - a.i;                                                                  // newest row
  });

  // ── Two-pass split ────────────────────────────────────────────────────────
  // Pass 1 — BACKFILL (capped at backfillCap): COMPLETED rows missing eval data.
  //   Previously uncapped; now uses its own budget bucket from the scan.
  //   backfillCap is computed proportionally from BACKFILL_GLOBAL across agents.
  //
  // Pass 2 — POLL (capped at pollCap): live calls (IN_PROGRESS / INITIATED /
  //   SCHEDULED / NOT_STARTED).
  //   pollCap is computed proportionally from POLL_GLOBAL across agents.
  //
  // Both caps were derived from _scanAgentWork() before any Hunar calls were
  // made, so allocation reflects actual pending work — not assumptions.

  const backfillCandidates = candidates.filter(c => c.priority === 0); // COMPLETED, no eval
  const pollCandidates     = candidates.filter(c => c.priority !== 0); // live calls

  const backfillPass = backfillCandidates.slice(0, backfillCap);
  const pollPass     = pollCandidates.slice(0, pollCap);

  if (backfillCandidates.length > 0) {
    console.log(`[poll] ${agent.agentCode}: backfill=${backfillCandidates.length} cap=${backfillCap} → processing ${backfillPass.length}`);
  }
  if (pollCandidates.length > 0) {
    const todayCount = pollCandidates.filter(c => c.isToday).length;
    console.log(`[poll] ${agent.agentCode}: poll=${pollCandidates.length} (${todayCount} today) cap=${pollCap} → processing ${pollPass.length}`);
  }

  const toProcess = [...backfillPass, ...pollPass];

  // ── Concurrent fetch — process CONCURRENCY calls at a time ───────────────
  // Serial: 100 calls × 150ms = 15s per agent.
  // Concurrent (5): 100 calls / 5 × 150ms = 3s per agent. ~5x faster.
  // Hunar rate limit is 10 req/s; CONCURRENCY=5 at 150ms gap = ~5 req/s — safe.
  const CONCURRENCY = 5;

  async function processOne({ i, row, callId, status, reqId, campaignDone }) {
    stats.fetched++;
    const r = await getCall(callId);
    if (!r.ok) { stats.errors++; return null; }

    const d = r.data;
    const newStatus = String(d.status || status).toUpperCase();
    const result    = d.result || {};

    const newRow = [...row];
    const setH = (name, val) => { const k = mtHeaders.indexOf(name); if (k >= 0) newRow[k] = val; };

    setH('Status',             newStatus);
    setH('Duration (Minutes)', d.duration_minutes ?? (row[mtHeaders.indexOf('Duration (Minutes)')] || 0));
    setH('Duration (Seconds)', d.duration_seconds ?? (row[mtHeaders.indexOf('Duration (Seconds)')] || 0));
    setH('Started At',         d.started_at || row[mtHeaders.indexOf('Started At')] || '');
    setH('Ended At',           d.ended_at   || row[mtHeaders.indexOf('Ended At')]   || '');
    setH('Answered By',        d.answered_by        || '');
    setH('Engagement Status',  d.engagement_status  || '');
    setH('Call Ended By',      d.call_ended_by      || '');
    setH('Recording URL',      d.recording_url      || '');
    setH('Updated At',         new Date().toISOString());

    customVars.forEach(cv => { if (d.custom_data?.[cv] !== undefined) setH('in.' + cv, d.custom_data[cv]); });
    resultFields.forEach(f => { setH('out.' + f, result[f] !== undefined ? result[f] : ''); });

    // NC handling (serial-safe: ncExistingIds is a Set, mutations are fine)
    if (newStatus === 'COMPLETED' && ncExistingIds.has(callId)) {
      const ncRowIdx = ncRows.findIndex(r => String(r[0] || '').trim() === callId);
      if (ncRowIdx >= 0) ncDeletes.push(ncRowIdx + 2);
    } else if ((newStatus === 'NOT_CONNECTED' || newStatus === 'FAILED') && campaignDone) {
      if (!ncExistingIds.has(callId) && status !== 'COMPLETED') {
        const calleeNameCol = mtHeaders.indexOf('Callee Name');
        const mobileCol     = mtHeaders.indexOf('Mobile Number');
        const trigByCol     = mtHeaders.indexOf('Triggered By');
        const retryDate     = new Date(Date.now() + 7 * 24 * 3600 * 1000).toISOString().slice(0, 10);
        ncAppends.push([
          callId,
          calleeNameCol >= 0 ? String(row[calleeNameCol] || '') : '',
          mobileCol     >= 0 ? String(row[mobileCol]     || '') : '',
          newStatus, reqId, 0, 0, '',
          trigByCol >= 0 ? String(row[trigByCol] || '') : '',
          new Date().toISOString(), retryDate, 'PENDING', '',
        ]);
        ncExistingIds.add(callId);
      }
    }

    return { rowIndex: i + 2, values: newRow };
  }

  // Process in chunks of CONCURRENCY — each chunk fires in parallel,
  // then we wait for all to settle before the next chunk.
  for (let ci = 0; ci < toProcess.length; ci += CONCURRENCY) {
    const chunk = toProcess.slice(ci, ci + CONCURRENCY);
    const results = await Promise.allSettled(chunk.map(item => processOne(item)));
    for (const res of results) {
      if (res.status === 'fulfilled' && res.value) {
        rowUpdates.push(res.value);
        stats.updated++;
      }
    }
    // Inter-chunk gap: keeps total rate at CONCURRENCY / gap req/s
    if (ci + CONCURRENCY < toProcess.length) await sleep(150);
  }

  // Flush all writes — ONE batchUpdate call instead of N individual writes
  // This is the key quota fix: N rows = 1 API call, not N API calls
  if (rowUpdates.length) {
    const BATCH = 100; // Google Sheets batchUpdate supports up to 100 ranges per call
    for (let i = 0; i < rowUpdates.length; i += BATCH) {
      const chunk = rowUpdates.slice(i, i + BATCH);
      await batchWriteRows(agentSsId, mtName, chunk);
      if (i + BATCH < rowUpdates.length) await sleep(500);
    }
  }

  if (ncAppends.length) await appendRows(agentSsId, ncName, ncAppends);
  if (ncDeletes.length) await deleteRows(agentSsId, ncName, ncDeletes);

  // ── Immediate eval re-fetch pass ─────────────────────────────────────────
  // Hunar sometimes writes eval/result data a few seconds AFTER status=COMPLETED.
  // When we detect a row that just flipped to COMPLETED but came back with empty result,
  // we wait 5s and re-fetch it inline — instead of waiting the full 2-min cycle.
  // Cap at 20 calls so this never becomes a runaway quota drain.
  const evalPending = rowUpdates.filter(({ values }) => {
    const st = values[statusCol];
    if (st !== 'COMPLETED') return false;
    return resultFields.every(f => {
      const col = mtHeaders.indexOf('out.' + f);
      return col < 0 || String(values[col] || '').trim() === '';
    });
  });

  if (evalPending.length > 0) {
    console.log(`[poll] ${agent.agentCode}: ${evalPending.length} calls COMPLETED but eval empty — re-fetching in 5s`);
    await sleep(5000); // give Hunar's eval pipeline a moment to settle

    const evalUpdates   = [];

    for (const { rowIndex, values } of evalPending.slice(0, 20)) {
      const callId = String(values[callIdCol] || '').trim();
      if (!callId) continue;

      await sleep(200);
      const r2 = await getCall(callId);
      if (!r2.ok) continue;

      const d2      = r2.data;
      const result2 = d2.result || {};
      const hasEval = resultFields.some(f => result2[f] !== undefined && result2[f] !== '');
      if (!hasEval) continue; // still not ready — priority-0 will catch it next cycle

      const newRow = [...values];
      const setH2  = (name, val) => { const k = mtHeaders.indexOf(name); if (k >= 0) newRow[k] = val; };
      setH2('Duration (Minutes)', d2.duration_minutes ?? values[mtHeaders.indexOf('Duration (Minutes)')] ?? 0);
      setH2('Duration (Seconds)', d2.duration_seconds ?? values[mtHeaders.indexOf('Duration (Seconds)')] ?? 0);
      setH2('Ended At',           d2.ended_at   || values[mtHeaders.indexOf('Ended At')]   || '');
      setH2('Answered By',        d2.answered_by || values[mtHeaders.indexOf('Answered By')] || '');
      setH2('Recording URL',      d2.recording_url || values[mtHeaders.indexOf('Recording URL')] || '');
      setH2('Updated At',         new Date().toISOString());
      resultFields.forEach(f => setH2('out.' + f, result2[f] !== undefined ? result2[f] : ''));
      customVars.forEach(cv => { if (d2.custom_data?.[cv] !== undefined) setH2('in.' + cv, d2.custom_data[cv]); });

      evalUpdates.push({ rowIndex, values: newRow });
      stats.updated++;

      // QL is synced by autoQualifyLeads cron — nothing to do here.
    }

    if (evalUpdates.length) {
      // Also update rowUpdates so _refreshCampaignTracker below sees the final values
      evalUpdates.forEach(eu => {
        const existing = rowUpdates.find(u => u.rowIndex === eu.rowIndex);
        if (existing) existing.values = eu.values;
        else rowUpdates.push(eu);
      });
      await batchWriteRows(agentSsId, mtName, evalUpdates);
      console.log(`[poll] ${agent.agentCode}: eval re-fetch filled ${evalUpdates.length}/${evalPending.length}`);
    }

  }

  // FIX 2: Build merged rows using a Map (O(n)) instead of .find() inside .map() (O(n²))
  // This avoids creating a huge in-memory copy of all mtRows on every poll cycle
  if (stats.updated > 0) {
    const updatedRowMap = new Map(rowUpdates.map(u => [u.rowIndex, u.values]));
    const mergedRows = mtRows.map((r, i) => updatedRowMap.get(i + 2) || r);
    await _refreshCampaignTracker(agent, agentSsId, mtHeaders, mergedRows);
    updatedRowMap.clear(); // FIX 3: help GC release this memory promptly
  }

  return stats;
}



async function _syncAgentQL(agent, userRoleMap, triggerMap) {
  const agentSsId = agent.spreadsheetId || MAIN_SS_ID;
  const mtName    = agent.spreadsheetId ? AGT.MASTER_TRACKER  : (agent.agentCode + AGT.MASTER_TRACKER);
  const qlName    = agent.spreadsheetId ? AGT.QUALIFIED_LEADS : (agent.agentCode + AGT.QUALIFIED_LEADS);

  // Read MT — only care about COMPLETED rows
  const { headers: mtHeaders, rows: mtRows } = await readSheet(agentSsId, mtName);
  if (!mtHeaders.length || !mtRows.length) return 0;

  const callIdCol  = mtHeaders.indexOf('Call ID');
  const statusCol  = mtHeaders.indexOf('Status');
  const reqIdCol   = mtHeaders.indexOf('Request ID');
  if (callIdCol < 0 || statusCol < 0) return 0;

  const resultFields = resultFieldNames(agent.resultSchema);

  // Collect all COMPLETED + qualified call IDs from MT
  const completedQualified = [];
  for (const row of mtRows) {
    const status = String(row[statusCol] || '').toUpperCase();
    if (status !== 'COMPLETED') continue;

    // Must have result data — if out.* columns are empty this row isn't ready
    if (resultFields.length > 0) {
      const hasResult = resultFields.some(f => {
        const col = mtHeaders.indexOf('out.' + f);
        return col >= 0 && String(row[col] || '').trim() !== '';
      });
      if (!hasResult) continue;
    }

    // Extract result data from out.* columns
    const result = {};
    resultFields.forEach(f => {
      const col = mtHeaders.indexOf('out.' + f);
      if (col >= 0) result[f] = row[col];
    });

    // ── Qualification check — rules come LIVE from the Agents sheet ──────────
    // qualificationField / qualificationValues / qualificationRules are read
    // from the Agents sheet on every cache refresh (5-min TTL).
    // To change who qualifies: edit the Agents sheet → takes effect next cycle.
    // No code changes needed.
    if (!isQualified(agent, result)) continue;

    const callId = String(row[callIdCol] || '').trim();
    if (!callId) continue;

    completedQualified.push({ callId, row, result });
  }

  if (!completedQualified.length) return 0;

  // Log the active rule so it's visible in Render logs
  const ruleDesc = (() => {
    if (agent.qualificationRules?.length) {
      return agent.qualificationRules.map(r =>
        `${r.field} contains [${(r.keywords||[]).join('|')}]`
      ).join(' AND ');
    }
    if (agent.qualificationField) {
      const vals = agent.qualificationValues || [];
      return `${agent.qualificationField} ∈ [${vals.join('|') || 'any non-empty'}]`;
    }
    return 'no rule — all COMPLETED pass';
  })();
  console.log(`[ql-sync] ${agent.agentCode}: rule="${ruleDesc}" → ${completedQualified.length} candidates`);

  // Read QL — get existing call IDs to avoid duplicates
  const { headers: qlHeaders, rows: qlRows } = await readSheet(agentSsId, qlName);
  const qlIdCol = qlHeaders.indexOf('Call ID');
  const qlExistingIds = new Set();
  if (qlIdCol >= 0) qlRows.forEach(r => {
    const id = String(r[qlIdCol] || '').trim();
    if (id) qlExistingIds.add(id);
  });

  // Build rows to append — only those not already in QL
  const toAppend = [];

  for (const { callId, row, result } of completedQualified) {
    if (qlExistingIds.has(callId)) continue;

    const reqId  = reqIdCol >= 0 ? String(row[reqIdCol] || '') : '';
    const mobileCol = mtHeaders.indexOf('Mobile Number');
    const mobile    = mobileCol >= 0 ? String(row[mobileCol] || '') : '';
    const assignment = resolveLeadAssignment(reqId, agent.agentCode, mobile, row, mtHeaders, userRoleMap, triggerMap);

    // Map MT columns → QL columns by header name
    const qlRow = new Array(qlHeaders.length).fill('');
    qlHeaders.forEach((h, k) => {
      const mi = mtHeaders.indexOf(h);
      if (mi >= 0) qlRow[k] = row[mi];
    });

    const qlAssignCol    = qlHeaders.indexOf('Assigned To Email');
    const qlRecruiterCol = qlHeaders.indexOf('Recruiter');
    const qlDateAddedCol = qlHeaders.indexOf('Date Added');

    if (assignment.assignEmail) {
      if (qlAssignCol >= 0)    qlRow[qlAssignCol]    = assignment.assignEmail;
      if (qlRecruiterCol >= 0) qlRow[qlRecruiterCol] = assignment.recruiterName;
    }
    if (qlDateAddedCol >= 0) qlRow[qlDateAddedCol] = new Date().toISOString();

    toAppend.push(qlRow);
    qlExistingIds.add(callId); // prevent duplicate within this batch
  }

  // One batch append — N rows = 1 Sheets API call
  if (toAppend.length > 0) {
    await appendRows(agentSsId, qlName, toAppend);
  }

  return toAppend.length;
}

async function _refreshCampaignTracker(agent, agentSsId, mtHeaders, mtRows) {
  try {
    const ctName = agent.spreadsheetId ? AGT.CAMPAIGN_TRACKER : (agent.agentCode + AGT.CAMPAIGN_TRACKER);
    const qlName = agent.spreadsheetId ? AGT.QUALIFIED_LEADS : (agent.agentCode + AGT.QUALIFIED_LEADS);

    const { headers: ctHeaders, rows: ctRows } = await readSheet(agent.spreadsheetId || MAIN_SS_ID, ctName);
    if (!ctHeaders.length || !ctRows.length) return;

    const reqIdCol  = mtHeaders.indexOf('Request ID');
    const statusCol = mtHeaders.indexOf('Status');
    const durCol    = mtHeaders.indexOf('Duration (Minutes)');
    const ctReqCol  = ctHeaders.indexOf('Request ID');

    const stats = {};
    mtRows.forEach(r => {
      const rid = String(r[reqIdCol] || '');
      if (!rid) return;
      if (!stats[rid]) stats[rid] = { total: 0, completed: 0, notConnected: 0, failed: 0, minutes: 0, qualified: 0 };
      stats[rid].total++;
      const s = String(r[statusCol] || '').toUpperCase();
      if (s === 'COMPLETED')  { stats[rid].completed++; }
      if (s === 'NOT_CONNECTED') stats[rid].notConnected++;
      if (s === 'FAILED' || s === 'CANCELLED') stats[rid].failed++;
      stats[rid].minutes += Number(r[durCol] || 0);
    });

    // Count QL per request
    const { headers: qlH, rows: qlRows } = await readSheet(agent.spreadsheetId || MAIN_SS_ID, qlName);
    const qlRidCol = qlH.indexOf('Request ID');
    if (qlRidCol >= 0) {
      qlRows.forEach(r => {
        const rid = String(r[qlRidCol] || '');
        if (rid && stats[rid]) stats[rid].qualified++;
      });
    }

    const ctStatusColIdx = ctHeaders.indexOf('Status');
    const updates = [];
    ctRows.forEach((r, idx) => {
      const rid = String(r[ctReqCol] || '');
      const s = stats[rid];
      if (!s) return;
      const done = s.completed + s.notConnected + s.failed;
      const newStatus = done >= s.total ? 'COMPLETED' : 'IN_PROGRESS';
      const newRow = [...r];
      const set = (name, val) => { const k = ctHeaders.indexOf(name); if (k >= 0) newRow[k] = val; };
      set('Status',       newStatus);
      set('Completed',    s.completed);
      set('Connected',    s.completed);
      set('Not Connected', s.notConnected);
      set('Failed',       s.failed);
      set('Qualified',    s.qualified);
      set('Actual Minutes', Math.round(s.minutes * 100) / 100);
      set('Last Updated', new Date().toISOString());
      updates.push({ rowIndex: idx + 2, values: newRow });
    });

    // Single batchWriteRows call instead of N individual writes (quota fix)
    if (updates.length) {
      await batchWriteRows(agent.spreadsheetId || MAIN_SS_ID, ctName, updates);
    }
  } catch (err) {
    console.error(`[poll] refreshCampaignTracker error on ${agent.agentCode}:`, err.message);
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// JOB 2: BACKFILL MISSING OUTPUTS
// For COMPLETED rows missing result data, fetch from Hunar and fill in
// ─────────────────────────────────────────────────────────────────────────────
// AUTO-QUALIFY — standalone cron, runs every 10 min
//
// Scans every active agent's Master Tracker for COMPLETED rows with result data
// that haven't yet landed in Qualified_Leads, checks them against the agent's
// qualification rules (read LIVE from the Agents sheet), and batch-appends
// the qualifying ones.
//
// Rules live in Google Sheets → Agents tab:
//   • "Qualification Field"  + "Qualification Values"  → simple field∈values check
//   • "Qualification Rules"  (JSON array)              → multi-field AND logic
//
// To update who qualifies for any agent: edit those columns in the Agents sheet.
// No deploy, no restart — takes effect on the next 10-min cycle.
//
// This job runs even when pollActiveBatches is idle (e.g. outside polling hours)
// so any backlog from overnight completions is cleared first thing in the morning.
// ─────────────────────────────────────────────────────────────────────────────

async function autoQualifyLeads(agentCodeFilter = null) {
  const label = '[auto-qualify]';
  try {
    const agents = (await getAllAgents()).filter(a => a.active);
    const targets = agentCodeFilter ? agents.filter(a => a.agentCode === agentCodeFilter) : agents;
    const users = await getAllUsers();
    const userRoleMap = buildUserRoleMap(users);
    const { headers: trigHeaders, rows: trigRows } = await _getTriggerLog();
    const triggerMap = trigHeaders.length ? buildTriggerMap(trigRows, trigHeaders) : {};

    let grandTotal = 0;
    for (const agent of targets) {
      try {
        const added = await _syncAgentQL(agent, userRoleMap, triggerMap);
        if (added > 0) {
          console.log(`${label} ${agent.agentCode}: +${added} leads pushed to Qualified_Leads`);
          grandTotal += added;
        }
      } catch (err) {
        console.error(`${label} Error on ${agent.agentCode}:`, err.message);
      }
    }
    if (grandTotal > 0) console.log(`${label} Total: +${grandTotal} qualified leads this run`);
    else console.log(`${label} No new qualified leads found`);
  } catch (err) {
    console.error(`${label} Fatal:`, err.message);
  }
}

// ─────────────────────────────────────────────────────────────────────────────

async function backfillMissingOutputs(agentCodeFilter = null) {
  if (pollRunning) {
    console.log('[backfill] Skipping — poll is running.');
    return;
  }
  const agents = (await getAllAgents()).filter(a => a.active);
  const targets = agentCodeFilter ? agents.filter(a => a.agentCode === agentCodeFilter) : agents;

  let totalMissing = 0, totalFilled = 0;

  for (const agent of targets) {
    try {
      const r = await _backfillAgent(agent);
      if (r.missing > 0) {
        console.log(`[backfill] ${agent.agentCode}: missing=${r.missing} filled=${r.filled}`);
      }
      totalMissing += r.missing;
      totalFilled  += r.filled;
    } catch (err) {
      console.error(`[backfill] Error on ${agent.agentCode}:`, err.message);
    }
    await sleep(2000); // stagger between agents
  }

  return { totalMissing, totalFilled };
}

async function _backfillAgent(agent) {
  const mtName = agent.spreadsheetId ? AGT.MASTER_TRACKER : (agent.agentCode + AGT.MASTER_TRACKER);
  const qlName = agent.spreadsheetId ? AGT.QUALIFIED_LEADS : (agent.agentCode + AGT.QUALIFIED_LEADS);

  const { headers: mtHeaders, rows: mtRows } = await readSheet(agent.spreadsheetId || MAIN_SS_ID, mtName);
  if (!mtHeaders.length) return { missing: 0, filled: 0 };

  const callIdCol    = mtHeaders.indexOf('Call ID');
  const statusCol    = mtHeaders.indexOf('Status');
  const resultFields = resultFieldNames(agent.resultSchema);
  const customVars   = agent.customVariables || [];

  if (callIdCol < 0 || !resultFields.length) return { missing: 0, filled: 0 };

  const { headers: qlHeaders, rows: qlRows } = await readSheet(agent.spreadsheetId || MAIN_SS_ID, qlName);
  const qlCallIdCol  = qlHeaders.indexOf('Call ID');
  const qlRowByCallId = {};
  if (qlCallIdCol >= 0) {
    qlRows.forEach((r, i) => {
      const cid = String(r[qlCallIdCol] || '').trim();
      if (cid) qlRowByCallId[cid] = { rowIndex: i + 2, row: r };
    });
  }

  let missing = 0, filled = 0;

  for (let i = 0; i < mtRows.length; i++) {
    const row = mtRows[i];
    const callId = String(row[callIdCol] || '').trim();
    const status = String(row[statusCol] || '').toUpperCase();

    if (!callId || status !== 'COMPLETED') continue;

    // Check if result data already exists
    const hasResult = resultFields.some(f => {
      const col = mtHeaders.indexOf('out.' + f);
      return col >= 0 && String(row[col] || '').trim() !== '';
    });
    if (hasResult) continue;

    missing++;
    const r = await getCall(callId);
    if (!r.ok) continue;

    const d = r.data;
    const result = d.result || {};
    const newRow = [...row];
    const setH = (name, val) => { const k = mtHeaders.indexOf(name); if (k >= 0) newRow[k] = val; };

    setH('Duration (Minutes)', d.duration_minutes ?? 0);
    setH('Duration (Seconds)', d.duration_seconds ?? 0);
    setH('Started At',         d.started_at || '');
    setH('Ended At',           d.ended_at || '');
    setH('Answered By',        d.answered_by || '');
    setH('Engagement Status',  d.engagement_status || '');
    setH('Call Ended By',      d.call_ended_by || '');
    setH('Recording URL',      d.recording_url || '');
    setH('Updated At',         new Date().toISOString());
    customVars.forEach(cv => { if (d.custom_data?.[cv] !== undefined) setH('in.' + cv, d.custom_data[cv]); });
    resultFields.forEach(f => { setH('out.' + f, result[f] !== undefined ? result[f] : ''); });

    await writeRow(agent.spreadsheetId || MAIN_SS_ID, mtName, i + 2, newRow);
    filled++;

    // Mirror to QL if this call is there
    if (qlCallIdCol >= 0 && qlRowByCallId[callId]) {
      const { rowIndex: qlRowIdx, row: qlRow } = qlRowByCallId[callId];
      const newQlRow = [...qlRow];
      let changed = false;
      resultFields.forEach(f => {
        const col = qlHeaders.indexOf('out.' + f);
        if (col >= 0 && String(newQlRow[col] || '').trim() === '' && result[f] !== undefined) {
          newQlRow[col] = result[f];
          changed = true;
        }
      });
      if (changed) await writeRow(agent.spreadsheetId || MAIN_SS_ID, qlName, qlRowIdx, newQlRow);
    }

    await sleep(400);
  }

  return { missing, filled };
}

// ─────────────────────────────────────────────────────────────────────────────
// JOB 3: REPAIR UNASSIGNED LEADS
// Assigns QL leads based on who triggered the campaign
// ─────────────────────────────────────────────────────────────────────────────

async function repairUnassignedLeads() {
  const agents  = (await getAllAgents()).filter(a => a.active);
  const users   = await getAllUsers();
  const userRoleMap = buildUserRoleMap(users);

  // FIX 1: Use cached Trigger Log here too
  const { headers: trigHeaders, rows: trigRows } = await _getTriggerLog();
  const triggerMap = trigHeaders.length ? buildTriggerMap(trigRows, trigHeaders) : {};

  let totalFixed = 0;

  for (const agent of agents) {
    try {
      const agentSsId2 = agent.spreadsheetId || MAIN_SS_ID;
      const qlName = agent.spreadsheetId ? AGT.QUALIFIED_LEADS : (agent.agentCode + AGT.QUALIFIED_LEADS);
      const { headers, rows } = await readSheet(agent.spreadsheetId || MAIN_SS_ID, qlName);
      if (!headers.length || !rows.length) continue;

      const assignCol    = headers.indexOf('Assigned To Email');
      const recruiterCol = headers.indexOf('Recruiter');
      const requestIdCol = headers.indexOf('Request ID');
      if (assignCol < 0 || requestIdCol < 0) continue;

      const updates = [];
      rows.forEach((row, i) => {
        const assigned = String(row[assignCol] || '').trim();
        if (assigned) return;
        const reqId = String(row[requestIdCol] || '').trim();
        if (!reqId) return;
        const triggeredBy = triggerMap[`${agent.agentCode}|${reqId}`];
        if (!triggeredBy) return;
        const u = userRoleMap[triggeredBy];
        if (!u) return;
        const newRow = [...row];
        newRow[assignCol]    = triggeredBy;
        if (recruiterCol >= 0) newRow[recruiterCol] = u.name;
        updates.push({ rowIndex: i + 2, values: newRow });
      });

      for (const u of updates) {
        await writeRow(agent.spreadsheetId || MAIN_SS_ID, qlName, u.rowIndex, u.values);
        totalFixed++;
      }
      if (updates.length) await sleep(500);
    } catch (err) {
      console.error(`[repair] Error on ${agent.agentCode}:`, err.message);
    }
  }

  if (totalFixed) console.log(`[repair] Fixed ${totalFixed} unassigned leads`);
}

// ─────────────────────────────────────────────────────────────────────────────
// JOB 4: CLEANUP EXPIRED SESSIONS
// ─────────────────────────────────────────────────────────────────────────────

async function cleanupExpiredSessions() {
  const { headers, rows } = await readSheet(MAIN_SS_ID, PORTAL.SESSIONS);
  if (!headers.length || !rows.length) return;

  const expiresCol = headers.indexOf('Expires At');
  if (expiresCol < 0) return;

  const now = Date.now();
  const toDelete = rows
    .map((r, i) => ({ rowIndex: i + 2, expires: new Date(r[expiresCol] || 0).getTime() }))
    .filter(r => r.expires < now)
    .map(r => r.rowIndex);

  if (toDelete.length) {
    await deleteRows(MAIN_SS_ID, PORTAL.SESSIONS, toDelete);
    console.log(`[sessions] Deleted ${toDelete.length} expired sessions`);
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// JOB 5: DEDUPE ALL SHEETS
// Removes duplicate Call ID rows from MT, QL, NC sheets
// ─────────────────────────────────────────────────────────────────────────────

async function dedupeAllSheets() {
  const agents = await getAllAgents();
  let total = 0;

  for (const agent of agents) {
    // FIX 4: was using undefined variable `dedupeSsId` — use correct spreadsheet ID
    const agentSsId = agent.spreadsheetId || MAIN_SS_ID;

    for (const suffix of [AGT.MASTER_TRACKER, AGT.QUALIFIED_LEADS, AGT.NOT_CONNECTED]) {
      try {
        const sheetName = agent.spreadsheetId ? suffix : (agent.agentCode + suffix);
        const { headers, rows } = await readSheet(agentSsId, sheetName);
        if (!headers.length) continue;
        const cidCol = headers.indexOf('Call ID');
        if (cidCol < 0) continue;

        const seen = new Set();
        const toDelete = [];
        rows.forEach((r, i) => {
          const cid = String(r[cidCol] || '').trim();
          if (!cid) return;
          if (seen.has(cid)) toDelete.push(i + 2);
          else seen.add(cid);
        });

        if (toDelete.length) {
          await deleteRows(agentSsId, sheetName, toDelete);
          total += toDelete.length;
          console.log(`[dedupe] ${sheetName}: removed ${toDelete.length} duplicates`);
        }
        await sleep(500);
      } catch (err) {
        console.error(`[dedupe] Error on ${agent.agentCode}/${suffix}:`, err.message);
      }
    }
  }

  console.log(`[dedupe] Total removed: ${total}`);
}

// ─────────────────────────────────────────────────────────────────────────────
// JOB 6-8: ARCHIVE COMPLETED DATA → TEAM SPREADSHEETS
// ─────────────────────────────────────────────────────────────────────────────

function isLeadCompleted(callStatus, feedback) {
  const cs = String(callStatus || '').trim();
  const fb = String(feedback || '').trim();
  if (cs === 'Hiring On hold' || cs === 'Hiring On Hold') return true;
  if (cs === 'DNP-3' || cs === 'DNP-4' || cs === 'DNP-5') return true;
  if ((cs === 'Connected' || cs === 'Irrelevant') && fb !== '') return true;
  return false;
}

async function _agentToTeamMap() {
  const users = await getAllUsers();
  const emailToTeam = {};
  users.forEach(u => { if (u.team) emailToTeam[u.email] = u.team; });
  const agents = await getAllAgents();
  const map = {};
  agents.forEach(a => {
    const team = emailToTeam[(a.createdBy || '').toLowerCase()];
    if (team) map[a.agentCode] = team;
  });
  return map;
}

async function _getTeamSS(teamName) {
  const teams = await getAllTeams();
  const team = teams.find(t => t.name === teamName);
  if (!team?.spreadsheetId) return null;
  return team.spreadsheetId;
}

async function archiveCompletedLeads() {
  console.log('[archive] Starting archiveCompletedLeads...');
  const agentTeam = await _agentToTeamMap();
  const agents    = await getAllAgents();
  let totalArchived = 0;

  for (const agent of agents) {
    const team = agentTeam[agent.agentCode];
    if (!team) continue;
    const teamSSId = await _getTeamSS(team);
    if (!teamSSId) { console.log(`[archive] No spreadsheet for team: ${team}`); continue; }

    try {
      const qlName = agent.spreadsheetId ? AGT.QUALIFIED_LEADS : (agent.agentCode + AGT.QUALIFIED_LEADS);
      const { headers, rows } = await readSheet(agent.spreadsheetId || MAIN_SS_ID, qlName);
      if (!headers.length || !rows.length) continue;

      const csCol = headers.indexOf('Call Status');
      const fbCol = headers.indexOf('Feedback');
      if (csCol < 0 || fbCol < 0) continue;

      const toArchive = [];
      const toDelete  = [];
      rows.forEach((r, i) => {
        if (isLeadCompleted(r[csCol], r[fbCol])) {
          toArchive.push(r);
          toDelete.push(i + 2);
        }
      });

      if (!toArchive.length) continue;

      // Ensure archive sheet exists in team SS
      await ensureSheet(teamSSId, ARCHIVE.LEADS,
        [...headers, 'Archived At', 'Archived From'],
        '#1a7f4b'
      );

      // Append archived rows
      const now = new Date().toISOString();
      const archiveRows = toArchive.map(r => [...r, now, qlName]);
      await appendRows(teamSSId, ARCHIVE.LEADS, archiveRows);

      // Delete from main SS
      await deleteRows(agent.spreadsheetId || MAIN_SS_ID, qlName, toDelete);
      totalArchived += toArchive.length;
      console.log(`[archive] ${agent.agentCode}: archived ${toArchive.length} leads to ${team}`);
    } catch (err) {
      console.error(`[archive] QL error on ${agent.agentCode}:`, err.message);
    }
    await sleep(1000);
  }
  console.log(`[archive] archiveCompletedLeads done. Total: ${totalArchived}`);
}

async function archiveCompletedMT() {
  console.log('[archive] Starting archiveCompletedMT...');
  const agentTeam = await _agentToTeamMap();
  const agents    = await getAllAgents();
  let totalArchived = 0;

  for (const agent of agents) {
    const team = agentTeam[agent.agentCode];
    if (!team) continue;
    const teamSSId = await _getTeamSS(team);
    if (!teamSSId) continue;

    try {
      // Get call IDs already archived in team SS _Completed_Leads
      const { headers: archQLH, rows: archQLRows } = await readSheet(teamSSId, ARCHIVE.LEADS);
      const archCidCol = archQLH.indexOf('Call ID');
      const archivedIds = new Set();
      if (archCidCol >= 0) archQLRows.forEach(r => { if (r[archCidCol]) archivedIds.add(String(r[archCidCol]).trim()); });
      if (!archivedIds.size) continue;

      const mtName = agent.spreadsheetId ? AGT.MASTER_TRACKER : (agent.agentCode + AGT.MASTER_TRACKER);
      const { headers: mtHeaders, rows: mtRows } = await readSheet(agent.spreadsheetId || MAIN_SS_ID, mtName);
      if (!mtHeaders.length) continue;
      const mtCidCol = mtHeaders.indexOf('Call ID');
      if (mtCidCol < 0) continue;

      // Check what's already in team MT archive
      await ensureSheet(teamSSId, ARCHIVE.MT,
        [...mtHeaders, 'Archived At', 'Archived From'],
        '#34495e'
      );
      const { headers: archMTH, rows: archMTRows } = await readSheet(teamSSId, ARCHIVE.MT);
      const archMTCidCol = archMTH.indexOf('Call ID');
      const alreadyArchived = new Set();
      if (archMTCidCol >= 0) archMTRows.forEach(r => { if (r[archMTCidCol]) alreadyArchived.add(String(r[archMTCidCol]).trim()); });

      const toArchive = [];
      const toDelete  = [];
      mtRows.forEach((r, i) => {
        const cid = String(r[mtCidCol] || '').trim();
        if (cid && archivedIds.has(cid) && !alreadyArchived.has(cid)) {
          toArchive.push(r);
          toDelete.push(i + 2);
        }
      });

      if (!toArchive.length) continue;
      const now = new Date().toISOString();
      await appendRows(teamSSId, ARCHIVE.MT, toArchive.map(r => [...r, now, mtName]));
      await deleteRows(agent.spreadsheetId || MAIN_SS_ID, mtName, toDelete);
      totalArchived += toArchive.length;
      console.log(`[archive] ${agent.agentCode}: archived ${toArchive.length} MT rows to ${team}`);
    } catch (err) {
      console.error(`[archive] MT error on ${agent.agentCode}:`, err.message);
    }
    await sleep(1000);
  }
  console.log(`[archive] archiveCompletedMT done. Total: ${totalArchived}`);
}

async function archiveManualTracker() {
  console.log('[archive] Starting archiveManualTracker...');
  const teams = await getAllTeams();
  const { headers, rows } = await readSheet(MAIN_SS_ID, QUEUE.MANUAL_TRACKER);
  if (!headers.length || !rows.length) return;

  const csCol   = headers.indexOf('Call Status');
  const teamCol = headers.indexOf('Team');
  const dateCol = headers.indexOf('Date');
  if (csCol < 0) return;

  const COMPLETED_STATUSES = new Set(['Connected', 'DNP-3', 'DNP-4', 'DNP-5', 'Hiring On Hold', 'Hiring On hold', 'Irrelevant', 'Not Interested']);
  const sevenDaysAgo = Date.now() - 7 * 24 * 3600 * 1000;

  const byTeam = {};
  const toDelete = [];

  rows.forEach((r, i) => {
    const cs   = String(r[csCol] || '').trim();
    const team = teamCol >= 0 ? String(r[teamCol] || '').trim() : '';
    const dateVal = dateCol >= 0 ? r[dateCol] : null;

    const isCompleted = COMPLETED_STATUSES.has(cs);
    const isOld = dateVal ? new Date(dateVal).getTime() < sevenDaysAgo : false;

    if ((!isCompleted && !isOld) || !team) return;
    if (!byTeam[team]) byTeam[team] = [];
    byTeam[team].push({ row: r, rowIndex: i + 2 });
    toDelete.push(i + 2);
  });

  let totalArchived = 0;
  const now = new Date().toISOString();

  for (const [teamName, items] of Object.entries(byTeam)) {
    const team = teams.find(t => t.name === teamName);
    if (!team?.spreadsheetId) continue;
    try {
      await ensureSheet(team.spreadsheetId, ARCHIVE.MANUAL,
        [...headers, 'Archived At'],
        '#0369a1'
      );
      await appendRows(team.spreadsheetId, ARCHIVE.MANUAL, items.map(item => [...item.row, now]));
      totalArchived += items.length;
      console.log(`[archive] Manual: archived ${items.length} rows to ${teamName}`);
    } catch (err) {
      console.error(`[archive] Manual error for ${teamName}:`, err.message);
    }
    await sleep(500);
  }

  if (toDelete.length) await deleteRows(MAIN_SS_ID, QUEUE.MANUAL_TRACKER, toDelete);
  console.log(`[archive] archiveManualTracker done. Total: ${totalArchived}`);
}

// ─────────────────────────────────────────────────────────────────────────────
// JOB 9: PROCESS CALLBACK QUEUE
// Triggers callbacks for calls where candidate said "call me back"
// ─────────────────────────────────────────────────────────────────────────────

async function processCallbackQueue() {
  console.log('[callbacks] Processing callback queue...');
  const { headers, rows } = await readSheet(MAIN_SS_ID, QUEUE.CALLBACK);
  if (!headers.length || !rows.length) return;

  const idx = h => headers.indexOf(h);
  const today = istDateStr();

  const groups = {};
  rows.forEach((r, i) => {
    const status        = String(r[idx('Status')] || '');
    const scheduledDate = String(r[idx('Scheduled Date')] || '');
    if (status !== 'PENDING' || scheduledDate > today) return;

    const agentCode = String(r[idx('Agent Code')] || '');
    const team      = String(r[idx('Team')] || '');
    const key = `${agentCode}|||${team}`;
    if (!groups[key]) groups[key] = { agentCode, team, items: [] };
    groups[key].items.push({ rowIndex: i + 2, data: r });
  });

  const agents = await getAllAgents();
  const agentMap = {};
  agents.forEach(a => { agentMap[a.agentCode] = a; });

  for (const [key, group] of Object.entries(groups)) {
    const agent = agentMap[group.agentCode];
    if (!agent?.active) {
      await _markCallbackRows(headers, group.items, 'SKIPPED', '');
      continue;
    }
    await _fireCallbackGroup(agent, group.team, group.items, headers, today);
    await sleep(2000);
  }
}

async function _fireCallbackGroup(agent, team, items, headers, todayStr) {
  const idx = h => headers.indexOf(h);
  const contacts = [];
  const assignMap = {};

  items.forEach(item => {
    const mobile  = String(item.data[idx('Mobile Number')] || '').trim();
    const callee  = String(item.data[idx('Callee Name')] || '');
    const assignEmail = String(item.data[idx('Assigned To Email')] || '').toLowerCase().trim();
    if (!mobile) return;
    contacts.push({ callee_name: callee, mobile_number: mobile, custom_data: {} });
    assignMap[mobile] = assignEmail;
  });

  if (!contacts.length) {
    await _markCallbackRows(headers, items, 'SKIPPED', '');
    return;
  }

  const seen = new Set();
  const unique = contacts.filter(c => {
    if (seen.has(c.mobile_number)) return false;
    seen.add(c.mobile_number);
    return true;
  });

  const requestId = `CB_AUTO_${istDateStr().replace(/-/g, '')}_${agent.agentCode.slice(0, 8)}_${(team || 'noteam').replace(/[^a-z0-9]/gi, '').slice(0, 8)}`;
  const result = await bulkCall({
    agent_id: agent.agentId, request_id: requestId,
    data: unique, remove_invalid_rows: true,
    remove_duplicate_phone_numbers: true,
    timezone: 'Asia/Kolkata',
  });

  if (!result.ok) {
    console.error(`[callbacks] Bulk call failed:`, result.error);
    return;
  }

  const createdCalls = Array.isArray(result.data) ? result.data : [];
  await _seedMasterTracker(agent, createdCalls, requestId, 'system');
  await _markCallbackRows(headers, items, 'TRIGGERED', requestId);
  console.log(`[callbacks] Fired ${unique.length} callbacks for ${agent.agentCode}/${team}`);
}

async function _markCallbackRows(headers, items, status, newRequestId) {
  const statusCol  = headers.indexOf('Status');
  const newReqCol  = headers.indexOf('New Request ID');
  const triggedCol = headers.indexOf('Triggered At');

  for (const item of items) {
    const newRow = [...item.data];
    if (statusCol >= 0)  newRow[statusCol]  = status;
    if (newReqCol >= 0 && newRequestId) newRow[newReqCol] = newRequestId;
    if (triggedCol >= 0 && status === 'TRIGGERED') newRow[triggedCol] = new Date().toISOString();
    await writeRow(MAIN_SS_ID, QUEUE.CALLBACK, item.rowIndex, newRow);
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// JOB 10: PROCESS RETRY QUEUE
// Retries NOT_CONNECTED / FAILED calls from completed campaigns
// ─────────────────────────────────────────────────────────────────────────────

async function processRetryQueue() {
  console.log('[retries] Processing retry queue...');
  const { headers, rows } = await readSheet(MAIN_SS_ID, QUEUE.RETRY);
  if (!headers.length || !rows.length) return;

  const idx    = h => headers.indexOf(h);
  const today  = istDateStr();
  const agents = await getAllAgents();
  const agentMap = {};
  agents.forEach(a => { agentMap[a.agentCode] = a; });

  for (let i = 0; i < rows.length; i++) {
    const row = rows[i];
    const status      = String(row[idx('Status')] || '');
    const retryAfter  = String(row[idx('Retry After Date')] || '');
    if (status !== 'PENDING' || retryAfter > today) continue;

    const agentCode     = String(row[idx('Agent Code')] || '');
    const originalReqId = String(row[idx('Original Request ID')] || '');
    const team          = String(row[idx('Team')] || '');
    const agent         = agentMap[agentCode];
    const rowIndex      = i + 2;

    if (!agent?.active) {
      const newRow = [...row];
      newRow[idx('Status')] = 'SKIPPED';
      await writeRow(MAIN_SS_ID, QUEUE.RETRY, rowIndex, newRow);
      continue;
    }

    const result = await _fireRetryGroup(agent, team, originalReqId);
    const newRow = [...row];
    newRow[idx('Status')]        = result.ok ? 'TRIGGERED' : 'SKIPPED';
    newRow[idx('New Request ID')] = result.newRequestId || '';
    newRow[idx('Triggered At')]   = new Date().toISOString();
    await writeRow(MAIN_SS_ID, QUEUE.RETRY, rowIndex, newRow);
    await sleep(2000);
  }
}

async function _fireRetryGroup(agent, team, originalReqId) {
  const mtName = agent.spreadsheetId ? AGT.MASTER_TRACKER : (agent.agentCode + AGT.MASTER_TRACKER);
  const { headers, rows } = await readSheet(agent.spreadsheetId || MAIN_SS_ID, mtName);
  if (!headers.length) return { ok: false };

  const ridCol     = headers.indexOf('Request ID');
  const statusCol  = headers.indexOf('Status');
  const calleeCol  = headers.indexOf('Callee Name');
  const mobileCol  = headers.indexOf('Mobile Number');

  const contacts = [];
  rows.forEach(r => {
    if (String(r[ridCol] || '') !== originalReqId) return;
    const s = String(r[statusCol] || '').toUpperCase();
    if (s !== 'NOT_CONNECTED' && s !== 'FAILED') return;
    const mobile = String(r[mobileCol] || '').trim();
    if (!mobile) return;
    contacts.push({ callee_name: String(r[calleeCol] || ''), mobile_number: mobile, custom_data: {} });
  });

  if (!contacts.length) return { ok: false };

  const seen = new Set();
  const unique = contacts.filter(c => {
    if (seen.has(c.mobile_number)) return false;
    seen.add(c.mobile_number);
    return true;
  });

  const ts = istDateStr().replace(/-/g, '');
  const requestId = `NC_AUTO_${ts}_${agent.agentCode.slice(0, 8)}_${(team || 'noteam').replace(/[^a-z0-9]/gi, '').slice(0, 8)}`;

  const result = await bulkCall({
    agent_id: agent.agentId, request_id: requestId,
    data: unique, remove_invalid_rows: true,
    remove_duplicate_phone_numbers: true,
    timezone: 'Asia/Kolkata',
  });

  if (!result.ok) return { ok: false };

  const createdCalls = Array.isArray(result.data) ? result.data : [];
  await _seedMasterTracker(agent, createdCalls, requestId, 'system');
  console.log(`[retries] Fired ${unique.length} retries for ${agent.agentCode}/${team} (original: ${originalReqId})`);
  return { ok: true, newRequestId: requestId };
}

async function _seedMasterTracker(agent, createdCalls, requestId, triggeredBy) {
  if (!createdCalls.length) return;
  const agentSsId = agent.spreadsheetId || MAIN_SS_ID;
  const mtName = agent.spreadsheetId ? AGT.MASTER_TRACKER : (agent.agentCode + AGT.MASTER_TRACKER);
  const { headers, rows } = await readSheet(agentSsId, mtName);
  if (!headers.length) return;

  const cidCol = headers.indexOf('Call ID');
  const existing = new Set();
  if (cidCol >= 0) rows.forEach(r => { if (r[cidCol]) existing.add(String(r[cidCol]).trim()); });

  const newRows = [];
  createdCalls.forEach(c => {
    const cid = String(c.id || '').trim();
    if (!cid || existing.has(cid)) return;
    existing.add(cid);
    const row = new Array(headers.length).fill('');
    const setH = (name, val) => { const k = headers.indexOf(name); if (k >= 0) row[k] = val; };
    setH('Call ID', cid);
    setH('Request ID', c.request_id || requestId);
    setH('Callee Name', c.callee_name || '');
    setH('Mobile Number', c.mobile_number || '');
    setH('Status', c.status || 'INITIATED');
    setH('Triggered By', triggeredBy);
    setH('Created At', new Date().toISOString());
    newRows.push(row);
  });

  if (newRows.length) await appendRows(agentSsId, mtName, newRows);
}

// ─────────────────────────────────────────────────────────────────────────────
// EOD SWEEP — runs daily at 9pm IST
// For every active campaign (not COMPLETED in Campaign Tracker),
// fetches ALL non-terminal rows with no cap — cleans up end-of-day stragglers
// ─────────────────────────────────────────────────────────────────────────────

async function eodSweep() {
  if (pollRunning) {
    console.log('[eod] Poll running — will retry next trigger.');
    return;
  }
  console.log('[eod] Starting end-of-day sweep...');
  const agents = (await getAllAgents()).filter(a => a.active);
  let totalFetched = 0, totalUpdated = 0;

  for (const agent of agents) {
    try {
      const agentSsId = agent.spreadsheetId || MAIN_SS_ID;
      const mtName    = agent.spreadsheetId ? AGT.MASTER_TRACKER : (agent.agentCode + AGT.MASTER_TRACKER);
      const ctName    = agent.spreadsheetId ? AGT.CAMPAIGN_TRACKER : (agent.agentCode + AGT.CAMPAIGN_TRACKER);

      // Find active (non-completed) campaigns
      const { headers: ctH, rows: ctRows } = await readSheet(agentSsId, ctName);
      const ctReqCol    = ctH.indexOf('Request ID');
      const ctStatusCol = ctH.indexOf('Status');
      const activeCampaigns = new Set();
      if (ctReqCol >= 0 && ctStatusCol >= 0) {
        ctRows.forEach(r => {
          const rid = String(r[ctReqCol] || '').trim();
          const st  = String(r[ctStatusCol] || '').toUpperCase();
          if (rid && st !== 'COMPLETED') activeCampaigns.add(rid);
        });
      }
      if (!activeCampaigns.size) continue;

      const { headers: mtH, rows: mtRows } = await readSheet(agentSsId, mtName);
      if (!mtH.length) continue;

      const callIdCol  = mtH.indexOf('Call ID');
      const statusCol  = mtH.indexOf('Status');
      const reqIdCol   = mtH.indexOf('Request ID');
      const resultFields = resultFieldNames(agent.resultSchema);
      const customVars   = agent.customVariables || [];
      if (callIdCol < 0 || statusCol < 0) continue;

      const rowUpdates = [];

      for (let i = 0; i < mtRows.length; i++) {
        const row    = mtRows[i];
        const callId = String(row[callIdCol] || '').trim();
        if (!callId) continue;

        const status = String(row[statusCol] || '').toUpperCase();
        const reqId  = reqIdCol >= 0 ? String(row[reqIdCol] || '').trim() : '';

        // Only rows belonging to active campaigns
        if (reqId && !activeCampaigns.has(reqId)) continue;

        // Skip terminal rows
        if (status === 'NOT_CONNECTED' || status === 'FAILED' || status === 'CANCELLED') continue;

        // Skip COMPLETED rows that already have result data
        if (status === 'COMPLETED') {
          const hasResult = resultFields.some(f => {
            const col = mtH.indexOf('out.' + f);
            return col >= 0 && String(row[col] || '').trim() !== '';
          });
          if (hasResult) continue;
        }

        totalFetched++;
        const r = await getCall(callId);
        if (!r.ok) continue;

        const d         = r.data;
        const newStatus = String(d.status || status).toUpperCase();
        const result    = d.result || {};
        const newRow    = [...row];
        const setH = (name, val) => { const k = mtH.indexOf(name); if (k >= 0) newRow[k] = val; };

        setH('Status',             newStatus);
        setH('Duration (Minutes)', d.duration_minutes ?? 0);
        setH('Duration (Seconds)', d.duration_seconds ?? 0);
        setH('Started At',         d.started_at || '');
        setH('Ended At',           d.ended_at   || '');
        setH('Answered By',        d.answered_by || '');
        setH('Engagement Status',  d.engagement_status || '');
        setH('Call Ended By',      d.call_ended_by || '');
        setH('Recording URL',      d.recording_url || '');
        setH('Updated At',         new Date().toISOString());
        customVars.forEach(cv => { if (d.custom_data?.[cv] !== undefined) setH('in.' + cv, d.custom_data[cv]); });
        resultFields.forEach(f  => { setH('out.' + f, result[f] !== undefined ? result[f] : ''); });

        rowUpdates.push({ rowIndex: i + 2, values: newRow });
        totalUpdated++;
        await sleep(150);
      }

      // Flush writes in batches of 100
      if (rowUpdates.length) {
        for (let i = 0; i < rowUpdates.length; i += 100) {
          await batchWriteRows(agentSsId, mtName, rowUpdates.slice(i, i + 100));
          if (i + 100 < rowUpdates.length) await sleep(500);
        }
        console.log(`[eod] ${agent.agentCode}: fetched=${rowUpdates.length} for ${activeCampaigns.size} active campaigns`);
      }

      await sleep(1500);
    } catch (err) {
      console.error(`[eod] Error on ${agent.agentCode}:`, err.message);
    }
  }

  console.log(`[eod] Done — totalFetched=${totalFetched} totalUpdated=${totalUpdated}`);
}

// ─────────────────────────────────────────────────────────────────────────────
// PUBLIC API: read archived data from team spreadsheets
// (called by server.js for archive API endpoints)
// ─────────────────────────────────────────────────────────────────────────────

async function getArchivedLeads(teamName) {
  const teamSSId = await _getTeamSS(teamName);
  if (!teamSSId) return [];
  return readSheetAsObjects(teamSSId, ARCHIVE.LEADS);
}

async function getArchivedMT(teamName) {
  const teamSSId = await _getTeamSS(teamName);
  if (!teamSSId) return [];
  return readSheetAsObjects(teamSSId, ARCHIVE.MT);
}

async function getArchivedManual(teamName) {
  const teamSSId = await _getTeamSS(teamName);
  if (!teamSSId) return [];
  return readSheetAsObjects(teamSSId, ARCHIVE.MANUAL);
}

// ─────────────────────────────────────────────────────────────────────────────
// STATUS & HEALTH
// ─────────────────────────────────────────────────────────────────────────────

function getStatus() {
  return {
    pollRunning,
    lastPollTime,
    lastPollStats,  // per-agent: { fetched, updated, errors, pollCap, backfillCap }
    jobStats,
    pollBudget: POLL_BUDGET,  // current budget config — tune POLL_GLOBAL / BACKFILL_GLOBAL etc.
    uptime: Math.round(process.uptime()),
    timestamp: new Date().toISOString(),
  };
}

// ─────────────────────────────────────────────────────────────────────────────
// SCHEDULER
// ─────────────────────────────────────────────────────────────────────────────

const IST_TZ = 'Asia/Kolkata'; // node-cron supports IANA tz with timezone option

async function startPoller() {
  try {
    await testConnection(MAIN_SS_ID);
    console.log('[poller] Google Sheets connected ✓');
  } catch (err) {
    console.error('[poller] Failed to connect:', err.message);
    process.exit(1);
  }

  // Poll every 3 minutes (was 2 min — reduced to give Sheets quota more recovery time
  // between cycles; with 9 agents and sequential scanning the cycle itself takes ~60-90s)
  cron.schedule('*/3 * * * *', async () => {
    try { await pollActiveBatches(); } catch (e) { console.error('[cron:poll]', e.message); }
  });

  // Backfill every 15 minutes (offset by 7 min from poll to avoid overlap)
  cron.schedule('7,22,37,52 * * * *', async () => {
    try { await backfillMissingOutputs(); } catch (e) { console.error('[cron:backfill]', e.message); }
  });

  // Auto-qualify every 10 minutes (offset 4 min to avoid colliding with poll + backfill)
  // Reads qualification rules LIVE from Agents sheet — no restart needed when rules change.
  cron.schedule('4,14,24,34,44,54 * * * *', async () => {
    try { await autoQualifyLeads(); } catch (e) { console.error('[cron:qualify]', e.message); }
  });

  // Repair unassigned leads every 20 minutes
  cron.schedule('*/20 * * * *', async () => {
    try { await repairUnassignedLeads(); } catch (e) { console.error('[cron:repair]', e.message); }
  });

  // Cleanup sessions every hour
  cron.schedule('0 * * * *', async () => {
    try { await cleanupExpiredSessions(); } catch (e) { console.error('[cron:sessions]', e.message); }
  });

  // Daily jobs in IST (cron uses UTC, IST = UTC+5:30)
  // 1am IST = 19:30 UTC previous day
  cron.schedule('30 19 * * *', async () => {
    try { await dedupeAllSheets(); } catch (e) { console.error('[cron:dedupe]', e.message); }
  });

  // 2am IST = 20:30 UTC previous day
  cron.schedule('30 20 * * *', async () => {
    try { await archiveCompletedLeads(); } catch (e) { console.error('[cron:archLeads]', e.message); }
  });

  // 3am IST = 21:30 UTC previous day
  cron.schedule('30 21 * * *', async () => {
    try { await archiveCompletedMT(); } catch (e) { console.error('[cron:archMT]', e.message); }
  });

  // 4am IST = 22:30 UTC previous day
  cron.schedule('30 22 * * *', async () => {
    try { await archiveManualTracker(); } catch (e) { console.error('[cron:archManual]', e.message); }
  });

  // 11am IST = 5:30 UTC
  cron.schedule('30 5 * * *', async () => {
    try { await processCallbackQueue(); } catch (e) { console.error('[cron:callbacks]', e.message); }
    await sleep(30000);
    try { await processRetryQueue(); } catch (e) { console.error('[cron:retries]', e.message); }
  });

  // 9pm IST = 15:30 UTC — end of day sweep, all active campaigns fully updated
  cron.schedule('30 15 * * *', async () => {
    try { await eodSweep(); } catch (e) { console.error('[cron:eod]', e.message); }
  });

  console.log('[poller] All 11 jobs scheduled ✓');

  // Run poll immediately on startup
  setTimeout(() => {
    pollActiveBatches().catch(e => console.error('[startup poll]', e.message));
  }, 5000);
}

module.exports = {
  startPoller,
  pollActiveBatches,
  autoQualifyLeads,
  backfillMissingOutputs,
  repairUnassignedLeads,
  cleanupExpiredSessions,
  dedupeAllSheets,
  archiveCompletedLeads,
  archiveCompletedMT,
  archiveManualTracker,
  processCallbackQueue,
  processRetryQueue,
  eodSweep,
  getArchivedLeads,
  getArchivedMT,
  getArchivedManual,
  getStatus,
  getAllAgents,
  getAllUsers,
  getAllTeams,
};