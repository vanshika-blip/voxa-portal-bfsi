'use strict';
/**
 * auth.js — Node-side authentication for Voxa Portal
 *
 * Handles login, session create/validate/destroy, password hashing
 * Reads Users + Sessions sheets directly via Google Sheets API (sheets.js)
 * Completely independent of GAS — no proxy needed for auth
 */

const crypto = require('crypto');
const { readSheet, appendRows, writeRow, readRange } = require('./sheets');

const MAIN_SS_ID      = process.env.SPREADSHEET_ID;
const SESSION_TTL_MS  = 12 * 60 * 60 * 1000; // 12 hours
const PW_ITERATIONS   = 2000;

// ─── In-memory session cache (fast lookups) ───────────────────────────────────
// Sessions are also persisted to the Sessions sheet
const _sessionCache = new Map(); // token → { email, role, team, name, expires }

// ─── Password utils (match GAS _hashPw exactly) ──────────────────────────────

/**
 * SHA-256 iterated hash — must match GAS _hashPw(pw, salt)
 * GAS uses: salt + ':' + pw as the initial input, iterates PW_ITERATIONS times
 */
function hashPassword(pw, salt) {
  // First iteration: hash the string "salt:pw"
  let buf = crypto.createHash('sha256').update(salt + ':' + pw, 'utf8').digest();
  // Remaining iterations: hash the raw bytes
  for (let i = 1; i < PW_ITERATIONS; i++) {
    buf = crypto.createHash('sha256').update(buf).digest();
  }
  return buf.toString('base64');
}

function verifyPassword(pw, salt, storedHash) {
  if (!pw || !salt || !storedHash) return false;
  const computed = hashPassword(pw, salt);
  if (computed.length !== storedHash.length) return false;
  // Constant-time compare
  let diff = 0;
  for (let i = 0; i < computed.length; i++) {
    diff |= computed.charCodeAt(i) ^ storedHash.charCodeAt(i);
  }
  return diff === 0;
}

// ─── Read users with full auth fields ────────────────────────────────────────

let _usersAuthCache    = null;
let _usersAuthCacheAt  = 0;

async function getAllUsersWithAuth(force = false) {
  if (!force && _usersAuthCache && Date.now() - _usersAuthCacheAt < 60 * 1000) {
    return _usersAuthCache; // 1-min cache for auth lookups
  }
  const { headers, rows } = await readSheet(MAIN_SS_ID, 'Users');
  if (!headers.length) return [];
  const idx = h => headers.indexOf(h);
  _usersAuthCache = rows.map(r => ({
    email:        String(r[idx('Email')]         || '').toLowerCase().trim(),
    name:         String(r[idx('Name')]          || '').trim(),
    role:         String(r[idx('Role')]          || '').trim().toLowerCase(),
    team:         String(r[idx('Team')]          || '').trim(),
    active:       r[idx('Active')] === true || String(r[idx('Active')]).toUpperCase() === 'TRUE',
    passwordHash: String(r[idx('Password Hash')] || '').trim(),
    passwordSalt: String(r[idx('Password Salt')] || '').trim(),
    dailyMinuteLimit: Number(r[idx('Daily Minute Limit')] || 0),
  })).filter(u => u.email);
  _usersAuthCacheAt = Date.now();
  return _usersAuthCache;
}

async function findUser(email) {
  const users = await getAllUsersWithAuth();
  return users.find(u => u.email === email.toLowerCase().trim()) || null;
}

// ─── Sessions sheet helpers ───────────────────────────────────────────────────

async function _loadSessionsFromSheet() {
  try {
    const { headers, rows } = await readSheet(MAIN_SS_ID, 'Sessions');
    if (!headers.length) return;
    const ti = headers.indexOf('Token');
    const ei = headers.indexOf('Email');
    const xi = headers.indexOf('Expires At');
    if (ti < 0 || ei < 0 || xi < 0) return;
    const now = Date.now();
    rows.forEach(r => {
      const token   = String(r[ti] || '').trim();
      const email   = String(r[ei] || '').toLowerCase().trim();
      const expires = new Date(r[xi] || 0).getTime();
      if (!token || !email || expires < now) return;
      if (!_sessionCache.has(token)) {
        _sessionCache.set(token, { email, expires, role: '', team: '', name: '' });
      }
    });
  } catch (e) {
    console.warn('[auth] Could not load sessions from sheet:', e.message);
  }
}

async function _persistSession(token, email, expires) {
  try {
    await appendRows(MAIN_SS_ID, 'Sessions', [
      [token, email, new Date().toISOString(), new Date(expires).toISOString()],
    ]);
  } catch (e) {
    console.warn('[auth] Could not persist session to sheet:', e.message);
  }
}

// ─── Login ────────────────────────────────────────────────────────────────────

async function login(email, password) {
  if (!email || !password) {
    return { ok: false, error: 'EMAIL_AND_PASSWORD_REQUIRED' };
  }
  email = email.toLowerCase().trim();

  let user;
  try {
    user = await findUser(email);
  } catch (e) {
    console.error('[auth] login sheet read error:', e.message);
    return { ok: false, error: 'SERVER_ERROR', message: 'Could not read user data.' };
  }

  if (!user)             return { ok: false, error: 'INVALID_CREDENTIALS' };
  if (!user.active)      return { ok: false, error: 'ACCOUNT_INACTIVE' };
  if (!user.passwordHash) return { ok: false, error: 'PASSWORD_NOT_SET', message: 'Check your email for the setup link.' };

  const valid = verifyPassword(password, user.passwordSalt, user.passwordHash);
  if (!valid) return { ok: false, error: 'INVALID_CREDENTIALS' };

  // Create session
  const token   = crypto.randomUUID() + '-' + crypto.randomBytes(4).toString('hex');
  const expires = Date.now() + SESSION_TTL_MS;

  _sessionCache.set(token, {
    email:   user.email,
    name:    user.name,
    role:    user.role,
    team:    user.team,
    expires,
  });

  // Persist to sheet (non-blocking)
  _persistSession(token, user.email, expires).catch(() => {});

  return {
    ok: true,
    session: token,
    user: {
      email:            user.email,
      name:             user.name,
      role:             user.role,
      team:             user.team,
      active:           user.active,
      dailyMinuteLimit: user.dailyMinuteLimit,
      hasPassword:      true,
    },
  };
}

// ─── Session validation ───────────────────────────────────────────────────────

async function validateSession(token) {
  if (!token) return null;

  // Check in-memory cache first
  const cached = _sessionCache.get(token);
  if (cached) {
    if (cached.expires < Date.now()) {
      _sessionCache.delete(token);
      return null;
    }
    // If role is missing (loaded from sheet without user data), enrich it
    if (!cached.role) {
      try {
        const user = await findUser(cached.email);
        if (user) {
          cached.role = user.role;
          cached.team = user.team;
          cached.name = user.name;
        }
      } catch (_) {}
    }
    return cached;
  }

  // Not in cache — try loading from sheet (server restart case)
  try {
    await _loadSessionsFromSheet();
    const fromSheet = _sessionCache.get(token);
    if (fromSheet && fromSheet.expires >= Date.now()) {
      // Enrich with user data
      const user = await findUser(fromSheet.email);
      if (user) {
        fromSheet.role = user.role;
        fromSheet.team = user.team;
        fromSheet.name = user.name;
      }
      return fromSheet;
    }
  } catch (_) {}

  return null;
}

// ─── Logout ───────────────────────────────────────────────────────────────────

function logout(token) {
  _sessionCache.delete(token);
  // Note: sheet cleanup is handled by cleanupExpiredSessions cron in poller.js
}

// ─── Cleanup expired sessions ─────────────────────────────────────────────────

async function cleanupExpiredSessions() {
  const now = Date.now();
  // Clean memory
  for (const [tok, sess] of _sessionCache.entries()) {
    if (sess.expires < now) _sessionCache.delete(tok);
  }
  // Clean sheet — keep only non-expired rows
  try {
    const { headers, rows } = await readSheet(MAIN_SS_ID, 'Sessions');
    if (!headers.length) return;
    const xi = headers.indexOf('Expires At');
    if (xi < 0) return;
    const keep = rows.filter(r => new Date(r[xi] || 0).getTime() > now);
    // Overwrite sheet: clear data rows then rewrite
    const sheets = require('./sheets');
    await sheets.clearRange(MAIN_SS_ID, `'Sessions'!A2:Z`);
    if (keep.length) await appendRows(MAIN_SS_ID, 'Sessions', keep);
    console.log(`[auth] Session cleanup: kept ${keep.length}, removed ${rows.length - keep.length}`);
  } catch (e) {
    console.warn('[auth] Session cleanup error:', e.message);
  }
}

// ─── Exports ──────────────────────────────────────────────────────────────────

module.exports = {
  login,
  validateSession,
  logout,
  cleanupExpiredSessions,
  getAllUsersWithAuth,
  findUser,
  hashPassword,
};
