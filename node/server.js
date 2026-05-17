/**
 * server.js — Voxa Portal Node Server
 *
 * Routes:
 *   POST /                    → proxy to GAS (user-facing actions)
 *   GET  /poller/status       → health + job stats
 *   POST /poller/force-refresh → force poll (all or one agent)
 *   POST /poller/run/:job     → run any background job
 *   POST /api/archive/leads   → get archived leads from team SS
 *   POST /api/archive/mt      → get archived MT rows from team SS
 *   POST /api/archive/manual  → get archived manual entries from team SS
 */

const express  = require('express');
const cors     = require('cors');
const axios    = require('axios');
const path     = require('path');

const {
  startPoller,
  pollActiveBatches,
  backfillMissingOutputs,
  repairUnassignedLeads,
  cleanupExpiredSessions,
  dedupeAllSheets,
  archiveCompletedLeads,
  archiveCompletedMT,
  archiveManualTracker,
  processCallbackQueue,
  processRetryQueue,
  getArchivedLeads,
  getArchivedMT,
  getArchivedManual,
  getStatus,
  getAllUsers,
} = require('./poller');

const { readSheet } = require('./sheets');

const app  = express();
const PORT = process.env.PORT || 10000;
const GAS_URL        = process.env.GAS_URL;
const POLLER_TOKEN   = process.env.POLLER_TOKEN || 'voxa-bfsi-2026';
const MAIN_SS_ID     = process.env.SPREADSHEET_ID;

app.use(cors());
app.use(express.json({ limit: '10mb' }));
app.use(express.static(path.join(__dirname, 'public')));

// ─── Auth middleware ─────────────────────────────────────────────────────────

function requirePollerToken(req, res, next) {
  const auth = req.headers['authorization'] || '';
  const token = auth.replace('Bearer ', '').trim();
  if (token !== POLLER_TOKEN) {
    return res.status(401).json({ ok: false, error: 'UNAUTHORIZED' });
  }
  next();
}

/**
 * Validate a user session token against the Sessions sheet in main SS
 * Returns { ok, user } where user = { email, role, team }
 */
async function validateSession(sessionToken) {
  if (!sessionToken) return { ok: false };
  try {
    const { headers, rows } = await readSheet(MAIN_SS_ID, 'Sessions');
    if (!headers.length) return { ok: false };
    const tokenCol   = headers.indexOf('Token');
    const emailCol   = headers.indexOf('Email');
    const expiresCol = headers.indexOf('Expires At');
    for (const row of rows) {
      if (String(row[tokenCol] || '') !== sessionToken) continue;
      const expires = new Date(row[expiresCol] || 0);
      if (expires.getTime() < Date.now()) return { ok: false, error: 'SESSION_EXPIRED' };
      const email = String(row[emailCol] || '').toLowerCase().trim();
      // Get user details
      const users = await getAllUsers();
      const user = users.find(u => u.email === email);
      if (!user || !user.active) return { ok: false };
      return { ok: true, user };
    }
    return { ok: false };
  } catch (e) {
    console.error('[auth] validateSession error:', e.message);
    return { ok: false };
  }
}

// ─── Main proxy route → GAS ──────────────────────────────────────────────────

app.post('/', async (req, res) => {
  if (!GAS_URL) return res.json({ ok: false, error: 'GAS_URL not configured' });
  try {
    const response = await axios.post(GAS_URL, req.body, {
      headers: { 'Content-Type': 'application/json' },
      timeout: 30000,
    });
    res.json(response.data);
  } catch (err) {
    const msg = err.response?.data || err.message;
    console.error('[proxy] GAS error:', msg);
    res.status(500).json({ ok: false, error: String(msg).slice(0, 300) });
  }
});

// ─── Poller admin endpoints ──────────────────────────────────────────────────

app.get('/poller/status', requirePollerToken, (req, res) => {
  res.json({ ok: true, ...getStatus() });
});

app.post('/poller/force-refresh', requirePollerToken, async (req, res) => {
  const { agentCode } = req.body || {};
  try {
    await pollActiveBatches(agentCode || null);
    res.json({ ok: true, message: agentCode ? `Refreshed ${agentCode}` : 'Refreshed all agents' });
  } catch (err) {
    res.status(500).json({ ok: false, error: err.message });
  }
});

const JOB_MAP = {
  poll:        () => pollActiveBatches(),
  backfill:    () => backfillMissingOutputs(),
  repair:      () => repairUnassignedLeads(),
  sessions:    () => cleanupExpiredSessions(),
  dedupe:      () => dedupeAllSheets(),
  archLeads:   () => archiveCompletedLeads(),
  archMT:      () => archiveCompletedMT(),
  archManual:  () => archiveManualTracker(),
  callbacks:   () => processCallbackQueue(),
  retries:     () => processRetryQueue(),
};

app.post('/poller/run/:job', requirePollerToken, async (req, res) => {
  const { job } = req.params;
  const fn = JOB_MAP[job];
  if (!fn) {
    return res.status(400).json({
      ok: false,
      error: `Unknown job: ${job}`,
      available: Object.keys(JOB_MAP),
    });
  }
  try {
    const result = await fn();
    res.json({ ok: true, job, result: result || 'done' });
  } catch (err) {
    res.status(500).json({ ok: false, error: err.message });
  }
});

// ─── Archive API endpoints ───────────────────────────────────────────────────
// These read from team spreadsheets and return archived data to the portal.
// Auth: session token from the portal user.

async function archiveAuth(req, res) {
  const sessionToken = req.body?.session || req.headers['x-session'];
  const auth = await validateSession(sessionToken);
  if (!auth.ok) {
    res.status(401).json({ ok: false, error: 'UNAUTHENTICATED' });
    return null;
  }
  return auth.user;
}

function resolveTeam(user, requestedTeam) {
  if (user.role === 'super_admin') return requestedTeam || null; // null = all teams
  if (user.role === 'team_lead' || user.role === 'individual_contributor') return user.team;
  return user.team; // recruiters see their own team
}

/**
 * POST /api/archive/leads
 * Body: { session, team?, agentCode?, filter: { requestId, search } }
 * Returns archived completed leads from the team's spreadsheet
 */
app.post('/api/archive/leads', async (req, res) => {
  const user = await archiveAuth(req, res);
  if (!user) return;

  const { body } = req;
  const team = resolveTeam(user, body.team);

  try {
    let teams = [];
    if (team) {
      teams = [team];
    } else if (user.role === 'super_admin') {
      const allTeams = await (require('./poller').getAllTeams());
      teams = allTeams.map(t => t.name);
    }

    let all = [];
    for (const t of teams) {
      try {
        const rows = await getArchivedLeads(t);
        rows.forEach(r => { r._team = t; r._source = 'archive'; });
        all.push(...rows);
      } catch (e) {
        console.error(`[archive/leads] Error for team ${t}:`, e.message);
      }
    }

    // Filter by agent
    if (body.agentCode) all = all.filter(r => r['_agent'] === body.agentCode || r['Agent Code'] === body.agentCode || true); // pass through for now

    // Filter by role
    if (user.role === 'recruiter') {
      all = all.filter(r => String(r['Assigned To Email'] || '').toLowerCase() === user.email);
    }

    // Filter by search
    if (body.filter?.search) {
      const s = String(body.filter.search).toLowerCase();
      all = all.filter(r =>
        String(r['Callee Name'] || '').toLowerCase().includes(s) ||
        String(r['Mobile Number'] || '').toLowerCase().includes(s)
      );
    }

    res.json({ ok: true, leads: all, count: all.length, source: 'archive' });
  } catch (err) {
    res.status(500).json({ ok: false, error: err.message });
  }
});

/**
 * POST /api/archive/mt
 * Returns archived master tracker rows from team spreadsheet
 */
app.post('/api/archive/mt', async (req, res) => {
  const user = await archiveAuth(req, res);
  if (!user) return;

  const team = resolveTeam(user, req.body?.team);
  if (!team) return res.json({ ok: true, rows: [], count: 0 });

  try {
    const rows = await getArchivedMT(team);
    res.json({ ok: true, rows, count: rows.length, source: 'archive' });
  } catch (err) {
    res.status(500).json({ ok: false, error: err.message });
  }
});

/**
 * POST /api/archive/manual
 * Returns archived manual tracker entries from team spreadsheet
 */
app.post('/api/archive/manual', async (req, res) => {
  const user = await archiveAuth(req, res);
  if (!user) return;

  const team = resolveTeam(user, req.body?.team);
  if (!team) return res.json({ ok: true, rows: [], count: 0 });

  try {
    let rows = await getArchivedManual(team);

    // Recruiters see only their own
    if (user.role === 'recruiter') {
      rows = rows.filter(r => String(r['Added By Email'] || '').toLowerCase() === user.email);
    }

    res.json({ ok: true, rows, count: rows.length, source: 'archive' });
  } catch (err) {
    res.status(500).json({ ok: false, error: err.message });
  }
});

// ─── Health check ─────────────────────────────────────────────────────────────

app.get('/health', (req, res) => {
  res.json({ ok: true, uptime: Math.round(process.uptime()), ts: new Date().toISOString() });
});

// ─── Catch-all: serve frontend ────────────────────────────────────────────────

app.get('*', (req, res) => {
  const indexPath = path.join(__dirname, 'public', 'index.html');
  res.sendFile(indexPath, err => {
    if (err) res.status(404).send('Not found');
  });
});

// ─── Start ────────────────────────────────────────────────────────────────────

app.listen(PORT, () => {
  console.log(`Voxa running on port ${PORT}`);
  startPoller();
});
