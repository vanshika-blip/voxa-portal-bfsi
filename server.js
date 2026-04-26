const express = require('express');
const fetch = require('node-fetch');
const compression = require('compression');
const NodeCache = require('node-cache');
const cors = require('cors');
const path = require('path');

const app = express();
const cache = new NodeCache({ stdTTL: 30 });
const GAS_URL = process.env.GAS_URL;

app.use(cors());

app.use(compression());
app.use(express.json({ limit: '10mb' }));
// The frontend sends Content-Type: text/plain;charset=utf-8 (required by GAS CORS policy).
// express.json() won't parse that, so we also accept raw text and parse it ourselves.
app.use(express.text({ type: 'text/plain', limit: '10mb' }));
app.use(express.static(path.join(__dirname, 'public')));

const CACHEABLE = ['getDashboard','getCampaigns','listAgents','listTeams','listUsers','getUsage'];
const BUST = {
  uploadContacts:1, triggercampaign:1, upsertUser:1, deleteUser:1,
  upsertTeam:1, upsertAgent:1, assignLead:1, updateLead:1
};

app.post('/api', async (req, res) => {
  // Support both application/json and text/plain (GAS CORS workaround)
  let parsed = req.body;
  if (typeof parsed === 'string') {
    try { parsed = JSON.parse(parsed); } catch (e) {
      return res.json({ ok: false, error: 'BAD_REQUEST', message: 'Invalid JSON body' });
    }
  }
  const { action, session, ...rest } = parsed || {};
  if (!action) return res.json({ ok: false, error: 'NO_ACTION' });

  if (!GAS_URL) return res.status(503).json({ ok: false, error: 'SERVER_MISCONFIGURED', message: 'GAS_URL environment variable is not set.' });

  const cacheKey = action + '|' + session + '|' + JSON.stringify(rest);

  if (CACHEABLE.includes(action)) {
    const hit = cache.get(cacheKey);
    if (hit) return res.json({ ...hit, _cached: true });
  }
  if (BUST[action]) cache.flushAll();

  try {
    const r = await fetch(GAS_URL, {
      method: 'POST',
      headers: { 'Content-Type': 'text/plain;charset=utf-8' },
      body: JSON.stringify({ action, session, ...rest }),
      timeout: 60000,
    });
    const text = await r.text();
    let data;
    try {
      data = JSON.parse(text);
    } catch (e) {
      // GAS returned HTML (e.g. login redirect, quota error, or script not deployed correctly)
      const snippet = text.slice(0, 200).replace(/\s+/g, ' ');
      return res.status(502).json({ ok: false, error: 'GAS_INVALID_RESPONSE', message: 'Google Apps Script did not return JSON. Check deployment settings and GAS_URL. Response: ' + snippet });
    }
    if (CACHEABLE.includes(action) && data.ok) cache.set(cacheKey, data);
    res.json(data);
  } catch (e) {
    res.status(502).json({ ok: false, error: 'UPSTREAM_ERROR', message: e.message });
  }
});

// All other routes → SPA
app.get('*', (_, res) => res.sendFile(path.join(__dirname, 'public', 'index.html')));

app.listen(process.env.PORT || 3000, () => console.log('Voxa running'));


// Keep-alive ping (free tier)
if (process.env.RENDER_EXTERNAL_URL) {
  setInterval(() => fetch(process.env.RENDER_EXTERNAL_URL + '/api', {
    method: 'POST', body: JSON.stringify({ action: 'ping' }),
    headers: { 'Content-Type': 'text/plain' }
  }).catch(() => {}), 14 * 60 * 1000);
}