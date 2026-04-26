const express = require('express');
const fetch = require('node-fetch');
const compression = require('compression');
const NodeCache = require('node-cache');
const path = require('path');

const app = express();
const cache = new NodeCache({ stdTTL: 30 });
const GAS_URL = process.env.GAS_URL;

app.use(compression());
app.use(express.json({ limit: '10mb' }));
app.use(express.static(path.join(__dirname, 'public')));

const CACHEABLE = ['getDashboard','getCampaigns','listAgents','listTeams','listUsers','getUsage'];
const BUST = {
  uploadContacts:1, triggercampaign:1, upsertUser:1, deleteUser:1,
  upsertTeam:1, upsertAgent:1, assignLead:1, updateLead:1
};

app.post('/api', async (req, res) => {
  const { action, session, ...rest } = req.body || {};
  if (!action) return res.json({ ok: false, error: 'NO_ACTION' });

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
    const data = await r.json();
    if (CACHEABLE.includes(action) && data.ok) cache.set(cacheKey, data);
    res.json(data);
  } catch (e) {
    res.status(502).json({ ok: false, error: 'UPSTREAM_ERROR', message: e.message });
  }
});

// All other routes → SPA
app.get('*', (_, res) => res.sendFile(path.join(__dirname, 'public', 'index.html')));

app.listen(process.env.PORT || 3000, () => console.log('Voxa running'));