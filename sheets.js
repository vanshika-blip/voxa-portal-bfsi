/**
 * sheets.js — Google Sheets API helper
 * Wraps googleapis with retry + quota-safe helpers
 */

const { google } = require('googleapis');

let _auth = null;
let _sheets = null;

function getAuth() {
  if (_auth) return _auth;
  const b64 = process.env.GOOGLE_SERVICE_ACCOUNT_B64;
  if (!b64) throw new Error('GOOGLE_SERVICE_ACCOUNT_B64 not set');
  const sa = JSON.parse(Buffer.from(b64, 'base64').toString('utf8'));
  _auth = new google.auth.GoogleAuth({
    credentials: sa,
    // Drive scope required for createSpreadsheet + shareSpreadsheet
    scopes: [
      'https://www.googleapis.com/auth/spreadsheets',
      'https://www.googleapis.com/auth/drive',
    ],
  });
  return _auth;
}

function getSheetsClient() {
  if (_sheets) return _sheets;
  _sheets = google.sheets({ version: 'v4', auth: getAuth() });
  return _sheets;
}

// Sleep helper
const sleep = (ms) => new Promise(r => setTimeout(r, ms));

// Retry wrapper — handles quota errors with exponential backoff
async function withRetry(fn, maxAttempts = 4, baseDelay = 2000) {
  for (let attempt = 1; attempt <= maxAttempts; attempt++) {
    try {
      return await fn();
    } catch (err) {
      const isQuota = err?.response?.status === 429 ||
        (err?.message || '').includes('Quota exceeded') ||
        (err?.message || '').includes('rate limit');
      const isLast = attempt === maxAttempts;
      if (!isQuota || isLast) throw err;
      const delay = baseDelay * Math.pow(2, attempt - 1);
      console.warn(`[sheets] Quota hit, retrying in ${delay}ms (attempt ${attempt}/${maxAttempts})`);
      await sleep(delay);
    }
  }
}

/**
 * Read a sheet range
 * @returns {string[][]} 2D array of values (empty array if sheet empty)
 */
async function readRange(spreadsheetId, range) {
  const sheets = getSheetsClient();
  const res = await withRetry(() => sheets.spreadsheets.values.get({
    spreadsheetId,
    range,
    valueRenderOption: 'UNFORMATTED_VALUE',
    dateTimeRenderOption: 'FORMATTED_STRING',
  }));
  return res.data.values || [];
}

/**
 * Read entire sheet (all rows, all columns)
 * Returns { headers: string[], rows: any[][] }
 */
async function readSheet(spreadsheetId, sheetName) {
  const raw = await readRange(spreadsheetId, `'${sheetName}'`);
  if (!raw.length) return { headers: [], rows: [] };
  const headers = raw[0].map(String);
  const rows = raw.slice(1);
  return { headers, rows };
}

/**
 * Read sheet and return array of objects keyed by header
 */
async function readSheetAsObjects(spreadsheetId, sheetName) {
  const { headers, rows } = await readSheet(spreadsheetId, sheetName);
  return rows.map(row => {
    const obj = {};
    headers.forEach((h, i) => { obj[h] = row[i] !== undefined ? row[i] : ''; });
    return obj;
  });
}

/**
 * Write a single row at a specific sheet row index (1-based)
 */
async function writeRow(spreadsheetId, sheetName, rowIndex, values) {
  const sheets = getSheetsClient();
  const range = `'${sheetName}'!A${rowIndex}`;
  await withRetry(() => sheets.spreadsheets.values.update({
    spreadsheetId,
    range,
    valueInputOption: 'RAW',
    requestBody: { values: [values] },
  }));
}

/**
 * Batch-write multiple rows starting at rowIndex (1-based)
 */
async function writeRows(spreadsheetId, sheetName, startRowIndex, values2D) {
  if (!values2D.length) return;
  const sheets = getSheetsClient();
  const range = `'${sheetName}'!A${startRowIndex}`;
  await withRetry(() => sheets.spreadsheets.values.update({
    spreadsheetId,
    range,
    valueInputOption: 'RAW',
    requestBody: { values: values2D },
  }));
}

/**
 * Append rows to the bottom of a sheet
 */
async function appendRows(spreadsheetId, sheetName, values2D) {
  if (!values2D.length) return;
  const sheets = getSheetsClient();
  await withRetry(() => sheets.spreadsheets.values.append({
    spreadsheetId,
    range: `'${sheetName}'!A1`,
    valueInputOption: 'RAW',
    insertDataOption: 'INSERT_ROWS',
    requestBody: { values: values2D },
  }));
}

/**
 * Clear a range
 */
async function clearRange(spreadsheetId, range) {
  const sheets = getSheetsClient();
  await withRetry(() => sheets.spreadsheets.values.clear({
    spreadsheetId,
    range,
  }));
}

/**
 * Get sheet metadata (list of sheets in a spreadsheet)
 */
async function getSheetList(spreadsheetId) {
  const sheets = getSheetsClient();
  const res = await withRetry(() => sheets.spreadsheets.get({
    spreadsheetId,
    fields: 'sheets.properties',
  }));
  return (res.data.sheets || []).map(s => ({
    id: s.properties.sheetId,
    name: s.properties.title,
    rowCount: s.properties.gridProperties?.rowCount || 0,
  }));
}

/**
 * Ensure a sheet exists in a spreadsheet (creates if missing)
 */
async function ensureSheet(spreadsheetId, sheetName, headers = [], color = null) {
  const list = await getSheetList(spreadsheetId);
  const existing = list.find(s => s.name === sheetName);

  if (!existing) {
    const sheets = getSheetsClient();
    const addReq = { addSheet: { properties: { title: sheetName } } };
    try {
      await withRetry(() => sheets.spreadsheets.batchUpdate({
        spreadsheetId,
        requestBody: { requests: [addReq] },
      }));
    } catch (err) {
      if (!(err.message || '').toLowerCase().includes('already exists')) throw err;
    }
    if (headers.length) {
      await appendRows(spreadsheetId, sheetName, [headers]);
      if (color) {
        await formatHeaderRow(spreadsheetId, sheetName, color);
      }
    }
    return;
  }

  // Sheet exists — check if headers need adding
  if (!headers.length) return;
  const { headers: existingHeaders } = await readSheet(spreadsheetId, sheetName);
  if (!existingHeaders.length) {
    await appendRows(spreadsheetId, sheetName, [headers]);
    return;
  }
  const missing = headers.filter(h => !existingHeaders.includes(h));
  if (missing.length) {
    // Append missing headers to row 1
    const startCol = existingHeaders.length + 1;
    const colLetter = colToLetter(startCol);
    const sheets = getSheetsClient();
    await withRetry(() => sheets.spreadsheets.values.update({
      spreadsheetId,
      range: `'${sheetName}'!${colLetter}1`,
      valueInputOption: 'RAW',
      requestBody: { values: [missing] },
    }));
  }
}

/**
 * Delete specific rows by index (1-based, sorted descending to preserve indices)
 * Batches deletions to avoid quota issues
 */
async function deleteRows(spreadsheetId, sheetName, rowIndices1Based) {
  if (!rowIndices1Based.length) return;
  const sheets = getSheetsClient();

  // Get sheet ID
  const list = await getSheetList(spreadsheetId);
  const sheet = list.find(s => s.name === sheetName);
  if (!sheet) throw new Error(`Sheet not found: ${sheetName}`);
  const sheetId = sheet.id;

  // Sort descending (delete from bottom up to preserve indices)
  const sorted = [...rowIndices1Based].sort((a, b) => b - a);

  // Batch into groups of 50 requests
  const BATCH = 50;
  for (let i = 0; i < sorted.length; i += BATCH) {
    const chunk = sorted.slice(i, i + BATCH);
    const requests = chunk.map(rowIdx => ({
      deleteDimension: {
        range: {
          sheetId,
          dimension: 'ROWS',
          startIndex: rowIdx - 1, // 0-based
          endIndex: rowIdx,       // exclusive
        },
      },
    }));
    await withRetry(() => sheets.spreadsheets.batchUpdate({
      spreadsheetId,
      requestBody: { requests },
    }));
    if (i + BATCH < sorted.length) await sleep(500);
  }
}

/**
 * Format header row with background color
 */
async function formatHeaderRow(spreadsheetId, sheetName, hexColor) {
  const list = await getSheetList(spreadsheetId);
  const sheet = list.find(s => s.name === sheetName);
  if (!sheet) return;
  const rgb = hexToRgb(hexColor);
  const sheets = getSheetsClient();
  await withRetry(() => sheets.spreadsheets.batchUpdate({
    spreadsheetId,
    requestBody: {
      requests: [{
        repeatCell: {
          range: { sheetId: sheet.id, startRowIndex: 0, endRowIndex: 1 },
          cell: {
            userEnteredFormat: {
              backgroundColor: rgb,
              textFormat: { foregroundColor: { red: 1, green: 1, blue: 1 }, bold: true },
            },
          },
          fields: 'userEnteredFormat(backgroundColor,textFormat)',
        },
      }],
    },
  }));
}

// Helpers
function hexToRgb(hex) {
  const r = parseInt(hex.slice(1, 3), 16) / 255;
  const g = parseInt(hex.slice(3, 5), 16) / 255;
  const b = parseInt(hex.slice(5, 7), 16) / 255;
  return { red: r, green: g, blue: b };
}

function colToLetter(col) {
  let s = '';
  while (col > 0) {
    const rem = (col - 1) % 26;
    s = String.fromCharCode(65 + rem) + s;
    col = Math.floor((col - 1) / 26);
  }
  return s;
}

/**
 * Test connection — reads first cell of spreadsheet
 */
async function testConnection(spreadsheetId) {
  const data = await readRange(spreadsheetId, 'A1');
  return true;
}

/**
 * Create a new Google Spreadsheet and return its ID.
 * Uses the service account (no Drive API needed — Sheets API create endpoint works with spreadsheets scope).
 */
async function createSpreadsheet(title) {
  const client = getSheetsClient();
  const res = await withRetry(() => client.spreadsheets.create({
    requestBody: { properties: { title } },
  }));
  return res.data.spreadsheetId;
}

/**
 * Share a spreadsheet with one or more email addresses (writer access).
 * Requires Drive scope on the service account.
 */
async function shareSpreadsheet(fileId, ...emails) {
  const auth  = getAuth();
  const drive = google.drive({ version: 'v3', auth });
  for (const email of emails.filter(Boolean)) {
    try {
      await withRetry(() => drive.permissions.create({
        fileId,
        requestBody: { role: 'writer', type: 'user', emailAddress: email },
        sendNotificationEmail: false,
      }));
    } catch (e) {
      console.warn(`[sheets] shareSpreadsheet: could not share ${fileId} with ${email}:`, e.message);
    }
  }
}

/**
 * Batch-write multiple NON-CONTIGUOUS rows in ONE API call.
 * updates = [{ rowIndex: number (1-based), values: any[] }]
 * This replaces N individual writeRow calls with 1 batchUpdate — critical for quota.
 */
async function batchWriteRows(spreadsheetId, sheetName, updates) {
  if (!updates.length) return;
  const sheets = getSheetsClient();
  const data = updates.map(u => ({
    range: `'${sheetName}'!A${u.rowIndex}`,
    values: [u.values],
  }));
  await withRetry(() => sheets.spreadsheets.values.batchUpdate({
    spreadsheetId,
    requestBody: { valueInputOption: 'RAW', data },
  }));
}

module.exports = {
  readRange,
  readSheet,
  readSheetAsObjects,
  writeRow,
  writeRows,
  appendRows,
  clearRange,
  getSheetList,
  ensureSheet,
  deleteRows,
  formatHeaderRow,
  testConnection,
  batchWriteRows,
  createSpreadsheet,
  shareSpreadsheet,
  getAuth,
  sleep,
  withRetry,
};