'use strict';
const http = require('http');
const fs   = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');

// ─── Constants ────────────────────────────────────────────────────────────────
const PORT        = process.env.PORT || 3000;
const MAX_LOBBIES = 5;
const GRACE_MS    = 45000;
const MAX_LINE    = 7;

const MIME = {
  '.png':'image/png','.jpg':'image/jpeg','.webp':'image/webp',
  '.svg':'image/svg+xml','.mp4':'video/mp4','.mp3':'audio/mpeg',
  '.webmanifest':'application/manifest+json','.json':'application/json',
  '.js':'application/javascript',
};

// ─── Global State ─────────────────────────────────────────────────────────────
const lobbies  = {};
const wsState  = new WeakMap();
const sessions = {};

// ─── Lobby Init ───────────────────────────────────────────────────────────────
for (let i = 0; i < MAX_LOBBIES; i++) {
  const id = 'L' + (i + 1);
  lobbies[id] = {
    id, name: `Mesa ${i + 1}`, maxPlayers: 4,
    players: [null,null,null,null], names: ['','','',''], tokens: [null,null,null,null],
    game: null, graceTimers: [null,null,null,null], solo: false,
  };
}

// ─── Tile / Deck Definitions ──────────────────────────────────────────────────
// tile: { id, bathers, type } type: 'normal'|'surf'|'rock'
function buildDeck() {
  const tiles = [];
  let id = 1;
  for (let i = 0; i < 20; i++) tiles.push({ id: id++, bathers: 1, type: 'normal' });
  for (let i = 0; i < 15; i++) tiles.push({ id: id++, bathers: 2, type: 'normal' });
  for (let i = 0; i < 8;  i++) tiles.push({ id: id++, bathers: 3, type: 'normal' });
  for (let i = 0; i < 5;  i++) tiles.push({ id: id++, bathers: 1, type: 'surf' });
  tiles.push({ id: id++, bathers: 0, type: 'rock' });
  // shuffle
  for (let i = tiles.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [tiles[i], tiles[j]] = [tiles[j], tiles[i]];
  }
  return tiles;
}

// 8 objective cards
function buildObjectives() {
  const all = [
    { id:'obj1', desc:'Quadrado 3×3 (9 tiles)',         pts:2, type:'square3' },
    { id:'obj2', desc:'Linha de 5 tiles',               pts:4, type:'row5' },
    { id:'obj3', desc:'Linha de 7 tiles',               pts:6, type:'row7' },
    { id:'obj4', desc:'Quadrado 5×5 (25 tiles)',         pts:2, type:'square5' },
    { id:'obj5', desc:'Coluna de 5 tiles',              pts:4, type:'col5' },
    { id:'obj6', desc:'Coluna de 7 tiles',              pts:6, type:'col7' },
    { id:'obj7', desc:'2 Pranchas adjacentes',          pts:4, type:'surf2adj' },
    { id:'obj8', desc:'Excursão (2×2 tiles com 3 banhistas cada)', pts:6, type:'excursion' },
  ];
  for (let i = all.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [all[i], all[j]] = [all[j], all[i]];
  }
  return all;
}

// ─── Board Helpers ─────────────────────────────────────────────────────────────
// board stored as Map "r,c" → tile object
function boardGet(board, r, c) { return board[`${r},${c}`] || null; }
function boardSet(board, r, c, tile) { board[`${r},${c}`] = tile; }
function boardKeys(board) {
  return Object.keys(board).map(k => { const [r,c] = k.split(','); return { r:+r, c:+c }; });
}

function lineLengthAt(board, r, c, dir) {
  // count total tiles in a row (dir='h') or col (dir='v')
  const cells = boardKeys(board);
  if (dir === 'h') {
    return cells.filter(p => p.r === r).length;
  } else {
    return cells.filter(p => p.c === c).length;
  }
}

function canPlace(board, r, c) {
  if (boardGet(board, r, c)) return false;
  const occupied = boardKeys(board);
  if (occupied.length === 0) return true;
  // must be orthogonally adjacent to existing tile
  const adj = occupied.some(p =>
    (p.r === r && Math.abs(p.c - c) === 1) ||
    (p.c === c && Math.abs(p.r - r) === 1)
  );
  if (!adj) return false;
  // check line limits
  const rowCount = occupied.filter(p => p.r === r).length;
  const colCount = occupied.filter(p => p.c === c).length;
  if (rowCount >= MAX_LINE || colCount >= MAX_LINE) return false;
  return true;
}

// Get sorted extent of tiles in a row/col
function getLine(board, r, c, dir) {
  const cells = boardKeys(board);
  if (dir === 'h') {
    return cells.filter(p => p.r === r).sort((a,b) => a.c - b.c);
  } else {
    return cells.filter(p => p.c === c).sort((a,b) => a.r - b.r);
  }
}

// Check if line is contiguous (no gaps)
function isContiguous(sorted, dir) {
  for (let i = 1; i < sorted.length; i++) {
    const key = dir === 'h' ? 'c' : 'r';
    if (sorted[i][key] - sorted[i-1][key] !== 1) return false;
  }
  return true;
}

// Count bathers for a lifeguard (respecting rocks as blockers)
function countBathersForGuard(board, r, c, dir) {
  const line = getLine(board, r, c, dir);
  if (!isContiguous(line, dir)) {
    // not contiguous — segment only (from tile outward until gap)
    // find segment containing (r,c)
    return countSegment(board, r, c, dir);
  }
  return sumBathers(board, line, r, c, dir);
}

function countSegment(board, r, c, dir) {
  // walk left/up and right/down from (r,c), stop at gap or boundary
  let total = 0;
  const key = dir === 'h' ? 'c' : 'r';
  const fixed = dir === 'h' ? r : c;
  const pos = dir === 'h' ? c : r;
  // go negative
  let i = pos - 1;
  while (true) {
    const tile = dir === 'h' ? boardGet(board, fixed, i) : boardGet(board, i, fixed);
    if (!tile) break;
    if (tile.type === 'rock') break;
    total += tile.bathers;
    i--;
  }
  // self
  const self = boardGet(board, r, c);
  if (self && self.type !== 'rock') total += self.bathers;
  // go positive
  i = pos + 1;
  while (true) {
    const tile = dir === 'h' ? boardGet(board, fixed, i) : boardGet(board, i, fixed);
    if (!tile) break;
    if (tile.type === 'rock') break;
    total += tile.bathers;
    i++;
  }
  return total;
}

function sumBathers(board, line, guardR, guardC, dir) {
  // Find which segment (between rocks) the guard is in
  let total = 0;
  const fixed = dir === 'h' ? guardR : guardC;
  const guardPos = dir === 'h' ? guardC : guardR;
  const key = dir === 'h' ? 'c' : 'r';
  // find segment boundaries
  let segStart = 0, segEnd = line.length - 1;
  for (let i = 0; i < line.length; i++) {
    const pos = line[i][key];
    const tile = boardGet(board, dir === 'h' ? fixed : pos, dir === 'h' ? pos : fixed);
    if (tile && tile.type === 'rock' && pos < guardPos) segStart = i + 1;
    if (tile && tile.type === 'rock' && pos > guardPos) { segEnd = i - 1; break; }
  }
  const segment = line.slice(segStart, segEnd + 1);
  // count surf multipliers
  let multiplier = 1;
  for (const p of segment) {
    const tile = boardGet(board, dir === 'h' ? fixed : p[key], dir === 'h' ? p[key] : fixed);
    if (tile && tile.type === 'surf') multiplier *= 2;
  }
  for (const p of segment) {
    const tile = boardGet(board, dir === 'h' ? fixed : p[key], dir === 'h' ? p[key] : fixed);
    if (tile) total += tile.bathers;
  }
  return total * multiplier;
}

// ─── Objective Checking ────────────────────────────────────────────────────────
function checkObjective(obj, board, lastR, lastC) {
  const cells = boardKeys(board);
  switch(obj.type) {
    case 'square3': return hasSquare(board, cells, 3);
    case 'square5': return hasSquare(board, cells, 5);
    case 'row5':    return hasRow(board, lastR, 5, 'h');
    case 'row7':    return hasRow(board, lastR, 7, 'h');
    case 'col5':    return hasRow(board, lastC, 5, 'v');
    case 'col7':    return hasRow(board, lastC, 7, 'v');
    case 'surf2adj': return hasSurf2Adj(board);
    case 'excursion': return hasExcursion(board, cells);
  }
  return false;
}

function hasRow(board, fixed, len, dir) {
  const cells = boardKeys(board);
  const matching = dir === 'h'
    ? cells.filter(p => p.r === fixed).sort((a,b) => a.c - b.c)
    : cells.filter(p => p.c === fixed).sort((a,b) => a.r - b.r);
  if (matching.length < len) return false;
  // check for contiguous run of len
  const key = dir === 'h' ? 'c' : 'r';
  for (let i = 0; i <= matching.length - len; i++) {
    let ok = true;
    for (let j = 1; j < len; j++) {
      if (matching[i+j][key] - matching[i+j-1][key] !== 1) { ok = false; break; }
    }
    if (ok) return true;
  }
  return false;
}

function hasSquare(board, cells, size) {
  const rows = [...new Set(cells.map(p => p.r))];
  const cols = [...new Set(cells.map(p => p.c))];
  for (const r of rows) {
    for (const c of cols) {
      let ok = true;
      outer: for (let dr = 0; dr < size; dr++) {
        for (let dc = 0; dc < size; dc++) {
          if (!boardGet(board, r+dr, c+dc)) { ok = false; break outer; }
        }
      }
      if (ok) return true;
    }
  }
  return false;
}

function hasSurf2Adj(board) {
  const cells = boardKeys(board);
  const surfCells = cells.filter(p => {
    const t = boardGet(board, p.r, p.c);
    return t && t.type === 'surf';
  });
  for (const s of surfCells) {
    const adj = [{r:s.r-1,c:s.c},{r:s.r+1,c:s.c},{r:s.r,c:s.c-1},{r:s.r,c:s.c+1}];
    for (const a of adj) {
      const t = boardGet(board, a.r, a.c);
      if (t && t.type === 'surf') return true;
    }
  }
  return false;
}

function hasExcursion(board, cells) {
  for (const p of cells) {
    const positions = [{r:p.r,c:p.c},{r:p.r,c:p.c+1},{r:p.r+1,c:p.c},{r:p.r+1,c:p.c+1}];
    if (positions.every(pos => {
      const t = boardGet(board, pos.r, pos.c);
      return t && t.bathers === 3;
    })) return true;
  }
  return false;
}

// ─── Game Logic ────────────────────────────────────────────────────────────────
function newGame(names, isSolo) {
  const deck = buildDeck();
  const allObjs = buildObjectives();
  const revealed = allObjs.slice(0, 4);
  const remaining = allObjs.slice(4);

  const board = {};
  boardSet(board, 0, 0, { id: 0, bathers: 1, type: 'normal' }); // starting tile

  return {
    players: names.map(name => ({ name, pts: 0, guards: [], fichas: 8, objPts: 0 })),
    n: names.length,
    deck,
    board,
    guards: [],      // [{r,c,dir,playerIdx,id}]
    guardIdSeq: 1,
    revealedObjs: revealed,
    remainingObjs: remaining,
    claimedObjs: [],
    phase: 'PLACE_TILE',   // PLACE_TILE | EXTRA_TURNS | GAME_OVER
    currentPlayer: 0,
    drawnTile: null,
    extraTurns: null,      // { remaining: [...playerIdx], initiator: idx } when fichas depleted
    turnGen: 0,
    isSolo,
    lastAction: null,
  };
}

function computeFinalScores(g) {
  // For each guard, count bathers in their line/col segment
  for (const guard of g.guards) {
    const score = countBathersForGuard(g.board, guard.r, guard.c, guard.dir);
    g.players[guard.playerIdx].pts += score;
  }
  // Bonus fichas remaining (+2 each)
  for (const p of g.players) {
    p.pts += p.fichas * 2;
    p.pts += p.objPts;
  }
}

function drawTile(g) {
  if (g.deck.length === 0) return null;
  return g.deck.shift();
}

function getValidPlacements(board) {
  const cells = boardKeys(board);
  const candidates = new Set();
  for (const p of cells) {
    const neighbors = [{r:p.r-1,c:p.c},{r:p.r+1,c:p.c},{r:p.r,c:p.c-1},{r:p.r,c:p.c+1}];
    for (const n of neighbors) {
      candidates.add(`${n.r},${n.c}`);
    }
  }
  const result = [];
  for (const key of candidates) {
    const [r,c] = key.split(',').map(Number);
    if (canPlace(board, r, c)) result.push({r,c});
  }
  return result;
}

// ─── Build View ────────────────────────────────────────────────────────────────
function buildView(g, seat) {
  const boardArr = Object.entries(g.board).map(([key, tile]) => {
    const [r,c] = key.split(',').map(Number);
    return { r, c, ...tile };
  });
  const validPlacements = g.phase === 'PLACE_TILE' && g.currentPlayer === seat && g.drawnTile
    ? getValidPlacements(g.board) : [];

  return {
    mySeat: seat,
    players: g.players.map(p => ({ name: p.name, pts: 0, fichas: p.fichas, objPts: p.objPts })),
    n: g.n,
    board: boardArr,
    guards: g.guards,
    phase: g.phase,
    currentPlayer: g.currentPlayer,
    drawnTile: g.currentPlayer === seat && g.drawnTile ? g.drawnTile : (g.drawnTile ? { hidden: true } : null),
    deckSize: g.deck.length,
    revealedObjs: g.revealedObjs,
    claimedObjs: g.claimedObjs,
    validPlacements,
    lastAction: g.lastAction,
    myFichas: g.players[seat].fichas,
  };
}

// ─── Helpers ──────────────────────────────────────────────────────────────────
function sendTo(ws, obj) {
  if (ws && ws.readyState === 1) ws.send(JSON.stringify(obj));
}

function findGameSeat(lobby, lobbySeat) {
  return lobbySeat; // 1:1 in this game (players keep their seat)
}

function lobbyInfo(lobby) {
  return {
    id: lobby.id, name: lobby.name, maxPlayers: lobby.maxPlayers,
    players: lobby.names.filter(Boolean).length,
    inGame: !!lobby.game,
  };
}

function broadcastGame(lobby) {
  const g = lobby.game;
  if (!g) return;
  lobby.players.forEach((ws, seat) => {
    if (ws) sendTo(ws, { type: 'GAME_STATE', state: buildView(g, seat) });
  });
}

function broadcastLobby(lobby) {
  const state = { names: lobby.names, maxPlayers: lobby.maxPlayers };
  lobby.players.forEach((ws, seat) => {
    if (ws) sendTo(ws, { type: 'LOBBY_STATE', lobby: state, myLobbySeat: seat });
  });
  broadcastLobbyList();
}

function broadcastLobbyList() {
  const list = Object.values(lobbies).map(lobbyInfo);
  for (const ws of wss.clients) {
    const st = wsState.get(ws);
    if (!st || !st.lobbyId)
      sendTo(ws, { type: 'LOBBIES', lobbies: list });
  }
}

function startGame(lobby) {
  const activePlayers = lobby.names.filter(Boolean);
  if (activePlayers.length < 2) return;
  lobby.game = newGame(activePlayers, lobby.solo);
  // draw first tile for first player
  lobby.game.drawnTile = drawTile(lobby.game);
  broadcastGame(lobby);
}

function advanceTurn(lobby) {
  const g = lobby.game;
  // draw tile for next player
  g.drawnTile = drawTile(g);
  if (!g.drawnTile) {
    // deck exhausted
    endGame(lobby);
    return;
  }
  // next player
  do {
    g.currentPlayer = (g.currentPlayer + 1) % g.n;
  } while (false);
  broadcastGame(lobby);
}

function endGame(lobby) {
  const g = lobby.game;
  g.phase = 'GAME_OVER';
  computeFinalScores(g);
  broadcastGame(lobby);
}

function hardLeaveBySlot(lobby, seat) {
  lobby.players[seat] = null;
  lobby.names[seat] = '';
  lobby.tokens[seat] = null;
  delete sessions[lobby.tokens?.[seat]];
  broadcastLobby(lobby);
  broadcastLobbyList();
}

// ─── Action Handler ────────────────────────────────────────────────────────────
function handleAction(ws, msg) {
  if (msg.type === 'PING')      { sendTo(ws, { type: 'PONG' }); return; }
  if (msg.type === 'LOBBIES')   { sendTo(ws, { type: 'LOBBIES', lobbies: Object.values(lobbies).map(lobbyInfo) }); return; }
  if (msg.type === 'RECONNECT') { handleReconnect(ws, msg); return; }
  if (msg.type === 'JOIN_LOBBY'){ handleJoin(ws, msg); return; }
  if (msg.type === 'LEAVE_LOBBY'){ handleLeave(ws); return; }

  const st = wsState.get(ws); if (!st || !st.lobbyId) return;
  const lobby = lobbies[st.lobbyId]; if (!lobby) return;
  const seat = st.seat;
  const g = lobby.game;

  switch(msg.type) {
    case 'START': {
      if (g) return;
      const seated = lobby.names.filter(Boolean).length;
      if (seated < 2) { sendTo(ws, { type: 'ERROR', text: 'Mínimo 2 jogadores' }); return; }
      startGame(lobby);
      break;
    }
    case 'REQUEST_STATE': {
      if (g) sendTo(ws, { type: 'GAME_STATE', state: buildView(g, seat) });
      else   sendTo(ws, { type: 'LOBBY_STATE', lobby: { names: lobby.names, maxPlayers: lobby.maxPlayers }, myLobbySeat: seat });
      break;
    }
    case 'PLACE_TILE': {
      if (!g || g.phase === 'GAME_OVER') return;
      if (g.currentPlayer !== seat) { sendTo(ws, { type: 'GAME_STATE', state: buildView(g, seat) }); return; }
      if (!g.drawnTile) return;
      const { r, c } = msg;
      if (!canPlace(g.board, r, c)) {
        sendTo(ws, { type: 'ERROR', text: 'Posição inválida' });
        sendTo(ws, { type: 'GAME_STATE', state: buildView(g, seat) });
        return;
      }
      // Place tile
      boardSet(g.board, r, c, g.drawnTile);
      const placedTile = g.drawnTile;
      g.drawnTile = null;
      g.lastAction = { type: 'PLACE', r, c, tile: placedTile, playerIdx: seat };

      // Check objectives
      const claimedNow = [];
      for (const obj of [...g.revealedObjs]) {
        if (checkObjective(obj, g.board, r, c)) {
          // claim it
          g.revealedObjs = g.revealedObjs.filter(o => o.id !== obj.id);
          obj.claimedBy = seat;
          obj.claimedByName = g.players[seat].name;
          g.claimedObjs.push(obj);
          g.players[seat].objPts += obj.pts;
          // reveal new one
          if (g.remainingObjs.length > 0) {
            g.revealedObjs.push(g.remainingObjs.shift());
          }
          claimedNow.push(obj);
        }
      }

      // Move to guard decision phase (handled client-side, we await PLACE_GUARD or SKIP_GUARD)
      g.phase = 'PLACE_GUARD';
      g.pendingPlacement = { r, c };
      broadcastGame(lobby);
      break;
    }
    case 'PLACE_GUARD': {
      if (!g || g.phase !== 'PLACE_GUARD') return;
      if (g.currentPlayer !== seat) return;
      const { dir } = msg; // 'h' or 'v'
      const { r, c } = g.pendingPlacement;
      const tile = boardGet(g.board, r, c);
      if (tile && tile.type === 'rock') {
        sendTo(ws, { type: 'ERROR', text: 'Não podes colocar salva-vidas em rochas' });
        return;
      }
      if (g.players[seat].fichas <= 0) {
        sendTo(ws, { type: 'ERROR', text: 'Sem fichas' });
        return;
      }
      g.players[seat].fichas--;
      const guardId = g.guardIdSeq++;
      g.guards.push({ r, c, dir, playerIdx: seat, id: guardId });
      g.lastAction = { type: 'GUARD', r, c, dir, playerIdx: seat };

      // check if this player ran out of fichas
      if (g.players[seat].fichas === 0) {
        handleFichasEmpty(lobby, seat);
        return;
      }

      nextTurn(lobby);
      break;
    }
    case 'SKIP_GUARD': {
      if (!g || g.phase !== 'PLACE_GUARD') return;
      if (g.currentPlayer !== seat) return;
      g.lastAction = { type: 'SKIP', playerIdx: seat };
      nextTurn(lobby);
      break;
    }
    case 'RESTART': {
      if (!g || g.phase !== 'GAME_OVER') return;
      lobby.game = null;
      broadcastLobby(lobby);
      break;
    }
  }
}

function handleFichasEmpty(lobby, seat) {
  const g = lobby.game;
  // player ran out of fichas — others get 1 extra turn
  const others = [];
  for (let i = 1; i < g.n; i++) {
    others.push((seat + i) % g.n);
  }
  g.extraTurns = { remaining: others, initiator: seat };
  g.phase = 'EXTRA_TURNS';
  // start first extra turn
  doNextExtraTurn(lobby);
}

function doNextExtraTurn(lobby) {
  const g = lobby.game;
  if (!g.extraTurns || g.extraTurns.remaining.length === 0) {
    endGame(lobby);
    return;
  }
  const nextP = g.extraTurns.remaining.shift();
  g.currentPlayer = nextP;
  g.phase = 'PLACE_TILE_EXTRA';
  g.drawnTile = drawTile(g);
  if (!g.drawnTile) {
    endGame(lobby);
    return;
  }
  broadcastGame(lobby);
}

function nextTurn(lobby) {
  const g = lobby.game;
  if (g.phase === 'EXTRA_TURNS' || g.phase === 'PLACE_TILE_EXTRA') {
    g.phase = 'EXTRA_TURNS';
    doNextExtraTurn(lobby);
    return;
  }
  g.currentPlayer = (g.currentPlayer + 1) % g.n;
  g.phase = 'PLACE_TILE';
  g.drawnTile = drawTile(g);
  g.pendingPlacement = null;
  if (!g.drawnTile) {
    endGame(lobby);
    return;
  }
  broadcastGame(lobby);
}

function handleJoin(ws, msg) {
  const { lobbyId, playerName } = msg;
  const name = (playerName || '').trim().slice(0, 20);
  if (!name) { sendTo(ws, { type: 'ERROR', text: 'Nome inválido' }); return; }
  const lobby = lobbies[lobbyId];
  if (!lobby) { sendTo(ws, { type: 'ERROR', text: 'Mesa não encontrada' }); return; }
  if (lobby.game) { sendTo(ws, { type: 'ERROR', text: 'Jogo já em curso' }); return; }

  const seat = lobby.players.findIndex(p => p === null);
  if (seat === -1) { sendTo(ws, { type: 'ERROR', text: 'Mesa cheia' }); return; }

  const token = Math.random().toString(36).slice(2) + Date.now().toString(36);
  lobby.players[seat] = ws;
  lobby.names[seat] = name;
  lobby.tokens[seat] = token;
  sessions[token] = { lobbyId, seat, name };
  wsState.set(ws, { lobbyId, seat, token });

  sendTo(ws, { type: 'JOINED', seat, token, lobbyId, solo: lobby.solo });
  broadcastLobby(lobby);
}

function handleLeave(ws) {
  const st = wsState.get(ws);
  if (!st || !st.lobbyId) return;
  const lobby = lobbies[st.lobbyId];
  if (!lobby) return;
  const { seat, token } = st;
  clearTimeout(lobby.graceTimers[seat]);
  lobby.players[seat] = null;
  lobby.names[seat] = '';
  lobby.tokens[seat] = null;
  delete sessions[token];
  wsState.delete(ws);
  broadcastLobby(lobby);
}

function handleReconnect(ws, msg) {
  const sess = sessions[msg.token];
  if (!sess) { sendTo(ws, { type: 'RECONNECT_FAIL' }); return; }
  const lobby = lobbies[sess.lobbyId];
  if (!lobby) { sendTo(ws, { type: 'RECONNECT_FAIL' }); return; }
  const { seat, name } = sess;
  const existing = lobby.players[seat];
  if (existing && existing !== ws && existing.readyState === 1) {
    sendTo(ws, { type: 'RECONNECT_FAIL' }); return;
  }
  clearTimeout(lobby.graceTimers[seat]);
  lobby.players[seat] = ws;
  lobby.names[seat] = name;
  wsState.set(ws, { lobbyId: sess.lobbyId, seat, token: msg.token });
  sendTo(ws, { type: 'RECONNECTED', seat, name, solo: lobby.solo });
  if (lobby.game) broadcastGame(lobby);
  else broadcastLobby(lobby);
  // notify others
  lobby.players.forEach((p, i) => {
    if (p && i !== seat) sendTo(p, { type: 'OPPONENT_RECONNECTED', seat, name });
  });
}

// ─── HTTP + WebSocket Server ──────────────────────────────────────────────────
function serveStatic(req, res) {
  const safe = path.normalize(req.url).replace(/^(\.\.[\\/])+/, '');
  const file = path.join(__dirname, 'public', safe.replace(/^\//, ''));
  const ext  = path.extname(file).toLowerCase();
  const mime = MIME[ext];
  if (!mime) { res.writeHead(404); res.end(); return; }
  fs.readFile(file, (err, data) => {
    if (err) { res.writeHead(404); res.end(); return; }
    res.writeHead(200, { 'Content-Type': mime, 'Cache-Control': 'public,max-age=86400' });
    res.end(data);
  });
}

const MANIFEST = `{
  "name": "Na Praia das Percebes",
  "short_name": "Percebes",
  "start_url": "/",
  "display": "standalone",
  "background_color": "#0077b6",
  "theme_color": "#00b4d8",
  "icons": []
}`;
const SW = `self.addEventListener('fetch', e => {});`;

// ─── CLIENT HTML ──────────────────────────────────────────────────────────────
const CLIENT_HTML = `<!DOCTYPE html>
<html lang="pt">
<head>
<meta charset="UTF-8"/>
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1"/>
<meta name="theme-color" content="#00b4d8"/>
<meta name="apple-mobile-web-app-capable" content="yes"/>
<link rel="manifest" href="/manifest.webmanifest"/>
<title>🏖 Na Praia das Percebes</title>
<style>
  :root{
    --sand:#f5deb3;--sand2:#e8c97a;--sea:#0096c7;--sea2:#00b4d8;--deep:#023e8a;
    --surf:#ff6b6b;--rock:#6b6b6b;--white:#fff;--dark:#1a1a2e;
    --p0:#e63946;--p1:#457b9d;--p2:#2a9d8f;--p3:#e9c46a;
  }
  *{box-sizing:border-box;margin:0;padding:0;font-family:'Segoe UI',sans-serif;}
  body{background:linear-gradient(160deg,#caf0f8 0%,#90e0ef 40%,var(--sand) 100%);min-height:100vh;overflow-x:hidden;}
  .screen{display:none;min-height:100vh;padding:16px;}
  .screen.active{display:flex;flex-direction:column;align-items:center;}

  /* ── Name Screen ── */
  #screen-name{justify-content:center;gap:20px;text-align:center;}
  .logo{font-size:3rem;filter:drop-shadow(2px 4px 8px rgba(0,0,0,.2));}
  .title{font-size:2rem;font-weight:900;color:var(--deep);text-shadow:2px 2px 4px rgba(0,0,0,.15);}
  .subtitle{font-size:1rem;color:#555;margin-top:-10px;}
  .inp-wrap{display:flex;gap:8px;width:100%;max-width:360px;}
  input{flex:1;padding:12px 16px;border:2px solid var(--sea2);border-radius:12px;font-size:1rem;outline:none;background:#ffffffe0;}
  input:focus{border-color:var(--deep);}
  .btn{padding:12px 20px;border:none;border-radius:12px;font-size:1rem;font-weight:700;cursor:pointer;transition:transform .1s,box-shadow .1s;}
  .btn:active{transform:scale(.96);}
  .btn-primary{background:linear-gradient(135deg,var(--sea),var(--deep));color:#fff;box-shadow:0 4px 12px rgba(0,80,160,.3);}
  .btn-secondary{background:var(--sand);color:var(--dark);border:2px solid var(--sand2);}
  .btn-danger{background:#e63946;color:#fff;}
  .btn-sm{padding:8px 14px;font-size:.85rem;}

  /* ── Lobby Screen ── */
  #screen-lobby{gap:16px;max-width:500px;margin:0 auto;width:100%;}
  .lobby-header{text-align:center;}
  .lobby-header h2{font-size:1.5rem;color:var(--deep);}
  .table-list{width:100%;display:flex;flex-direction:column;gap:10px;}
  .table-card{background:#ffffffd0;border-radius:16px;padding:14px 16px;display:flex;align-items:center;justify-content:space-between;box-shadow:0 2px 10px rgba(0,0,0,.1);}
  .table-info h3{font-size:1rem;color:var(--dark);}
  .table-info p{font-size:.8rem;color:#666;}
  .table-badge{font-size:.75rem;padding:4px 8px;border-radius:8px;font-weight:700;}
  .badge-open{background:#d8f3dc;color:#1b4332;}
  .badge-full{background:#ffd6d6;color:#c1121f;}
  .badge-game{background:#ffd6a5;color:#774900;}

  /* ── Waiting Room ── */
  #screen-waiting{gap:16px;max-width:400px;margin:0 auto;width:100%;text-align:center;}
  .waiting-players{width:100%;display:flex;flex-direction:column;gap:8px;}
  .player-slot{background:#ffffffc0;border-radius:12px;padding:10px 14px;display:flex;align-items:center;gap:10px;}
  .player-slot .dot{width:12px;height:12px;border-radius:50%;background:#ccc;}
  .dot.filled{background:var(--sea2);}
  .dot.me{background:#2dc653;}

  /* ── Game Screen ── */
  #screen-game{padding:0;gap:0;max-width:100%;align-items:stretch;}
  .game-topbar{background:var(--deep);color:#fff;padding:8px 16px;display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:6px;}
  .topbar-players{display:flex;gap:10px;flex-wrap:wrap;}
  .tp{padding:4px 10px;border-radius:20px;font-size:.8rem;font-weight:700;background:#ffffff20;}
  .tp.active{background:#ffffff40;border:2px solid #ffd166;}
  .tp.me{border:2px solid #06d6a0;}
  .game-status{font-size:.85rem;color:#caf0f8;max-width:220px;text-align:right;}

  /* ── Board ── */
  .game-main{display:flex;flex-direction:column;align-items:center;flex:1;padding:12px;gap:12px;}
  .board-wrap{position:relative;overflow:auto;max-width:100%;max-height:60vh;}
  .board-grid{position:relative;display:inline-block;}
  .board-canvas{position:relative;}
  .tile{position:absolute;width:56px;height:56px;border-radius:8px;display:flex;flex-direction:column;align-items:center;justify-content:center;font-size:1.1rem;border:2px solid #ccc;cursor:pointer;transition:transform .1s,border-color .15s;user-select:none;}
  .tile:hover{transform:scale(1.06);}
  .tile.normal{background:linear-gradient(135deg,var(--sand),var(--sand2));}
  .tile.surf{background:linear-gradient(135deg,#ff9f1c,#ffbf69);}
  .tile.rock{background:linear-gradient(135deg,#8d8d8d,#555);color:#fff;}
  .tile.start-tile{border:2px solid var(--deep);}
  .tile .bathers{font-size:.65rem;color:#555;margin-top:2px;}
  .tile .guard-marker{position:absolute;top:2px;right:2px;font-size:.7rem;}
  .valid-cell{position:absolute;width:56px;height:56px;border-radius:8px;border:3px dashed var(--sea);background:rgba(0,180,216,.15);cursor:pointer;transition:background .15s;display:flex;align-items:center;justify-content:center;font-size:1.4rem;}
  .valid-cell:hover{background:rgba(0,180,216,.35);}

  /* ── Panel ── */
  .game-panel{background:#ffffffd0;border-radius:16px;padding:12px 16px;width:100%;max-width:500px;}
  .panel-row{display:flex;align-items:center;justify-content:space-between;gap:10px;flex-wrap:wrap;}
  .drawn-tile-wrap{display:flex;align-items:center;gap:10px;}
  .drawn-tile{width:60px;height:60px;border-radius:10px;display:flex;flex-direction:column;align-items:center;justify-content:center;font-size:1.4rem;border:3px solid var(--deep);}
  .guard-btns{display:flex;gap:6px;flex-wrap:wrap;}
  .fichas-count{font-size:.85rem;color:#555;}

  /* ── Objectives ── */
  .obj-list{display:flex;flex-wrap:wrap;gap:6px;margin-top:8px;}
  .obj-card{background:var(--sand);border-radius:8px;padding:6px 10px;font-size:.75rem;display:flex;gap:6px;align-items:center;}
  .obj-card.claimed{background:#d8f3dc;text-decoration:line-through;color:#555;}
  .obj-pts{font-weight:800;color:var(--deep);}

  /* ── End Screen ── */
  #screen-end{justify-content:center;gap:16px;text-align:center;max-width:420px;margin:0 auto;}
  .score-table{width:100%;border-collapse:collapse;border-radius:12px;overflow:hidden;box-shadow:0 2px 12px rgba(0,0,0,.1);}
  .score-table th{background:var(--deep);color:#fff;padding:10px;}
  .score-table td{padding:10px;text-align:center;border-bottom:1px solid #eee;background:#fff;}
  .score-table tr:last-child td{border-bottom:none;}
  .score-table tr.winner td{background:#d8f3dc;font-weight:700;}
  .winner-banner{font-size:1.8rem;font-weight:900;color:var(--deep);}
  .notif{position:fixed;top:20px;left:50%;transform:translateX(-50%);background:var(--dark);color:#fff;padding:12px 24px;border-radius:12px;font-size:.9rem;z-index:999;pointer-events:none;opacity:0;transition:opacity .3s;max-width:90vw;text-align:center;}
  .notif.show{opacity:1;}
  @media(min-width:700px){
    .game-main{flex-direction:row;align-items:flex-start;}
    .board-wrap{max-height:80vh;}
    .game-panel{max-width:260px;}
  }
</style>
</head>
<body>

<!-- Name Screen -->
<div id="screen-name" class="screen active">
  <div class="logo">🏖</div>
  <div class="title">Na Praia das Percebes</div>
  <div class="subtitle">Jogo de colocação de tiles para 2–4 jogadores</div>
  <div class="inp-wrap">
    <input id="inp-name" placeholder="O teu nome..." maxlength="20" autocomplete="off"/>
    <button class="btn btn-primary" id="btn-go">Entrar</button>
  </div>
</div>

<!-- Lobby Screen -->
<div id="screen-lobby" class="screen">
  <div class="lobby-header"><h2>🌊 Escolhe uma mesa</h2></div>
  <div class="table-list" id="lobby-list"></div>
</div>

<!-- Waiting Screen -->
<div id="screen-waiting" class="screen">
  <h2 style="color:var(--deep)">🏖 Sala de Espera</h2>
  <p id="waiting-table-name" style="color:#555;font-size:.9rem"></p>
  <div class="waiting-players" id="waiting-players"></div>
  <button class="btn btn-primary" id="btn-start" style="width:100%">▶ Iniciar Jogo</button>
  <button class="btn btn-secondary btn-sm" id="btn-leave">Sair da Mesa</button>
</div>

<!-- Game Screen -->
<div id="screen-game" class="screen">
  <div class="game-topbar">
    <div class="topbar-players" id="tp-players"></div>
    <div class="game-status" id="game-status">A aguardar...</div>
  </div>
  <div class="game-main">
    <div class="board-wrap">
      <div class="board-canvas" id="board-canvas"></div>
    </div>
    <div class="game-panel">
      <div id="drawn-section">
        <div style="font-weight:700;margin-bottom:8px;color:var(--dark)">🃏 Tile Retirado</div>
        <div class="panel-row">
          <div class="drawn-tile-wrap">
            <div class="drawn-tile" id="drawn-tile-display">?</div>
            <div>
              <div id="drawn-tile-desc" style="font-size:.8rem;color:#555"></div>
              <div class="fichas-count">🛟 Fichas: <b id="my-fichas">8</b></div>
            </div>
          </div>
        </div>
        <div id="guard-section" style="margin-top:10px;display:none;">
          <div style="font-size:.85rem;color:#555;margin-bottom:6px">Colocar salva-vidas?</div>
          <div class="guard-btns">
            <button class="btn btn-primary btn-sm" id="btn-guard-h">↔ Horizontal</button>
            <button class="btn btn-primary btn-sm" id="btn-guard-v">↕ Vertical</button>
            <button class="btn btn-secondary btn-sm" id="btn-guard-skip">✗ Não</button>
          </div>
        </div>
        <div id="waiting-turn" style="display:none;margin-top:10px;font-size:.85rem;color:#888;text-align:center;">
          ⏳ Vez de outro jogador...
        </div>
      </div>
      <hr style="margin:12px 0;border:none;border-top:1px solid #ddd;"/>
      <div style="font-weight:700;color:var(--dark);margin-bottom:6px">🎯 Objetivos</div>
      <div class="obj-list" id="obj-list"></div>
    </div>
  </div>
</div>

<!-- End Screen -->
<div id="screen-end" class="screen">
  <div class="logo">🏆</div>
  <div class="winner-banner" id="end-winner"></div>
  <table class="score-table" id="score-table"></table>
  <button class="btn btn-primary" id="btn-restart" style="width:100%">↺ Nova Partida</button>
</div>

<div class="notif" id="notif"></div>

<script>
// ── State ──────────────────────────────────────────────────────────────────────
let ws, myName='', myToken='', myLobbySeat=-1, myGameSeat=-1;
let currentLobbyId='', inGame=false;
let lastState=null, pendingGuard=null;
let _cachedLobbies=[];

// ── WebSocket ──────────────────────────────────────────────────────────────────
function connect() {
  const proto = location.protocol==='https:' ? 'wss' : 'ws';
  ws = new WebSocket(proto+'://'+location.host);
  ws.onopen = () => {
    myToken = sessionStorage.getItem('pp_token') || '';
    if (myToken) ws.send(JSON.stringify({type:'RECONNECT',token:myToken}));
    else ws.send(JSON.stringify({type:'LOBBIES'}));
    startPing();
  };
  ws.onmessage = e => handleMsg(JSON.parse(e.data));
  ws.onclose = () => setTimeout(connect, 2000);
  ws.onerror = () => ws.close();
}
function send(obj) { if(ws&&ws.readyState===1) ws.send(JSON.stringify(obj)); }
function startPing() { setInterval(()=>send({type:'PING'}), 15000); }

// ── Message Handler ────────────────────────────────────────────────────────────
function handleMsg(msg) {
  switch(msg.type) {
    case 'PONG': break;
    case 'LOBBIES':
      _cachedLobbies = msg.lobbies;
      renderLobbyList(msg.lobbies);
      break;
    case 'JOINED':
      myLobbySeat = msg.seat;
      myToken = msg.token;
      currentLobbyId = msg.lobbyId;
      sessionStorage.setItem('pp_token', myToken);
      showScreen('screen-waiting');
      break;
    case 'LOBBY_STATE':
      myLobbySeat = msg.myLobbySeat;
      renderWaiting(msg.lobby);
      break;
    case 'GAME_STATE':
      myGameSeat = msg.state.mySeat;
      lastState = msg.state;
      inGame = true;
      showScreen('screen-game');
      renderGame(msg.state);
      break;
    case 'RECONNECTED':
      myName = msg.name;
      myLobbySeat = msg.seat;
      myToken = sessionStorage.getItem('pp_token');
      currentLobbyId = '';
      showScreen('screen-waiting');
      send({type:'REQUEST_STATE'});
      break;
    case 'RECONNECT_FAIL':
      sessionStorage.removeItem('pp_token');
      myToken=''; myName='';
      showScreen('screen-name');
      break;
    case 'ERROR':
      notif('⚠️ '+msg.text);
      break;
    case 'OPPONENT_RECONNECTED':
      notif('👋 '+msg.name+' voltou!');
      break;
    case 'OPPONENT_DISCONNECTED_GRACE':
      notif('📡 Um jogador desligou...');
      break;
  }
}

// ── Screens ────────────────────────────────────────────────────────────────────
function showScreen(id) {
  document.querySelectorAll('.screen').forEach(s=>s.classList.remove('active'));
  document.getElementById(id).classList.add('active');
}

// ── Name Screen ────────────────────────────────────────────────────────────────
document.getElementById('btn-go').onclick = () => {
  const n = document.getElementById('inp-name').value.trim();
  if (!n) { notif('Precisas de um nome!'); return; }
  myName = n.slice(0,20);
  showScreen('screen-lobby');
  renderLobbyList(_cachedLobbies);
  send({type:'LOBBIES'});
};
document.getElementById('inp-name').onkeydown = e => {
  if (e.key==='Enter') document.getElementById('btn-go').click();
};

// ── Lobby Screen ───────────────────────────────────────────────────────────────
function renderLobbyList(lobbies) {
  _cachedLobbies = lobbies;
  if (!myName) return;
  const el = document.getElementById('lobby-list');
  if (!el) return;
  el.innerHTML = '';
  for (const t of lobbies) {
    const div = document.createElement('div');
    div.className = 'table-card';
    const occupied = t.players;
    const status = t.inGame ? 'Em jogo' : (occupied >= t.maxPlayers ? 'Cheia' : 'Aberta');
    const badgeClass = t.inGame ? 'badge-game' : (occupied >= t.maxPlayers ? 'badge-full' : 'badge-open');
    div.innerHTML = '<div class="table-info"><h3>'+escH(t.name)+'</h3><p>'+occupied+'/'+t.maxPlayers+' jogadores</p></div>'
      +'<div style="display:flex;align-items:center;gap:8px;">'
      +'<span class="table-badge '+badgeClass+'">'+escH(status)+'</span>'
      +((!t.inGame && occupied < t.maxPlayers) ? '<button class="btn btn-primary btn-sm btn-join" data-id="'+t.id+'">Entrar</button>' : '')
      +'</div>';
    el.appendChild(div);
  }
  el.querySelectorAll('.btn-join').forEach(b => {
    b.onclick = () => send({type:'JOIN_LOBBY', lobbyId:b.dataset.id, playerName:myName});
  });
}

// ── Waiting Room ───────────────────────────────────────────────────────────────
function renderWaiting(lobby) {
  const wp = document.getElementById('waiting-players');
  wp.innerHTML = '';
  for (let i = 0; i < lobby.maxPlayers; i++) {
    const name = lobby.names[i] || '';
    const isMe = i === myLobbySeat;
    const div = document.createElement('div');
    div.className = 'player-slot';
    const dotClass = 'dot' + (name ? ' filled' : '') + (isMe ? ' me' : '');
    div.innerHTML = '<div class="'+dotClass+'"></div>'
      +'<span>'+(name ? escH(name) + (isMe ? ' (tu)' : '') : 'Livre...')+'</span>';
    wp.appendChild(div);
  }
  const filledCount = lobby.names.filter(Boolean).length;
  document.getElementById('btn-start').style.display = myLobbySeat === 0 && filledCount >= 2 ? 'block' : 'none';
}

document.getElementById('btn-start').onclick = () => send({type:'START'});
document.getElementById('btn-leave').onclick = () => {
  send({type:'LEAVE_LOBBY'});
  sessionStorage.removeItem('pp_token');
  myToken=''; inGame=false; currentLobbyId='';
  showScreen('screen-lobby');
};

// ── Game Rendering ─────────────────────────────────────────────────────────────
const PLAYER_COLORS = ['--p0','--p1','--p2','--p3'];
const GUARD_EMOJIS = ['🟥','🟦','🟩','🟨'];

function renderGame(state) {
  const isMyTurn = state.currentPlayer === state.mySeat;
  const phase = state.phase;

  // Top bar players
  const tpEl = document.getElementById('tp-players');
  tpEl.innerHTML = '';
  for (let i = 0; i < state.n; i++) {
    const p = state.players[i];
    const span = document.createElement('span');
    span.className = 'tp' + (i===state.currentPlayer?' active':'') + (i===state.mySeat?' me':'');
    const guardCount = (state.guards||[]).filter(g=>g.playerIdx===i).length;
    span.textContent = p.name + ' 🛟'+p.fichas + (guardCount>0?' 💂'+guardCount:'');
    tpEl.appendChild(span);
  }

  // Status
  const statusEl = document.getElementById('game-status');
  if (phase === 'GAME_OVER') {
    statusEl.textContent = '🏁 Fim de jogo!';
    renderEndScreen(state);
    return;
  }
  const curName = state.players[state.currentPlayer]?.name;
  if (isMyTurn && (phase==='PLACE_TILE'||phase==='PLACE_TILE_EXTRA')) {
    statusEl.textContent = '🎯 A tua vez! Coloca o tile.';
  } else if (isMyTurn && phase==='PLACE_GUARD') {
    statusEl.textContent = '🛟 Colocar salva-vidas?';
  } else {
    statusEl.textContent = '⏳ Vez de '+curName;
  }

  // Drawn tile
  document.getElementById('my-fichas').textContent = state.myFichas;
  const dtd = document.getElementById('drawn-tile-display');
  const dtDesc = document.getElementById('drawn-tile-desc');
  if (isMyTurn && state.drawnTile && !state.drawnTile.hidden) {
    const tile = state.drawnTile;
    dtd.textContent = tileEmoji(tile);
    dtd.className = 'drawn-tile '+tile.type;
    dtDesc.textContent = tileLabel(tile);
  } else if (state.drawnTile) {
    dtd.textContent = '🃏';
    dtd.className = 'drawn-tile';
    dtDesc.textContent = 'Tile escondido';
  } else {
    dtd.textContent = '—';
    dtDesc.textContent = '';
  }

  // Guard section
  const guardSec = document.getElementById('guard-section');
  const waitingTurn = document.getElementById('waiting-turn');
  if (isMyTurn && phase==='PLACE_GUARD') {
    guardSec.style.display='block';
    waitingTurn.style.display='none';
    const tile = state.board.find(t=>t.r===pendingGuard?.r&&t.c===pendingGuard?.c) ||
      (state.lastAction?.type==='PLACE' ? state.lastAction : null);
    const isRock = tile?.type==='rock';
    document.getElementById('btn-guard-h').disabled = isRock || state.myFichas<=0;
    document.getElementById('btn-guard-v').disabled = isRock || state.myFichas<=0;
  } else if (!isMyTurn || phase==='PLACE_TILE'||phase==='PLACE_TILE_EXTRA') {
    guardSec.style.display='none';
    waitingTurn.style.display = (!isMyTurn && (phase==='PLACE_TILE'||phase==='PLACE_TILE_EXTRA'||phase==='EXTRA_TURNS')) ? 'block' : 'none';
  } else {
    guardSec.style.display='none';
    waitingTurn.style.display='none';
  }

  // Board
  renderBoard(state);

  // Objectives
  renderObjs(state);
}

function renderBoard(state) {
  const canvas = document.getElementById('board-canvas');
  canvas.innerHTML = '';

  const TILE_SIZE = 56;
  const GAP = 4;
  const STEP = TILE_SIZE + GAP;

  const board = state.board || [];
  if (board.length === 0) return;

  const minR = Math.min(...board.map(t=>t.r));
  const minC = Math.min(...board.map(t=>t.c));
  const maxR = Math.max(...board.map(t=>t.r));
  const maxC = Math.max(...board.map(t=>t.c));

  // Include valid placements in bounds
  const valid = state.validPlacements || [];
  const allR = [...board.map(t=>t.r), ...valid.map(v=>v.r)];
  const allC = [...board.map(t=>t.c), ...valid.map(v=>v.c)];
  const vMinR = Math.min(...allR), vMinC = Math.min(...allC);
  const vMaxR = Math.max(...allR), vMaxC = Math.max(...allC);

  const W = (vMaxC - vMinC + 1) * STEP;
  const H = (vMaxR - vMinR + 1) * STEP;
  canvas.style.width = W + 'px';
  canvas.style.height = H + 'px';

  // Guards lookup: {r,c} → [guards]
  const guardMap = {};
  for (const g of (state.guards||[])) {
    const key = g.r+','+g.c;
    if (!guardMap[key]) guardMap[key] = [];
    guardMap[key].push(g);
  }

  // Place tiles
  for (const tile of board) {
    const x = (tile.c - vMinC) * STEP;
    const y = (tile.r - vMinR) * STEP;
    const div = document.createElement('div');
    div.className = 'tile ' + tile.type + (tile.id===0?' start-tile':'');
    div.style.left = x+'px';
    div.style.top = y+'px';
    div.style.width = TILE_SIZE+'px';
    div.style.height = TILE_SIZE+'px';
    div.innerHTML = tileEmoji(tile) + '<div class="bathers">' + tileLabel(tile) + '</div>';
    // Guard markers
    const guards = guardMap[tile.r+','+tile.c] || [];
    if (guards.length > 0) {
      const gm = document.createElement('div');
      gm.className = 'guard-marker';
      gm.title = guards.map(g=>state.players[g.playerIdx].name+' ('+( g.dir==='h'?'↔':'↕')+')')
        .join(', ');
      gm.textContent = guards.map(g=>(g.dir==='h'?'↔':'↕')+GUARD_EMOJIS[g.playerIdx]).join('');
      div.appendChild(gm);
    }
    canvas.appendChild(div);
  }

  // Valid placements
  const isMyTurnPlace = state.currentPlayer===state.mySeat &&
    (state.phase==='PLACE_TILE'||state.phase==='PLACE_TILE_EXTRA');
  if (isMyTurnPlace) {
    for (const v of valid) {
      const x = (v.c - vMinC) * STEP;
      const y = (v.r - vMinR) * STEP;
      const div = document.createElement('div');
      div.className = 'valid-cell';
      div.style.left = x+'px';
      div.style.top = y+'px';
      div.style.width = TILE_SIZE+'px';
      div.style.height = TILE_SIZE+'px';
      div.textContent = '+';
      div.onclick = () => {
        pendingGuard = {r:v.r, c:v.c};
        send({type:'PLACE_TILE', r:v.r, c:v.c});
      };
      canvas.appendChild(div);
    }
  }
}

function renderObjs(state) {
  const el = document.getElementById('obj-list');
  el.innerHTML = '';
  const all = [...(state.revealedObjs||[]), ...(state.claimedObjs||[])];
  for (const obj of all) {
    const div = document.createElement('div');
    div.className = 'obj-card' + (obj.claimedBy!==undefined?' claimed':'');
    div.innerHTML = '<span class="obj-pts">+'+obj.pts+'</span><span>'+escH(obj.desc)+'</span>'
      +(obj.claimedByName?'<span style="font-size:.7rem;color:#1b4332">✓ '+escH(obj.claimedByName)+'</span>':'');
    el.appendChild(div);
  }
}

// ── End Screen ─────────────────────────────────────────────────────────────────
function renderEndScreen(state) {
  showScreen('screen-end');
  const players = state.players.map((p,i)=>({
    ...p,
    seat:i,
    isMe: i===state.mySeat,
    guardPts: computeGuardPts(state, i),
    objPts: p.objPts,
    fichaBonus: p.fichas*2,
    total: 0,
  }));
  for (const p of players) {
    p.total = p.guardPts + p.objPts + p.fichaBonus;
  }
  players.sort((a,b) => b.total - a.total);
  const winner = players[0];
  document.getElementById('end-winner').textContent = '🏆 '+winner.name+' ganhou!';
  const table = document.getElementById('score-table');
  table.innerHTML = '<thead><tr><th>Jogador</th><th>🛟 Guardas</th><th>🎯 Obj.</th><th>💰 Fichas</th><th>Total</th></tr></thead>';
  const tbody = document.createElement('tbody');
  for (const p of players) {
    const tr = document.createElement('tr');
    if (p.seat === winner.seat) tr.className='winner';
    tr.innerHTML = '<td>'+(p.isMe?'⭐ ':'')+escH(p.name)+'</td>'
      +'<td>'+p.guardPts+'</td><td>'+p.objPts+'</td><td>'+p.fichaBonus+'</td>'
      +'<td><b>'+p.total+'</b></td>';
    tbody.appendChild(tr);
  }
  table.appendChild(tbody);
}

function computeGuardPts(state, playerIdx) {
  // crude estimate using server data — server computes proper final
  // If game over, pts field has server-computed total
  return state.players[playerIdx]?.pts || 0;
}

document.getElementById('btn-restart').onclick = () => {
  send({type:'RESTART'});
  showScreen('screen-waiting');
  inGame=false;
};

// ── Guard Buttons ──────────────────────────────────────────────────────────────
document.getElementById('btn-guard-h').onclick = () => send({type:'PLACE_GUARD', dir:'h'});
document.getElementById('btn-guard-v').onclick = () => send({type:'PLACE_GUARD', dir:'v'});
document.getElementById('btn-guard-skip').onclick = () => send({type:'SKIP_GUARD'});

// ── Tile Helpers ───────────────────────────────────────────────────────────────
function tileEmoji(tile) {
  if (tile.type==='rock') return '🪨';
  if (tile.type==='surf') return '🏄';
  if (tile.bathers===1) return '🧍';
  if (tile.bathers===2) return '👫';
  return '👨‍👩‍👦';
}
function tileLabel(tile) {
  if (tile.type==='rock') return 'Rocha';
  if (tile.type==='surf') return 'Prancha (×2)';
  return tile.bathers + (tile.bathers===1?' banhista':' banhistas');
}

// ── Notification ───────────────────────────────────────────────────────────────
let notifTimer;
function notif(text) {
  const el = document.getElementById('notif');
  el.textContent = text;
  el.classList.add('show');
  clearTimeout(notifTimer);
  notifTimer = setTimeout(()=>el.classList.remove('show'), 3000);
}

// ── Misc ──────────────────────────────────────────────────────────────────────
function escH(s) {
  return String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
}

document.addEventListener('visibilitychange', () => {
  if (!document.hidden && (!ws || ws.readyState > 1)) connect();
});

connect();
</script>
</body>
</html>`;

// ─── HTTP Server ──────────────────────────────────────────────────────────────
const server = http.createServer((req, res) => {
  const url = req.url.split('?')[0];
  if (url === '/' || url === '/index.html') {
    res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
    res.end(CLIENT_HTML);
  } else if (url === '/manifest.webmanifest') {
    res.writeHead(200, { 'Content-Type': 'application/manifest+json' });
    res.end(MANIFEST);
  } else if (url === '/sw.js') {
    res.writeHead(200, { 'Content-Type': 'application/javascript', 'Service-Worker-Allowed': '/' });
    res.end(SW);
  } else {
    serveStatic(req, res);
  }
});

// ─── WebSocket Server ─────────────────────────────────────────────────────────
const wss = new WebSocketServer({ server });

wss.on('connection', ws => {
  wsState.set(ws, {});
  ws.on('message', raw => {
    try { handleAction(ws, JSON.parse(raw)); } catch(e) { console.error(e); }
  });
  ws.on('close', () => {
    const st = wsState.get(ws);
    if (!st || !st.lobbyId) return;
    const lobby = lobbies[st.lobbyId];
    if (!lobby) return;
    const { seat, token } = st;
    lobby.players[seat] = null;
    lobby.players.forEach((p, i) => {
      if (p && i !== seat) sendTo(p, { type: 'OPPONENT_DISCONNECTED_GRACE', seat, name: lobby.names[seat], graceMs: GRACE_MS });
    });
    broadcastLobbyList();
    lobby.graceTimers[seat] = setTimeout(() => hardLeaveBySlot(lobby, seat), GRACE_MS);
  });
  // Send lobby list immediately
  sendTo(ws, { type: 'LOBBIES', lobbies: Object.values(lobbies).map(lobbyInfo) });
});

// Keep-alive pings
setInterval(() => {
  for (const ws of wss.clients) if (ws.readyState === 1) ws.ping();
}, 20000);

server.listen(PORT, () => console.log('🏖 Na Praia das Percebes a correr em porta', PORT));
