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
// 5 human tables
for (let i = 0; i < MAX_LOBBIES; i++) {
  const id = 'L' + (i + 1);
  lobbies[id] = {
    id, name: `Mesa ${i + 1}`, maxPlayers: 4,
    players: [null,null,null,null], names: ['','','',''], tokens: [null,null,null,null],
    game: null, graceTimers: [null,null,null,null], solo: false, aiCount: 0,
  };
}
// 3 AI tables: 1 player + 1 AI, 1 player + 2 AI, 1 player + 3 AI
const AI_TABLE_CONFIGS = [
  { id:'AI2', name:'🤖 vs 1 IA (2 jog.)',  maxPlayers:2, aiCount:1 },
  { id:'AI3', name:'🤖 vs 2 IA (3 jog.)',  maxPlayers:3, aiCount:2 },
  { id:'AI4', name:'🤖 vs 3 IA (4 jog.)',  maxPlayers:4, aiCount:3 },
];
for (const cfg of AI_TABLE_CONFIGS) {
  const slots = Array(cfg.maxPlayers).fill(null);
  const names = Array(cfg.maxPlayers).fill('');
  const tokens = Array(cfg.maxPlayers).fill(null);
  lobbies[cfg.id] = {
    id: cfg.id, name: cfg.name, maxPlayers: cfg.maxPlayers,
    players: slots, names, tokens,
    game: null, graceTimers: Array(cfg.maxPlayers).fill(null),
    solo: true, aiCount: cfg.aiCount,
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

// ─── Guard Line Check ──────────────────────────────────────────────────────────
// Returns true if there's already a guard watching a given row (dir='h') or col (dir='v')
function lineHasGuard(guards, r, c, dir) {
  return guards.some(g => g.dir === dir && (dir === 'h' ? g.r === r : g.c === c));
}

function getAvailableGuardDirs(guards, r, c) {
  return {
    h: !lineHasGuard(guards, r, c, 'h'),
    v: !lineHasGuard(guards, r, c, 'v'),
  };
}

// ─── Build View ────────────────────────────────────────────────────────────────
function buildView(g, seat) {
  const boardArr = Object.entries(g.board).map(([key, tile]) => {
    const [r,c] = key.split(',').map(Number);
    return { r, c, ...tile };
  });
  const validPlacements = (g.phase === 'PLACE_TILE' || g.phase === 'PLACE_TILE_EXTRA') && g.currentPlayer === seat && g.drawnTile
    ? getValidPlacements(g.board) : [];

  // For guard phase, tell client which directions are available
  let availableGuardDirs = null;
  if (g.phase === 'PLACE_GUARD' && g.currentPlayer === seat && g.pendingPlacement) {
    const { r, c } = g.pendingPlacement;
    const tile = boardGet(g.board, r, c);
    if (tile && tile.type !== 'rock') {
      availableGuardDirs = getAvailableGuardDirs(g.guards, r, c);
    } else {
      availableGuardDirs = { h: false, v: false };
    }
  }

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
    availableGuardDirs,
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
  const humanNames = lobby.names.filter(Boolean);
  if (humanNames.length < 1) return;
  // AI table: fill remaining seats with AI names
  const allNames = [...humanNames];
  if (lobby.solo) {
    const aiNames = ['🤖 IA Mariana','🤖 IA João','🤖 IA Sofia'];
    while (allNames.length < lobby.maxPlayers) {
      allNames.push(aiNames[allNames.length - humanNames.length] || ('🤖 IA '+(allNames.length)));
    }
    // track which seats are AI (seats >= humanNames.length)
    lobby.aiSeats = allNames.map((_, i) => i >= humanNames.length);
  } else {
    lobby.aiSeats = allNames.map(() => false);
  }
  lobby.game = newGame(allNames, lobby.solo);
  lobby.game.drawnTile = drawTile(lobby.game);
  broadcastGame(lobby);
  // if AI goes first, schedule its move
  maybeScheduleBot(lobby);
}

// ─── Bot AI ───────────────────────────────────────────────────────────────────
function maybeScheduleBot(lobby) {
  const g = lobby.game;
  if (!g || g.phase === 'GAME_OVER') return;
  if (!lobby.aiSeats || !lobby.aiSeats[g.currentPlayer]) return;
  const gen = g.turnGen;
  setTimeout(() => {
    if (!lobby.game || lobby.game.turnGen !== gen) return;
    botMove(lobby);
  }, 1200 + Math.random() * 800);
}

function botMove(lobby) {
  const g = lobby.game;
  if (!g || g.phase === 'GAME_OVER') return;
  const seat = g.currentPlayer;
  if (!lobby.aiSeats[seat]) return;

  if (g.phase === 'PLACE_TILE' || g.phase === 'PLACE_TILE_EXTRA') {
    const valid = getValidPlacements(g.board);
    if (valid.length === 0) { nextTurn(lobby); return; }
    // pick best placement: prefer high bathers in surrounding lines
    const scored = valid.map(v => {
      const rowLen = Object.keys(g.board).filter(k => +k.split(',')[0] === v.r).length;
      const colLen = Object.keys(g.board).filter(k => +k.split(',')[1] === v.c).length;
      return { ...v, score: rowLen + colLen + Math.random() };
    });
    scored.sort((a,b) => b.score - a.score);
    const pick = scored[0];
    boardSet(g.board, pick.r, pick.c, g.drawnTile);
    g.pendingPlacement = { r: pick.r, c: pick.c };
    g.drawnTile = null;
    // check objectives
    for (const obj of [...g.revealedObjs]) {
      if (checkObjective(obj, g.board, pick.r, pick.c)) {
        g.revealedObjs = g.revealedObjs.filter(o => o.id !== obj.id);
        obj.claimedBy = seat; obj.claimedByName = g.players[seat].name;
        g.claimedObjs.push(obj);
        g.players[seat].objPts += obj.pts;
        if (g.remainingObjs.length > 0) g.revealedObjs.push(g.remainingObjs.shift());
      }
    }
    g.phase = 'PLACE_GUARD';
    broadcastGame(lobby);
    // schedule guard decision
    const gen = g.turnGen;
    setTimeout(() => {
      if (!lobby.game || lobby.game.turnGen !== gen) return;
      botGuard(lobby, pick.r, pick.c, seat);
    }, 800);
  } else if (g.phase === 'PLACE_GUARD') {
    const { r, c } = g.pendingPlacement;
    botGuard(lobby, r, c, seat);
  }
}

function botGuard(lobby, r, c, seat) {
  const g = lobby.game;
  if (!g || g.currentPlayer !== seat) return;
  const tile = boardGet(g.board, r, c);
  // don't place on rock
  if (tile && tile.type === 'rock') { nextTurn(lobby); return; }

  // check which directions are available (no existing guard in that line/col)
  const canH = !lineHasGuard(g.guards, r, c, 'h');
  const canV = !lineHasGuard(g.guards, r, c, 'v');

  // decide: place guard if fichas > 0 and line looks valuable
  const rowLen = Object.keys(g.board).filter(k => +k.split(',')[0] === r).length;
  const colLen = Object.keys(g.board).filter(k => +k.split(',')[1] === c).length;
  const shouldPlace = g.players[seat].fichas > 0 && (rowLen + colLen > 3 || Math.random() > 0.4);

  if (shouldPlace && g.players[seat].fichas > 0 && (canH || canV)) {
    // pick best available direction
    let dir;
    if (canH && canV) dir = rowLen >= colLen ? 'h' : 'v';
    else if (canH) dir = 'h';
    else dir = 'v';

    g.players[seat].fichas--;
    g.guards.push({ r, c, dir, playerIdx: seat, id: g.guardIdSeq++ });
    if (g.players[seat].fichas === 0) { handleFichasEmpty(lobby, seat); return; }
  }
  nextTurn(lobby);
}

function advanceTurn(lobby) {
  const g = lobby.game;
  g.drawnTile = drawTile(g);
  if (!g.drawnTile) { endGame(lobby); return; }
  g.currentPlayer = (g.currentPlayer + 1) % g.n;
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
      const minRequired = lobby.solo ? 1 : 2;
      if (seated < minRequired) { sendTo(ws, { type: 'ERROR', text: lobby.solo ? 'Precisa de pelo menos 1 jogador' : 'Mínimo 2 jogadores' }); return; }
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
        sendTo(ws, { type: 'GAME_STATE', state: buildView(g, seat) });
        return;
      }
      if (lineHasGuard(g.guards, r, c, dir)) {
        sendTo(ws, { type: 'ERROR', text: 'Já existe um salva-vidas nessa ' + (dir === 'h' ? 'linha' : 'coluna') });
        sendTo(ws, { type: 'GAME_STATE', state: buildView(g, seat) });
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
  maybeScheduleBot(lobby);
}

function nextTurn(lobby) {
  const g = lobby.game;
  g.turnGen++;
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
  maybeScheduleBot(lobby);
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
    --p0bg:#fde8ea;--p1bg:#dbeaf5;--p2bg:#d0f0ed;--p3bg:#fdf6dc;
    font-size:18px;
  }
  *{box-sizing:border-box;margin:0;padding:0;font-family:'Segoe UI',sans-serif;}
  body{background:linear-gradient(160deg,#caf0f8 0%,#90e0ef 40%,var(--sand) 100%);min-height:100vh;overflow-x:hidden;}
  .screen{display:none;min-height:100vh;padding:20px;}
  .screen.active{display:flex;flex-direction:column;align-items:center;}
  .credits{font-size:.7rem;color:#888;margin-top:auto;padding-top:16px;font-style:italic;}

  /* ── Name Screen ── */
  #screen-name{justify-content:center;gap:22px;text-align:center;}
  .sunset-title{
    font-size:3.2rem;font-weight:900;letter-spacing:-.02em;
    background:linear-gradient(135deg,#ff4e00 0%,#ec9f05 25%,#ff6b35 50%,#f7c59f 70%,#fffae0 100%);
    -webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text;
    text-shadow:none;line-height:1.1;
    filter:drop-shadow(0 4px 16px rgba(255,100,0,.25));
  }
  .subtitle{font-size:1rem;color:#666;margin-top:-10px;}
  .inp-wrap{display:flex;gap:10px;width:100%;max-width:420px;}
  input{flex:1;padding:14px 18px;border:2px solid var(--sea2);border-radius:14px;font-size:1rem;outline:none;background:#ffffffe0;}
  input:focus{border-color:var(--deep);}
  .btn{padding:14px 22px;border:none;border-radius:14px;font-size:1rem;font-weight:700;cursor:pointer;transition:transform .1s,box-shadow .1s;}
  .btn:active{transform:scale(.96);}
  .btn-primary{background:linear-gradient(135deg,var(--sea),var(--deep));color:#fff;box-shadow:0 4px 14px rgba(0,80,160,.3);}
  .btn-secondary{background:var(--sand);color:var(--dark);border:2px solid var(--sand2);}
  .btn-danger{background:#e63946;color:#fff;}
  .btn-sm{padding:9px 15px;font-size:.88rem;}

  /* ── Lobby Screen ── */
  #screen-lobby{gap:18px;max-width:580px;margin:0 auto;width:100%;}
  .lobby-header{text-align:center;}
  .lobby-header h2{font-size:1.6rem;color:var(--deep);}
  .lobby-section-title{font-size:.85rem;font-weight:700;color:#666;text-transform:uppercase;letter-spacing:.05em;margin-top:6px;}
  .table-list{width:100%;display:flex;flex-direction:column;gap:11px;}
  .table-card{background:#ffffffd0;border-radius:18px;padding:15px 18px;display:flex;align-items:center;justify-content:space-between;box-shadow:0 2px 12px rgba(0,0,0,.1);}
  .table-card.ai-table{border-left:4px solid #a855f7;}
  .table-info h3{font-size:1rem;color:var(--dark);}
  .table-info p{font-size:.82rem;color:#666;}
  .table-badge{font-size:.77rem;padding:5px 9px;border-radius:9px;font-weight:700;}
  .badge-open{background:#d8f3dc;color:#1b4332;}
  .badge-full{background:#ffd6d6;color:#c1121f;}
  .badge-game{background:#ffd6a5;color:#774900;}

  /* ── Waiting Room ── */
  #screen-waiting{gap:18px;max-width:440px;margin:0 auto;width:100%;text-align:center;}
  .waiting-players{width:100%;display:flex;flex-direction:column;gap:9px;}
  .player-slot{background:#ffffffc0;border-radius:13px;padding:11px 15px;display:flex;align-items:center;gap:12px;}
  .player-color-swatch{width:18px;height:18px;border-radius:4px;flex-shrink:0;}
  .player-slot .dot{width:13px;height:13px;border-radius:50%;background:#ccc;flex-shrink:0;}
  .dot.filled{background:var(--sea2);}
  .dot.me{background:#2dc653;}

  /* ── Game Screen ── */
  #screen-game{padding:0;gap:0;max-width:100%;align-items:stretch;}
  .game-topbar{background:var(--deep);color:#fff;padding:10px 18px;display:grid;grid-template-columns:1fr auto 1fr;align-items:center;gap:8px;}
  .topbar-players{display:flex;gap:10px;flex-wrap:wrap;align-items:center;}
  .topbar-title{text-align:center;font-size:.9rem;font-weight:700;color:#caf0f8;white-space:nowrap;}
  .game-status{font-size:.82rem;color:#caf0f8;text-align:right;}
  .tp{padding:5px 11px;border-radius:20px;font-size:.8rem;font-weight:700;background:#ffffff20;display:flex;align-items:center;gap:6px;}
  .tp.active{background:#ffffff40;outline:2px solid #ffd166;}
  .tp.me{outline:2px solid #06d6a0;}
  .tp-swatch{width:10px;height:10px;border-radius:3px;flex-shrink:0;}

  /* ── Board ── */
  .game-main{display:flex;flex-direction:column;align-items:center;flex:1;padding:14px;gap:14px;}
  .board-wrap{position:relative;overflow:auto;max-width:100%;max-height:58vh;}
  .board-canvas{position:relative;}
  .tile{position:absolute;width:84px;height:84px;border-radius:12px;display:flex;flex-direction:column;align-items:center;justify-content:center;font-size:1.6rem;border:2px solid #ccc;cursor:default;transition:transform .1s;user-select:none;}
  .tile.normal{background:linear-gradient(135deg,var(--sand),var(--sand2));}
  .tile.surf{background:linear-gradient(135deg,#ff9f1c,#ffbf69);}
  .tile.rock{background:linear-gradient(135deg,#8d8d8d,#555);color:#fff;}
  .tile.start-tile{border:2px solid var(--deep);}
  .tile .bathers{font-size:.7rem;color:#444;margin-top:2px;}
  .tile.rock .bathers{color:#ddd;}
  .tile .guard-marker{position:absolute;top:3px;right:3px;font-size:.75rem;line-height:1;}
  .valid-cell{position:absolute;width:84px;height:84px;border-radius:12px;border:3px dashed var(--sea);background:rgba(0,180,216,.15);cursor:pointer;transition:background .15s;display:flex;align-items:center;justify-content:center;font-size:1.8rem;}
  .valid-cell:hover{background:rgba(0,180,216,.38);}

  /* ── Panel ── */
  .game-panel{background:#ffffffd0;border-radius:18px;padding:14px 18px;width:100%;max-width:560px;}
  .panel-row{display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap;}
  .drawn-tile-wrap{display:flex;align-items:center;gap:12px;}
  .drawn-tile{width:70px;height:70px;border-radius:12px;display:flex;flex-direction:column;align-items:center;justify-content:center;font-size:1.6rem;border:3px solid var(--deep);}
  .guard-btns{display:flex;gap:7px;flex-wrap:wrap;}
  .fichas-count{font-size:.88rem;color:#555;}
  .my-color-badge{display:inline-flex;align-items:center;gap:6px;font-size:.82rem;font-weight:700;padding:4px 10px;border-radius:20px;margin-bottom:8px;}

  /* ── Objectives ── */
  .obj-list{display:flex;flex-wrap:wrap;gap:7px;margin-top:9px;}
  .obj-card{background:var(--sand);border-radius:9px;padding:7px 11px;font-size:.78rem;display:flex;gap:7px;align-items:center;}
  .obj-card.claimed{background:#d8f3dc;text-decoration:line-through;color:#666;}
  .obj-pts{font-weight:800;color:var(--deep);}

  /* ── End Screen ── */
  #screen-end{justify-content:center;gap:18px;text-align:center;max-width:460px;margin:0 auto;}
  .score-table{width:100%;border-collapse:collapse;border-radius:13px;overflow:hidden;box-shadow:0 2px 14px rgba(0,0,0,.1);}
  .score-table th{background:var(--deep);color:#fff;padding:11px;}
  .score-table td{padding:11px;text-align:center;border-bottom:1px solid #eee;background:#fff;}
  .score-table tr:last-child td{border-bottom:none;}
  .score-table tr.winner td{background:#d8f3dc;font-weight:700;}
  .winner-banner{font-size:1.9rem;font-weight:900;color:var(--deep);}
  .notif{position:fixed;top:20px;left:50%;transform:translateX(-50%);background:var(--dark);color:#fff;padding:13px 26px;border-radius:13px;font-size:.9rem;z-index:999;pointer-events:none;opacity:0;transition:opacity .3s;max-width:90vw;text-align:center;}
  .notif.show{opacity:1;}
  @media(min-width:750px){
    .game-main{flex-direction:row;align-items:flex-start;}
    .board-wrap{max-height:80vh;}
    .game-panel{max-width:300px;}
  }
</style>
</head>
<body>

<!-- Name Screen -->
<div id="screen-name" class="screen active">
  <div class="sunset-title">Praia das Percebes</div>
  <div class="subtitle">Jogo de colocação de tiles para 2–4 jogadores</div>
  <div class="inp-wrap">
    <input id="inp-name" placeholder="O teu nome..." maxlength="20" autocomplete="off"/>
    <button class="btn btn-primary" id="btn-go">Entrar</button>
  </div>
  <div class="credits">um jogo de David Marques</div>
</div>

<!-- Lobby Screen -->
<div id="screen-lobby" class="screen">
  <div class="lobby-header"><h2>🌊 Escolhe uma mesa</h2></div>
  <div class="lobby-section-title">Multijogador</div>
  <div class="table-list" id="lobby-list-human"></div>
  <div class="lobby-section-title">Jogar com IA</div>
  <div class="table-list" id="lobby-list-ai"></div>
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
    <div class="topbar-title">🏖 Praia das Percebes</div>
    <div class="game-status" id="game-status">A aguardar...</div>
  </div>
  <div class="game-main">
    <div class="board-wrap">
      <div class="board-canvas" id="board-canvas"></div>
    </div>
    <div class="game-panel">
      <div id="my-color-badge-wrap"></div>
      <div id="drawn-section">
        <div style="font-weight:700;margin-bottom:9px;color:var(--dark)">🃏 Tile Retirado</div>
        <div class="panel-row">
          <div class="drawn-tile-wrap">
            <div class="drawn-tile" id="drawn-tile-display">?</div>
            <div>
              <div id="drawn-tile-desc" style="font-size:.82rem;color:#555"></div>
              <div class="fichas-count">🛟 Fichas: <b id="my-fichas">8</b></div>
            </div>
          </div>
        </div>
        <div id="guard-section" style="margin-top:11px;display:none;">
          <div style="font-size:.88rem;color:#555;margin-bottom:7px">Colocar salva-vidas?</div>
          <div class="guard-btns">
            <button class="btn btn-primary btn-sm" id="btn-guard-h">↔ Horizontal</button>
            <button class="btn btn-primary btn-sm" id="btn-guard-v">↕ Vertical</button>
            <button class="btn btn-secondary btn-sm" id="btn-guard-skip">✗ Não</button>
          </div>
        </div>
        <div id="waiting-turn" style="display:none;margin-top:11px;font-size:.88rem;color:#888;text-align:center;">
          ⏳ Vez de outro jogador...
        </div>
      </div>
      <hr style="margin:13px 0;border:none;border-top:1px solid #ddd;"/>
      <div style="font-weight:700;color:var(--dark);margin-bottom:7px">🎯 Objetivos</div>
      <div class="obj-list" id="obj-list"></div>
      <div class="credits" style="text-align:center;margin-top:14px;">um jogo de David Marques</div>
    </div>
  </div>
</div>

<!-- End Screen -->
<div id="screen-end" class="screen">
  <div class="logo">🏆</div>
  <div class="winner-banner" id="end-winner"></div>
  <table class="score-table" id="score-table"></table>
  <button class="btn btn-primary" id="btn-restart" style="width:100%">↺ Nova Partida</button>
  <div class="credits">um jogo de David Marques</div>
</div>

<div class="notif" id="notif"></div>

<script>
// ── Constants ──────────────────────────────────────────────────────────────────
const PLAYER_COLORS = ['#e63946','#457b9d','#2a9d8f','#e9c46a'];
const PLAYER_COLORS_BG = ['#fde8ea','#dbeaf5','#d0f0ed','#fdf6dc'];
const GUARD_SYMS = ['↔↕','↔↕','↔↕','↔↕']; // colored by playerIdx

// ── State ──────────────────────────────────────────────────────────────────────
let ws, myName='', myToken='', myLobbySeat=-1, myGameSeat=-1;
let currentLobbyId='', inGame=false, isAiTable=false;
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
      isAiTable = msg.solo;
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
      isAiTable = msg.solo;
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
  const humanEl = document.getElementById('lobby-list-human');
  const aiEl    = document.getElementById('lobby-list-ai');
  if (!humanEl) return;
  humanEl.innerHTML = '';
  aiEl.innerHTML = '';

  for (const t of lobbies) {
    const isAi = t.id && t.id.startsWith('AI');
    const div = document.createElement('div');
    div.className = 'table-card' + (isAi ? ' ai-table' : '');
    const occupied = t.players;
    const status = t.inGame ? 'Em jogo' : (occupied >= t.maxPlayers ? 'Cheia' : 'Aberta');
    const badgeClass = t.inGame ? 'badge-game' : (occupied >= t.maxPlayers ? 'badge-full' : 'badge-open');
    const canJoin = !t.inGame && occupied < t.maxPlayers;
    div.innerHTML = '<div class="table-info"><h3>'+escH(t.name)+'</h3><p>'+occupied+'/'+t.maxPlayers+' jogadores</p></div>'
      +'<div style="display:flex;align-items:center;gap:9px;">'
      +'<span class="table-badge '+badgeClass+'">'+escH(status)+'</span>'
      +(canJoin ? '<button class="btn btn-primary btn-sm btn-join" data-id="'+t.id+'">Entrar</button>' : '')
      +'</div>';
    (isAi ? aiEl : humanEl).appendChild(div);
  }
  document.querySelectorAll('.btn-join').forEach(b => {
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
    const swatch = document.createElement('div');
    swatch.className = 'player-color-swatch';
    swatch.style.background = name ? PLAYER_COLORS[i] : '#ddd';
    const dotEl = document.createElement('div');
    dotEl.className = 'dot' + (name ? ' filled' : '') + (isMe ? ' me' : '');
    const label = document.createElement('span');
    label.textContent = name ? name + (isMe ? ' (tu)' : '') : 'Livre...';
    div.appendChild(swatch);
    div.appendChild(dotEl);
    div.appendChild(label);
    wp.appendChild(div);
  }
  const filledCount = lobby.names.filter(Boolean).length;
  const minReq = isAiTable ? 1 : 2;
  document.getElementById('btn-start').style.display = myLobbySeat === 0 && filledCount >= minReq ? 'block' : 'none';
}

document.getElementById('btn-start').onclick = () => send({type:'START'});
document.getElementById('btn-leave').onclick = () => {
  send({type:'LEAVE_LOBBY'});
  sessionStorage.removeItem('pp_token');
  myToken=''; inGame=false; currentLobbyId='';
  showScreen('screen-lobby');
};

// ── Game Rendering ─────────────────────────────────────────────────────────────
function renderGame(state) {
  const isMyTurn = state.currentPlayer === state.mySeat;
  const phase = state.phase;

  // My color badge in panel
  const badgeWrap = document.getElementById('my-color-badge-wrap');
  badgeWrap.innerHTML = '';
  const badge = document.createElement('div');
  badge.className = 'my-color-badge';
  badge.style.background = PLAYER_COLORS_BG[state.mySeat];
  badge.style.color = PLAYER_COLORS[state.mySeat];
  badge.style.border = '2px solid ' + PLAYER_COLORS[state.mySeat];
  const sw = document.createElement('div');
  sw.style.cssText = 'width:14px;height:14px;border-radius:3px;background:'+PLAYER_COLORS[state.mySeat];
  badge.appendChild(sw);
  badge.appendChild(document.createTextNode(state.players[state.mySeat]?.name));
  badgeWrap.appendChild(badge);

  // Top bar players
  const tpEl = document.getElementById('tp-players');
  tpEl.innerHTML = '';
  for (let i = 0; i < state.n; i++) {
    const p = state.players[i];
    const span = document.createElement('span');
    span.className = 'tp' + (i===state.currentPlayer?' active':'') + (i===state.mySeat?' me':'');
    const sw2 = document.createElement('div');
    sw2.className = 'tp-swatch';
    sw2.style.background = PLAYER_COLORS[i];
    span.appendChild(sw2);
    const guardCount = (state.guards||[]).filter(g=>g.playerIdx===i).length;
    span.appendChild(document.createTextNode(p.name + ' 🛟'+p.fichas + (guardCount>0?' 💂'+guardCount:'')));
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

  // Guard section — disable based on server-provided availability
  const guardSec = document.getElementById('guard-section');
  const waitingTurn = document.getElementById('waiting-turn');
  if (isMyTurn && phase==='PLACE_GUARD') {
    guardSec.style.display='block';
    waitingTurn.style.display='none';
    const avail = state.availableGuardDirs;
    const la = state.lastAction;
    const isRock = la && la.tile && la.tile.type === 'rock';
    const noFichas = state.myFichas <= 0;
    const canH = avail ? avail.h : true;
    const canV = avail ? avail.v : true;
    document.getElementById('btn-guard-h').disabled = isRock || noFichas || !canH;
    document.getElementById('btn-guard-v').disabled = isRock || noFichas || !canV;
    const guardLabel = document.getElementById('guard-section').querySelector('div');
    if (isRock) {
      guardLabel.textContent = '🪨 Rocha — sem salva-vidas';
    } else if (!canH && !canV) {
      guardLabel.textContent = '🚫 Linha e coluna já têm salva-vidas';
    } else if (!canH) {
      guardLabel.textContent = '↕ Só vertical disponível';
    } else if (!canV) {
      guardLabel.textContent = '↔ Só horizontal disponível';
    } else {
      guardLabel.textContent = 'Colocar salva-vidas?';
    }
  } else {
    guardSec.style.display='none';
    waitingTurn.style.display = (!isMyTurn && phase!=='GAME_OVER') ? 'block' : 'none';
  }

  // Board
  renderBoard(state);
  // Objectives
  renderObjs(state);
}

function renderBoard(state) {
  const canvas = document.getElementById('board-canvas');
  canvas.innerHTML = '';
  const TILE_SIZE = 84;
  const GAP = 6;
  const STEP = TILE_SIZE + GAP;
  const board = state.board || [];
  if (board.length === 0) return;

  const valid = state.validPlacements || [];
  const allR = [...board.map(t=>t.r), ...valid.map(v=>v.r)];
  const allC = [...board.map(t=>t.c), ...valid.map(v=>v.c)];
  const vMinR = Math.min(...allR), vMinC = Math.min(...allC);
  const vMaxR = Math.max(...allR), vMaxC = Math.max(...allC);
  const W = (vMaxC - vMinC + 1) * STEP;
  const H = (vMaxR - vMinR + 1) * STEP;
  canvas.style.width = W + 'px';
  canvas.style.height = H + 'px';

  // Guards lookup
  const guardMap = {};
  for (const g of (state.guards||[])) {
    const key = g.r+','+g.c;
    if (!guardMap[key]) guardMap[key] = [];
    guardMap[key].push(g);
  }

  for (const tile of board) {
    const x = (tile.c - vMinC) * STEP;
    const y = (tile.r - vMinR) * STEP;
    const div = document.createElement('div');
    div.className = 'tile ' + tile.type + (tile.id===0?' start-tile':'');
    div.style.left = x+'px';
    div.style.top = y+'px';
    div.style.width = TILE_SIZE+'px';
    div.style.height = TILE_SIZE+'px';
    const emojiEl = document.createElement('div');
    emojiEl.textContent = tileEmoji(tile);
    div.appendChild(emojiEl);
    const bathEl = document.createElement('div');
    bathEl.className = 'bathers';
    bathEl.textContent = tileLabel(tile);
    div.appendChild(bathEl);
    const guards = guardMap[tile.r+','+tile.c] || [];
    if (guards.length > 0) {
      const gm = document.createElement('div');
      gm.className = 'guard-marker';
      // show colored dots for each guard
      for (const g of guards) {
        const dot = document.createElement('span');
        dot.textContent = g.dir==='h' ? '↔' : '↕';
        dot.style.color = PLAYER_COLORS[g.playerIdx];
        dot.title = state.players[g.playerIdx]?.name + ' (' + (g.dir==='h'?'↔':'↕') + ')';
        gm.appendChild(dot);
      }
      div.appendChild(gm);
    }
    canvas.appendChild(div);
  }

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
    const pts = document.createElement('span');
    pts.className = 'obj-pts';
    pts.textContent = '+'+obj.pts;
    div.appendChild(pts);
    const desc = document.createElement('span');
    desc.textContent = obj.desc;
    div.appendChild(desc);
    if (obj.claimedByName) {
      const who = document.createElement('span');
      who.style.cssText = 'font-size:.7rem;color:#1b4332';
      who.textContent = '✓ '+obj.claimedByName;
      div.appendChild(who);
    }
    el.appendChild(div);
  }
}

// ── End Screen ─────────────────────────────────────────────────────────────────
function renderEndScreen(state) {
  showScreen('screen-end');
  const players = state.players.map((p,i)=>({
    ...p, seat:i, isMe:i===state.mySeat,
    total: (p.pts||0),
  }));
  players.sort((a,b)=>b.total-a.total);
  const winner = players[0];
  document.getElementById('end-winner').textContent = '🏆 '+winner.name+' ganhou!';
  const table = document.getElementById('score-table');
  table.innerHTML = '<thead><tr><th></th><th>Jogador</th><th>Pontos</th></tr></thead>';
  const tbody = document.createElement('tbody');
  for (const p of players) {
    const tr = document.createElement('tr');
    if (p.seat===winner.seat) tr.className='winner';
    const swCell = document.createElement('td');
    const sw = document.createElement('div');
    sw.style.cssText = 'width:14px;height:14px;border-radius:3px;background:'+PLAYER_COLORS[p.seat]+';margin:0 auto';
    swCell.appendChild(sw);
    tr.appendChild(swCell);
    const nameCell = document.createElement('td');
    nameCell.textContent = (p.isMe?'⭐ ':'')+p.name;
    tr.appendChild(nameCell);
    const ptsCell = document.createElement('td');
    ptsCell.innerHTML = '<b>'+p.total+'</b>';
    tr.appendChild(ptsCell);
    tbody.appendChild(tr);
  }
  table.appendChild(tbody);
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
  if (tile.type==='surf') return 'Prancha ×2';
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
