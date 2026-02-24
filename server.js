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
// tile: { id, bathers, type, variantIdx } type: 'normal'|'surf'|'rock'|'sand'
// variantIdx: sequential index within category (1-based), used for unique tile images
// Base deck: 44 tiles total
// 4 surf, 2 rock, 6×3-bathers, 12×2-bathers, 8×1-bather, 12 sand
function buildDeck(nPlayers) {
  const tiles = [];
  let id = 1;
  for (let i = 0; i < 8;  i++) tiles.push({ id: id++, bathers: 1, type: 'normal', variantIdx: i+1 });
  for (let i = 0; i < 12; i++) tiles.push({ id: id++, bathers: 2, type: 'normal', variantIdx: i+1 });
  for (let i = 0; i < 6;  i++) tiles.push({ id: id++, bathers: 3, type: 'normal', variantIdx: i+1 });
  for (let i = 0; i < 4;  i++) tiles.push({ id: id++, bathers: 1, type: 'surf',   variantIdx: i+1 });
  for (let i = 0; i < 2;  i++) tiles.push({ id: id++, bathers: 0, type: 'rock',   variantIdx: i+1 });
  for (let i = 0; i < 12; i++) tiles.push({ id: id++, bathers: 0, type: 'sand',   variantIdx: i+1 });
  // shuffle
  for (let i = tiles.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [tiles[i], tiles[j]] = [tiles[j], tiles[i]];
  }
  // Trim for player count: 2→44 (all), 3→42 (remove 2), 4→44 (all)
  const target = nPlayers === 3 ? 42 : 44;
  return tiles.slice(0, target);
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
  // check grid span: overall board must fit within 7×7
  const allR = occupied.map(p => p.r);
  const allC = occupied.map(p => p.c);
  if (Math.max(...allR, r) - Math.min(...allR, r) >= MAX_LINE) return false;
  if (Math.max(...allC, c) - Math.min(...allC, c) >= MAX_LINE) return false;
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
function newGame(names, isSolo, nPlayers) {
  // nPlayers is passed explicitly to avoid any ambiguity with AI tables
  const n = nPlayers || names.length;
  const deck = buildDeck(n);
  const totalDeck = deck.length;
  const allObjs = buildObjectives();
  const revealed = allObjs.slice(0, 4);
  const remaining = allObjs.slice(4);

  // Fichas scaled by player count to avoid guard congestion
  const fichasByN = { 2: 6, 3: 5, 4: 4 };
  const fichas = fichasByN[n] || 6;

  const board = {};
  boardSet(board, 0, 0, { id: 0, bathers: 1, type: 'normal' }); // starting tile

  return {
    players: names.map(name => ({ name, pts: 0, guards: [], fichas, objPts: 0 })),
    n: names.length,
    deck,
    totalDeck,
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
    players: g.players.map(p => ({ name: p.name, pts: p.pts, fichas: p.fichas, objPts: p.objPts })),
    n: g.n,
    board: boardArr,
    guards: g.guards,
    phase: g.phase,
    currentPlayer: g.currentPlayer,
    drawnTile: g.currentPlayer === seat && g.drawnTile ? g.drawnTile : (g.drawnTile ? { hidden: true } : null),
    deckSize: g.deck.length,
    totalDeck: g.totalDeck || 44,
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
    inGame: !!lobby.game && lobby.game.phase !== 'GAME_OVER',
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
  lobby.game = newGame(allNames, lobby.solo, lobby.maxPlayers);
  if (allNames.length !== lobby.maxPlayers) {
    console.warn('[startGame] allNames.length mismatch: got', allNames.length, 'expected', lobby.maxPlayers);
  }
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
    // Check if guard phase is needed
    const tileIsRock = g.board[pick.r + ',' + pick.c]?.type === 'rock';
    const canH = !lineHasGuard(g.guards, pick.r, pick.c, 'h');
    const canV = !lineHasGuard(g.guards, pick.r, pick.c, 'v');
    const hasGuardOption = !tileIsRock && (canH || canV) && g.players[seat].fichas > 0;

    if (!hasGuardOption) {
      g.pendingPlacement = null;
      nextTurn(lobby);
    } else {
      g.phase = 'PLACE_GUARD';
      broadcastGame(lobby);
      // schedule guard decision
      const gen = g.turnGen;
      setTimeout(() => {
        if (!lobby.game || lobby.game.turnGen !== gen) return;
        botGuard(lobby, pick.r, pick.c, seat);
      }, 800);
    }
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
  // Reset lobby immediately — clients already have the final scores rendered
  // from the GAME_STATE broadcast above. No need to hold slots.
  setTimeout(() => resetLobby(lobby), 300);
}

function resetLobby(lobby) {
  // Clear all player slots and sessions, reset game
  for (let i = 0; i < lobby.maxPlayers; i++) {
    if (lobby.tokens[i]) delete sessions[lobby.tokens[i]];
    // Disconnect the ws gracefully if still open
    const ws = lobby.players[i];
    if (ws && ws.readyState === 1) {
      sendTo(ws, { type: 'LOBBY_RESET' });
    }
    lobby.players[i] = null;
    lobby.names[i] = '';
    lobby.tokens[i] = null;
    if (lobby.graceTimers[i]) { clearTimeout(lobby.graceTimers[i]); lobby.graceTimers[i] = null; }
  }
  lobby.game = null;
  lobby.aiSeats = null;
  broadcastLobbyList();
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
  if (msg.type === 'REJOIN')    { handleRejoin(ws, msg); return; }
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

      // Move to guard decision phase — but skip immediately if rock or no fichas
      const placedIsRock = placedTile.type === 'rock';
      const availH = !lineHasGuard(g.guards, r, c, 'h');
      const availV = !lineHasGuard(g.guards, r, c, 'v');
      const hasAnyGuardDir = !placedIsRock && (availH || availV) && g.players[seat].fichas > 0;

      if (!hasAnyGuardDir) {
        // Skip guard phase entirely — go straight to next turn
        g.pendingPlacement = null;
        nextTurn(lobby);
      } else {
        g.phase = 'PLACE_GUARD';
        g.pendingPlacement = { r, c };
        broadcastGame(lobby);
      }
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
      resetLobby(lobby);
      break;
    }
  }
}

function handleFichasEmpty(lobby, seat) {
  // Fichas vazias não terminam o jogo — o jogador simplesmente não pode colocar mais guards
  // O jogo continua até o baralho esgotar
  nextTurn(lobby);
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
  g.pendingPlacement = null;
  // End game if deck can no longer serve all players
  if (g.deck.length < g.n) {
    endGame(lobby);
    return;
  }
  g.drawnTile = drawTile(g);
  if (!g.drawnTile) {
    endGame(lobby);
    return;
  }
  // If grid is completely full (no valid placements), discard tiles and skip turns
  // until a valid placement is found or deck/player count triggers end
  let safetyLimit = g.n * 2;
  while (getValidPlacements(g.board).length === 0 && safetyLimit-- > 0) {
    g.drawnTile = null;
    if (g.deck.length < g.n) { endGame(lobby); return; }
    g.currentPlayer = (g.currentPlayer + 1) % g.n;
    g.drawnTile = drawTile(g);
    if (!g.drawnTile) { endGame(lobby); return; }
  }
  if (getValidPlacements(g.board).length === 0) {
    // Grid truly full — end game
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
  // If game is over, free the slot immediately and reject reconnect
  if (!lobby.game || lobby.game.phase === 'GAME_OVER') {
    const { seat } = sess;
    delete sessions[msg.token];
    if (lobby.graceTimers[seat]) { clearTimeout(lobby.graceTimers[seat]); lobby.graceTimers[seat] = null; }
    lobby.players[seat] = null;
    lobby.names[seat] = '';
    lobby.tokens[seat] = null;
    broadcastLobbyList();
    sendTo(ws, { type: 'RECONNECT_FAIL' }); return;
  }
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
  lobby.players.forEach((p, i) => {
    if (p && i !== seat) sendTo(p, { type: 'OPPONENT_RECONNECTED', seat, name });
  });
}

// Rejoin: player lost their token but remembers their name + lobbyId
// Find their slot in the active game by name and re-attach
function handleRejoin(ws, msg) {
  const { lobbyId, playerName } = msg;
  const lobby = lobbies[lobbyId];
  if (!lobby || !lobby.game || lobby.game.phase === 'GAME_OVER') {
    sendTo(ws, { type: 'REJOIN_FAIL' }); return;
  }
  const name = (playerName || '').trim().slice(0, 20);
  const seat = lobby.names.findIndex(n => n === name);
  if (seat === -1) { sendTo(ws, { type: 'REJOIN_FAIL' }); return; }
  // Slot found — re-attach
  const token = Math.random().toString(36).slice(2) + Date.now().toString(36);
  if (lobby.graceTimers[seat]) { clearTimeout(lobby.graceTimers[seat]); lobby.graceTimers[seat] = null; }
  // Clean up old session if any
  if (lobby.tokens[seat]) delete sessions[lobby.tokens[seat]];
  lobby.players[seat] = ws;
  lobby.tokens[seat] = token;
  sessions[token] = { lobbyId, seat, name };
  wsState.set(ws, { lobbyId, seat, token });
  sendTo(ws, { type: 'RECONNECTED', seat, name, solo: lobby.solo, newToken: token });
  broadcastGame(lobby);
  lobby.players.forEach((p, i) => {
    if (p && i !== seat) sendTo(p, { type: 'OPPONENT_RECONNECTED', seat, name });
  });
}
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
  "name": "Praia das Percebes",
  "short_name": "Percebes",
  "description": "Jogo de colocação de tiles para 2–4 jogadores",
  "start_url": "/",
  "display": "standalone",
  "orientation": "portrait",
  "background_color": "#0077b6",
  "theme_color": "#023e8a",
  "icons": [
    { "src": "/public/icon-192.png", "sizes": "192x192", "type": "image/png", "purpose": "any maskable" },
    { "src": "/public/icon-512.png", "sizes": "512x512", "type": "image/png", "purpose": "any maskable" }
  ]
}`;
const SW = `
const CACHE = 'percebes-v1';
const SHELL = ['/', '/manifest.webmanifest'];

self.addEventListener('install', e => {
  e.waitUntil(caches.open(CACHE).then(c => c.addAll(SHELL)));
  self.skipWaiting();
});

self.addEventListener('activate', e => {
  e.waitUntil(caches.keys().then(keys =>
    Promise.all(keys.filter(k => k !== CACHE).map(k => caches.delete(k)))
  ));
  self.clients.claim();
});

self.addEventListener('fetch', e => {
  const url = new URL(e.request.url);
  // Always go to network for WebSocket upgrades and game API
  if (e.request.headers.get('upgrade') === 'websocket') return;
  // Cache-first for static assets (icons, tile images)
  if (url.pathname.startsWith('/public/')) {
    e.respondWith(
      caches.match(e.request).then(cached => cached || fetch(e.request).then(res => {
        const clone = res.clone();
        caches.open(CACHE).then(c => c.put(e.request, clone));
        return res;
      }))
    );
    return;
  }
  // Network-first for everything else (game stays live)
  e.respondWith(
    fetch(e.request).catch(() => caches.match(e.request))
  );
});
`;

// ─── CLIENT HTML ──────────────────────────────────────────────────────────────
const CLIENT_HTML = `<!DOCTYPE html>
<html lang="pt">
<head>
<meta charset="UTF-8"/>
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1"/>
<meta name="theme-color" content="#023e8a"/>
<meta name="apple-mobile-web-app-capable" content="yes"/>
<meta name="apple-mobile-web-app-status-bar-style" content="black-translucent"/>
<meta name="apple-mobile-web-app-title" content="Percebes"/>
<link rel="manifest" href="/manifest.webmanifest"/>
<link rel="icon" href="/public/icon-192.png" type="image/png"/>
<link rel="apple-touch-icon" href="/public/icon-512.png"/>
<!-- Apple splash screens -->
<link rel="apple-touch-startup-image" href="/public/splash-1170x2532.png" media="(device-width:390px) and (device-height:844px) and (-webkit-device-pixel-ratio:3)"/>
<link rel="apple-touch-startup-image" href="/public/splash-1284x2778.png" media="(device-width:428px) and (device-height:926px) and (-webkit-device-pixel-ratio:3)"/>
<link rel="apple-touch-startup-image" href="/public/splash-1125x2436.png" media="(device-width:375px) and (device-height:812px) and (-webkit-device-pixel-ratio:3)"/>
<link rel="apple-touch-startup-image" href="/public/splash-750x1334.png"  media="(device-width:375px) and (device-height:667px) and (-webkit-device-pixel-ratio:2)"/>
<title>Praia das Percebes</title>
<script>
  if ('serviceWorker' in navigator) {
    window.addEventListener('load', () => navigator.serviceWorker.register('/sw.js'));
  }
</script>
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
    background:linear-gradient(135deg,#e85d04 0%,#f48c06 45%,#faa307 100%);
    -webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text;
    text-shadow:none;line-height:1.1;
    filter:drop-shadow(0 4px 20px rgba(232,93,4,.3));
  }
  .subtitle{font-size:1rem;color:#666;margin-top:-10px;}
  .inp-wrap{display:flex;gap:10px;width:100%;max-width:420px;}
  input{flex:1;padding:14px 18px;border:2px solid var(--sea2);border-radius:14px;font-size:1rem;outline:none;background:#ffffffe0;}
  input:focus{border-color:var(--deep);}
  @media(max-width:480px){
    #screen-name{gap:14px;}
    .sunset-title{font-size:2.2rem !important;}
    .subtitle{font-size:.85rem;}
    .inp-wrap{flex-direction:column;align-items:stretch;}
    .inp-wrap .btn{width:100%;}
  }
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
  #screen-game{padding:0;gap:0;width:100%;align-items:stretch !important;height:100vh;overflow:hidden;flex-direction:column !important;}
  .game-topbar{background:var(--deep);color:#fff;padding:8px 14px;display:flex;align-items:center;justify-content:space-between;gap:8px;flex-shrink:0;}
  .topbar-players{display:flex;gap:6px;flex-wrap:wrap;align-items:center;flex:1;min-width:0;}
  .topbar-title{display:none;}
  .topbar-right{display:flex;align-items:center;gap:10px;justify-content:flex-end;}
  .game-status{font-size:.78rem;color:#555;font-style:italic;}
  .board-footer{display:flex;align-items:center;justify-content:center;gap:10px;padding:6px 14px;flex-shrink:0;}
  .tp{padding:5px 11px;border-radius:20px;font-size:.8rem;font-weight:700;background:#ffffff20;display:flex;align-items:center;gap:6px;}
  .tp.active{background:#ffffff40;outline:2px solid #ffd166;}
  .tp.me{outline:2px solid #06d6a0;}
  .tp-swatch{width:10px;height:10px;border-radius:3px;flex-shrink:0;}
  .btn-rules{background:#ffffff22;border:1px solid #ffffff44;color:#fff;padding:5px 12px;border-radius:20px;font-size:.78rem;font-weight:700;cursor:pointer;white-space:nowrap;}
  .btn-rules:hover{background:#ffffff33;}
  .btn-leave-game{background:#e6394622;border:1px solid #e6394666;}
  .btn-leave-game:hover{background:#e6394644;}
  .deck-counter{background:#e8f4f8;border:1px solid #b0d8e8;color:var(--deep);padding:4px 10px;border-radius:20px;font-size:.78rem;font-weight:700;white-space:nowrap;}
  .board-footer .btn-rules{background:#e8f4f8;border:1px solid #b0d8e8;color:var(--deep);}

  /* ── Main layout: board centered, bottom panel ── */
  .game-body{display:flex;flex-direction:column;flex:1;overflow:hidden;min-height:0;}

  /* Board zone — fills available space, board centered inside */
  .board-zone{flex:1;display:flex;flex-direction:column;align-items:center;justify-content:center;overflow:hidden;position:relative;padding:14px 14px 0;}
  .board-scroll{overflow:auto;max-width:100%;max-height:100%;display:flex;align-items:center;justify-content:center;scrollbar-width:none;}
  .board-scroll::-webkit-scrollbar{display:none;}
  .board-canvas{position:relative;margin:auto;}

  .tile{position:absolute;width:84px;height:84px;border-radius:12px;display:flex;flex-direction:column;align-items:center;justify-content:center;font-size:1.6rem;border:2px solid #ccc;cursor:default;transition:transform .1s;user-select:none;}
  .tile.normal{background:linear-gradient(135deg,var(--sand),var(--sand2));}
  .tile.surf{background:linear-gradient(135deg,#ff9f1c,#ffbf69);}
  .tile.rock{background:linear-gradient(135deg,#8d8d8d,#555);color:#fff;}
  .tile.sand{background:linear-gradient(135deg,#f5deb3,#e8c97a);}
  .tile.start-tile{border:2px solid var(--deep);}
  .tile .bathers{font-size:.7rem;color:#444;margin-top:2px;}
  .tile.rock .bathers{color:#ddd;}
  .tile-img{width:100%;height:100%;object-fit:contain;border-radius:8px;display:block;}
  .drawn-tile .tile-img{width:100%;height:100%;object-fit:contain;border-radius:10px;}
  .valid-cell{position:absolute;width:84px;height:84px;border-radius:12px;border:3px dashed var(--sea);background:rgba(0,180,216,.15);cursor:pointer;transition:background .15s;display:flex;align-items:center;justify-content:center;font-size:1.8rem;}
  .valid-cell:hover{background:rgba(0,180,216,.38);}

  /* Turn guide strip */
  .turn-guide{background:#ffffffb0;backdrop-filter:blur(6px);border-radius:12px;padding:8px 14px;display:flex;gap:6px;align-items:center;flex-wrap:wrap;font-size:.75rem;color:#444;border:1px solid #e0e0e0;margin:8px 14px 0;flex-shrink:0;}
  .tg-step{display:flex;align-items:center;gap:5px;white-space:nowrap;}
  .tg-num{width:20px;height:20px;border-radius:50%;background:var(--deep);color:#fff;font-size:.7rem;font-weight:800;display:flex;align-items:center;justify-content:center;flex-shrink:0;}
  .tg-arrow{color:#aaa;font-size:.8rem;}
  .tg-score{background:#e8f4f8;border-radius:8px;padding:3px 8px;font-size:.72rem;color:var(--deep);font-weight:600;white-space:nowrap;}

  /* Bottom panel: 2 columns */
  .bottom-panel{display:flex;gap:0;background:#ffffffd0;border-top:1px solid #ddd;flex-shrink:0;height:200px;}
  .panel-turn{flex:1;padding:10px 16px 10px;border-right:1px solid #eee;overflow:hidden;display:flex;flex-direction:column;gap:0;}
  .panel-objectives{flex:1;padding:10px 16px;overflow:hidden;}
  .panel-label{font-weight:700;color:var(--dark);font-size:.82rem;margin-bottom:6px;}
  .my-color-badge{display:inline-flex;align-items:center;gap:6px;font-size:.78rem;font-weight:700;padding:3px 10px;border-radius:20px;margin-bottom:6px;}
  /* Tile row: tile left, everything else stacked right */
  .tile-main-row{display:flex;gap:14px;align-items:flex-start;flex:1;}
  .tile-col{display:flex;flex-direction:column;align-items:flex-start;gap:3px;flex-shrink:0;}
  .drawn-tile{width:64px;height:64px;border-radius:12px;display:flex;flex-direction:column;align-items:center;justify-content:center;font-size:1.8rem;border:3px solid var(--deep);flex-shrink:0;}
  .drawn-tile-label{font-size:.62rem;color:#888;text-align:center;width:64px;margin-top:2px;}
  /* Right col: guard buttons stacked vertically then fichas */
  .tile-right-col{display:flex;flex-direction:column;justify-content:center;gap:8px;flex:1;}
  /* Guard buttons: horizontal strip */
  .guard-row{display:flex;gap:6px;align-items:center;flex-wrap:nowrap;}
  .guard-divider{color:#bbb;font-size:.9rem;user-select:none;}
  .btn{padding:14px 22px;border:none;border-radius:14px;font-size:1rem;font-weight:700;cursor:pointer;transition:transform .1s,box-shadow .1s;}
  .btn:active{transform:scale(.96);}
  .btn-primary{background:linear-gradient(135deg,var(--sea),var(--deep));color:#fff;box-shadow:0 4px 14px rgba(0,80,160,.3);}
  .btn-secondary{background:var(--sand);color:var(--dark);border:2px solid var(--sand2);}
  .btn-sm{padding:8px 14px;font-size:.83rem;border-radius:10px;}
  .btn-skip{background:#f0f0f0;color:#555;border:1.5px solid #ccc;}
  /* Fichas dots */
  .fichas-row{display:flex;align-items:center;gap:5px;flex-wrap:wrap;}
  .ficha-dot{width:14px;height:14px;border-radius:3px;display:inline-block;flex-shrink:0;}
  .fichas-label{font-size:.78rem;color:#555;font-weight:600;margin-right:2px;}
  .waiting-msg{font-size:.82rem;color:#888;font-style:italic;}
  .guard-btns{display:flex;gap:5px;flex-wrap:wrap;}

  /* Objectives */
  .obj-list{display:flex;flex-wrap:wrap;gap:6px;}
  .obj-card{background:var(--sand);border-radius:8px;padding:5px 9px;font-size:.74rem;display:flex;gap:6px;align-items:center;}
  .obj-card.claimed{background:#d8f3dc;text-decoration:line-through;color:#666;}
  .obj-pts{font-weight:800;color:var(--deep);}
  .credits-small{font-size:.65rem;color:#aaa;font-style:italic;text-align:center;margin-top:8px;}

  /* ── Rules Modal ── */
  .modal-overlay{position:fixed;inset:0;background:rgba(0,0,0,.55);z-index:500;display:flex;align-items:center;justify-content:center;padding:16px;opacity:0;pointer-events:none;transition:opacity .2s;}
  .modal-overlay.open{opacity:1;pointer-events:all;}
  .modal{background:#fff;border-radius:20px;padding:24px 28px;max-width:560px;width:100%;max-height:85vh;overflow-y:auto;box-shadow:0 8px 40px rgba(0,0,0,.25);}
  .modal h2{font-size:1.3rem;color:var(--deep);margin-bottom:14px;}
  .modal h3{font-size:.95rem;color:var(--deep);margin:14px 0 6px;font-weight:800;}
  .modal p,.modal li{font-size:.85rem;color:#444;line-height:1.5;}
  .modal ul{padding-left:18px;display:flex;flex-direction:column;gap:4px;}
  .modal-close{float:right;background:none;border:none;font-size:1.4rem;cursor:pointer;color:#666;line-height:1;}
  .rule-step{display:flex;gap:10px;align-items:flex-start;margin-bottom:8px;}
  .rule-num{width:24px;height:24px;border-radius:50%;background:var(--deep);color:#fff;font-size:.78rem;font-weight:800;display:flex;align-items:center;justify-content:center;flex-shrink:0;margin-top:1px;}
  .score-pill{display:inline-block;background:#e8f4f8;color:var(--deep);border-radius:6px;padding:2px 7px;font-size:.78rem;font-weight:700;margin-left:4px;}

  /* ── Objectives Strip ── */
  .obj-strip{background:#ffffffc0;border-bottom:1px solid #ddd;flex-shrink:0;}
  .obj-strip-toggle{display:none;}
  .obj-strip-inner{padding:6px 14px;display:flex;gap:8px;flex-wrap:wrap;align-items:flex-start;overflow-x:auto;}
  .panel-objectives{display:none;} /* old panel no longer used */

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

  /* ── Mobile Layout ── */
  @media (max-width:600px) {
    html { font-size:15px; }

    /* Lobby & waiting screens */
    #screen-lobby, #screen-waiting { padding:14px; }
    .lobby-header h2 { font-size:1.3rem; }

    /* Topbar: more compact */
    .game-topbar { padding: 6px 10px; }
    .topbar-players { font-size: .7rem; gap: 4px; }
    .tp { padding: 3px 7px; font-size: .7rem; }
    .btn-leave-game { font-size: .68rem; padding: 4px 8px; }

    /* Board footer compact */
    .board-footer { padding: 3px 10px; gap: 8px; }
    .deck-counter { font-size: .68rem; padding: 2px 7px; }
    .board-footer .btn-rules { font-size: .68rem; padding: 2px 7px; }

    /* Hide turn-guide on mobile */
    .turn-guide { display: none; }

    /* Board tiles smaller */
    .tile { width: 60px !important; height: 60px !important; font-size: 1.2rem !important; border-radius: 9px !important; }
    .tile .bathers { font-size: .6rem !important; }
    .tile .guard-marker { font-size: 1.1rem !important; }
    .valid-cell { width: 60px !important; height: 60px !important; font-size: 1.3rem !important; }

    /* Bottom panel: anchored to bottom of screen */
    .bottom-panel {
      position: fixed;
      bottom: 0; left: 0; right: 0;
      height: auto;
      max-height: none;
      overflow: visible;
      flex-direction: row;
      z-index: 10;
      box-shadow: 0 -2px 10px rgba(0,0,0,.12);
    }
    .panel-turn { border-right: none; padding: 15px 10px; flex: 1; flex-shrink: 0; }
    .panel-objectives { display: none; }
    /* Give the game-body padding so content isn't hidden behind fixed panel */
    .game-body { padding-bottom: 140px; }

    /* Badge row compact */
    .my-color-badge { font-size: .7rem; padding: 2px 6px; }
    .ficha-dot { width: 10px; height: 10px; }
    #game-status { font-size: .68rem; }

    /* Tile + guard buttons */
    .tile-main-row { gap: 8px; margin-top: 4px; }
    .drawn-tile { width: 46px !important; height: 46px !important; font-size: 1.2rem !important; }
    .drawn-tile-label { font-size: .58rem !important; width: 46px !important; }
    .guard-row { flex-wrap: wrap; gap: 3px; }
    .btn-sm { padding: 5px 8px; font-size: .74rem; }
    .waiting-msg { font-size: .72rem; }

    /* Objectives strip: at top on mobile (stays after topbar naturally) */
    .obj-strip { border-bottom: 1px solid #ddd; border-top: none; }
    .obj-strip-toggle {
      display: flex !important;
      width: 100%;
      align-items: center;
      justify-content: space-between;
      font-size: .78rem;
      font-weight: 700;
      color: var(--deep);
      background: #eaf6ff;
      border: none;
      border-bottom: 1px solid #dde;
      padding: 8px 14px;
      cursor: pointer;
    }
    .obj-strip-inner { flex-direction: column; gap: 5px; padding: 8px 12px; max-height: 35vh; overflow-y: auto; }
    .obj-strip-inner.mob-hidden { display: none; }
    .obj-card { font-size: .68rem; padding: 4px 7px; }
    .obj-pts { font-size: .75rem; }

    /* Modal */
    .modal { padding: 16px 18px; border-radius: 14px; }
    .modal h2 { font-size: 1.1rem; }
    .modal h3 { font-size: .85rem; }
    .modal p, .modal li { font-size: .78rem; }
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
  <div class="lobby-header"><h2>Escolhe uma mesa</h2></div>
  <div class="lobby-section-title">Multijogador</div>
  <div class="table-list" id="lobby-list-human"></div>
  <div class="lobby-section-title">Jogar com IA</div>
  <div class="table-list" id="lobby-list-ai"></div>
</div>

<!-- Waiting Screen -->
<div id="screen-waiting" class="screen">
  <h2 style="color:var(--deep)">Sala de Espera</h2>
  <p id="waiting-table-name" style="color:#555;font-size:.9rem"></p>
  <div class="waiting-players" id="waiting-players"></div>
  <button class="btn btn-primary" id="btn-start" style="width:100%">▶ Iniciar Jogo</button>
  <button class="btn btn-secondary btn-sm" id="btn-leave">Sair da Mesa</button>
</div>

<!-- Rules Modal -->
<div class="modal-overlay" id="modal-rules">
  <div class="modal">
    <button class="modal-close" id="btn-modal-close">✕</button>
    <h2>Regras — Praia das Percebes</h2>

    <h3>Objetivo</h3>
    <p>Coloca salva-vidas em tiles da praia. Cada salva-vidas vigia uma linha ou coluna e no final do jogo vale os banhistas nesse segmento.</p>

    <h3>Baralho</h3>
    <p>44 tiles no total (42 para 3 jogadores): 8 × 1 banhista, 12 × 2 banhistas, 6 × 3 banhistas, 4 pranchas de surf, 2 rochas, 12 areia. O jogo termina quando o baralho tem menos tiles do que jogadores.</p>

    <h3>Sequência de Turno</h3>
    <div class="rule-step"><div class="rule-num">1</div><p><b>Pescar tile</b> — retira automaticamente o tile do topo do baralho.</p></div>
    <div class="rule-step"><div class="rule-num">2</div><p><b>Colocar tile</b> — coloca-o ortogonalmente adjacente a um tile existente (nunca diagonal). A grelha nunca pode exceder 7×7 slots.</p></div>
    <div class="rule-step"><div class="rule-num">3</div><p><b>Salva-vidas (opcional)</b> — coloca 1 salva-vidas no tile que acabaste de jogar: horizontal (↔) ou vertical (↕). Gasta 1 ficha. Só 1 salva-vidas por linha e por coluna em todo o tabuleiro.</p></div>
    <div class="rule-step"><div class="rule-num">4</div><p><b>Verificar objetivos</b> — se completaste um objetivo revelado, recolhes a carta imediatamente.</p></div>

    <h3>Tiles Especiais</h3>
    <ul>
      <li><b>Prancha de surf (↔×2)</b> — conta 1 banhista mas dobra todos os pontos dessa linha/coluna. Várias pranchas multiplicam (×4, ×8…).</li>
      <li><b>Rocha</b> — vale 0 banhistas e bloqueia a contagem da linha/coluna. Não podes colocar salva-vidas em rochas.</li>
      <li><b>Areia</b> — vale 0 banhistas. Ocupa espaço na grelha mas não contribui para a pontuação.</li>
    </ul>

    <h3>Pontuação (só no final)</h3>
    <ul>
      <li><b>Salva-vidas</b> — soma os banhistas no seu segmento de linha/coluna (para nas rochas), com multiplicadores de pranchas.</li>
      <li><b>Fichas restantes</b> — +2 pts por cada ficha não gasta. Cada jogador começa com fichas conforme o número de jogadores: 6 fichas (2 jog.), 5 fichas (3 jog.), 4 fichas (4 jog.).</li>
      <li><b>Objetivos</b> — soma os pontos das cartas conquistadas.</li>
    </ul>

    <h3>Fim de Jogo</h3>
    <p>O jogo termina quando o baralho fica com menos tiles do que jogadores. Quando um jogador fica sem fichas, simplesmente já não pode colocar mais salva-vidas — mas continua a jogar tiles até o fim.</p>

    <h3>Objetivos Disponíveis</h3>
    <ul>
      <li>Quadrado 3×3 (9 tiles) <span class="score-pill">+2</span></li>
      <li>Quadrado 5×5 (25 tiles) <span class="score-pill">+2</span></li>
      <li>Linha de 5 tiles <span class="score-pill">+4</span></li>
      <li>Coluna de 5 tiles <span class="score-pill">+4</span></li>
      <li>2 Pranchas adjacentes <span class="score-pill">+4</span></li>
      <li>Linha de 7 tiles <span class="score-pill">+6</span></li>
      <li>Coluna de 7 tiles <span class="score-pill">+6</span></li>
      <li>Excursão (2×2 tiles com 3 banhistas cada) <span class="score-pill">+6</span></li>
    </ul>
  </div>
</div>

<!-- Game Screen -->
<div id="screen-game" class="screen">
  <div class="game-topbar">
    <div class="topbar-players" id="tp-players"></div>
    <button class="btn-rules btn-leave-game" id="btn-leave-game">Sair</button>
  </div>

  <!-- Objectives: always visible on desktop, collapsible strip on mobile -->
  <div class="obj-strip" id="obj-strip">
    <button class="obj-strip-toggle" id="btn-mob-objs" style="display:none">Objetivos ▾</button>
    <div class="obj-strip-inner" id="obj-inner">
      <div class="obj-list" id="obj-list"></div>
    </div>
  </div>

  <!-- Deck counter + rules, just below objectives -->
  <div class="board-footer">
    <div class="deck-counter" id="deck-counter" title="Tiles restantes no baralho">Baralho: <span id="deck-count">—</span></div>
    <button class="btn-rules" id="btn-show-rules">Regras</button>
  </div>

  <div class="game-body">
    <!-- Board: centered, grows from middle -->
    <div class="board-zone">
      <div class="board-scroll">
        <div class="board-canvas" id="board-canvas"></div>
      </div>
    </div>

    <!-- Turn sequence strip (desktop only) -->
    <div class="turn-guide">
      <div class="tg-step"><div class="tg-num">1</div> Pescar tile</div>
      <div class="tg-arrow">›</div>
      <div class="tg-step"><div class="tg-num">2</div> Colocar no tabuleiro</div>
      <div class="tg-arrow">›</div>
      <div class="tg-step"><div class="tg-num">3</div> Salva-vidas? (↔↕)</div>
      <div class="tg-arrow">›</div>
      <div class="tg-step"><div class="tg-num">4</div> Objetivos?</div>
      <div class="tg-score">pontos = banhistas na linha · prancha ×2 · rocha bloqueia · +2/ficha restante</div>
    </div>

    <!-- Bottom 2-column panel -->
    <div class="bottom-panel">
      <!-- Left: turn panel -->
      <div class="panel-turn">
        <!-- Player badge + fichas + status inline -->
        <div id="my-color-badge-wrap"></div>
        <!-- Tile + right column -->
        <div class="tile-main-row">
          <div class="tile-col">
            <div class="drawn-tile" id="drawn-tile-display">?</div>
            <div class="drawn-tile-label" id="drawn-tile-desc"></div>
          </div>
          <div class="tile-right-col">
            <!-- Guard buttons in a horizontal strip -->
            <div id="guard-section" style="opacity:0;pointer-events:none;transition:opacity .15s;">
              <div class="guard-row">
                <button class="btn btn-primary btn-sm" id="btn-guard-h">↔ Horizontal</button>
                <span class="guard-divider" id="guard-div-h">|</span>
                <button class="btn btn-primary btn-sm" id="btn-guard-v">↕ Vertical</button>
                <span class="guard-divider">|</span>
                <button class="btn btn-sm btn-skip" id="btn-guard-skip">✗</button>
              </div>
            </div>
            <div id="waiting-turn" class="waiting-msg" style="opacity:0;pointer-events:none;transition:opacity .15s;">
              Vez de outro jogador...
            </div>
          </div>
        </div>
        <!-- Mobile: objectives moved to top strip -->
      </div>
    </div>
  </div>
</div>

<!-- End Screen -->
<div id="screen-end" class="screen">
  <div class="logo">🏆</div>
  <div class="winner-banner" id="end-winner"></div>
  <table class="score-table" id="score-table"></table>
  <button class="btn btn-primary" id="btn-restart" style="width:100%">↺ Nova Partida</button>
  <div id="end-countdown" style="font-size:.78rem;color:#888;font-style:italic;text-align:center;margin-top:4px;"></div>
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

// Restore name from sessionStorage if available
myName = sessionStorage.getItem('pp_name') || '';
if (myName) document.getElementById('inp-name').value = myName;

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
      sessionStorage.setItem('pp_lobby', currentLobbyId);
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
      if (msg.newToken) { myToken = msg.newToken; sessionStorage.setItem('pp_token', myToken); }
      else myToken = sessionStorage.getItem('pp_token') || '';
      currentLobbyId = '';
      sessionStorage.removeItem('pp_lobby');
      showScreen('screen-waiting');
      send({type:'REQUEST_STATE'});
      break;
    case 'RECONNECT_FAIL': {
      sessionStorage.removeItem('pp_token');
      myToken=''; inGame=false; currentLobbyId='';
      if (document.getElementById('screen-end').classList.contains('active')) break;
      // Try rejoin by name if we know which lobby we were in
      const savedLobby = sessionStorage.getItem('pp_lobby');
      if (myName && savedLobby) {
        send({type:'REJOIN', lobbyId:savedLobby, playerName:myName});
      } else if (myName) {
        send({type:'LOBBIES'}); showScreen('screen-lobby'); renderLobbyList(_cachedLobbies);
      } else {
        showScreen('screen-name');
      }
      break;
    }
    case 'REJOIN_FAIL':
      sessionStorage.removeItem('pp_lobby');
      send({type:'LOBBIES'}); showScreen('screen-lobby'); renderLobbyList(_cachedLobbies);
      break;
    case 'LOBBY_RESET':
      // Server cleared the table — clean up state
      sessionStorage.removeItem('pp_token');
      myToken=''; inGame=false; currentLobbyId='';
      // If player is already on the score screen, stay there — don't redirect
      if (!document.getElementById('screen-end').classList.contains('active')) {
        send({type:'LOBBIES'});
        showScreen('screen-lobby');
        renderLobbyList(_cachedLobbies);
      }
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
  sessionStorage.setItem('pp_name', myName);
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

  // My color badge in panel (with fichas dots inline)
  const badgeWrap = document.getElementById('my-color-badge-wrap');
  badgeWrap.innerHTML = '';
  const badgeRow = document.createElement('div');
  badgeRow.style.cssText = 'display:flex;align-items:center;gap:8px;margin-bottom:6px;flex-wrap:wrap;';
  // Name badge
  const badge = document.createElement('div');
  badge.className = 'my-color-badge';
  badge.style.background = PLAYER_COLORS_BG[state.mySeat];
  badge.style.color = PLAYER_COLORS[state.mySeat];
  badge.style.border = '2px solid ' + PLAYER_COLORS[state.mySeat];
  const sw = document.createElement('div');
  sw.style.cssText = 'width:14px;height:14px;border-radius:3px;background:'+PLAYER_COLORS[state.mySeat];
  badge.appendChild(sw);
  badge.appendChild(document.createTextNode(state.players[state.mySeat]?.name));
  badgeRow.appendChild(badge);
  // Fichas dots right after the badge
  const fichasDots = document.createElement('div');
  fichasDots.id = 'fichas-dots';
  fichasDots.style.cssText = 'display:flex;gap:3px;align-items:center;flex-wrap:wrap;';
  const playerColor = PLAYER_COLORS[state.mySeat];
  const totalFichas = state.myFichas || 0;
  for (let i = 0; i < totalFichas; i++) {
    const dot = document.createElement('span');
    dot.className = 'ficha-dot';
    dot.style.background = playerColor;
    fichasDots.appendChild(dot);
  }
  if (totalFichas === 0) {
    const none = document.createElement('span');
    none.style.cssText = 'font-size:.72rem;color:#aaa;font-style:italic;';
    none.textContent = 'sem fichas';    fichasDots.appendChild(none);
  }
  badgeRow.appendChild(fichasDots);
  // Status inline after fichas
  const statusInline = document.createElement('span');
  statusInline.id = 'game-status';
  statusInline.style.cssText = 'font-size:.75rem;color:#555;font-style:italic;margin-left:4px;flex-shrink:1;min-width:0;';
  badgeRow.appendChild(statusInline);
  badgeWrap.appendChild(badgeRow);

  // Deck counter
  const deckCountEl = document.getElementById('deck-count');
  if (deckCountEl) {
    const remaining = state.deckSize || 0;
    const total = state.totalDeck || 44;
    const isLow = remaining <= state.n;
    deckCountEl.textContent = remaining + '/' + total;
    const counterEl = document.getElementById('deck-counter');
    if (counterEl) counterEl.style.background = isLow ? '#fde8ea' : '#e8f4f8';
  }

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
    span.appendChild(document.createTextNode(p.name + ' ·'+p.fichas + (guardCount>0?' ↔'+guardCount:'')));
    tpEl.appendChild(span);
  }

  // Status
  const statusEl = document.getElementById('game-status');
  if (phase === 'GAME_OVER') {
    statusEl.textContent = 'Fim de jogo!';
    renderEndScreen(state);
    return;
  }
  const curName = state.players[state.currentPlayer]?.name;
  if (isMyTurn && (phase==='PLACE_TILE'||phase==='PLACE_TILE_EXTRA')) {
    statusEl.textContent = 'A tua vez! Coloca o tile.';
  } else if (isMyTurn && phase==='PLACE_GUARD') {
    statusEl.textContent = 'Colocar salva-vidas?';
  } else {
    statusEl.textContent = 'Vez de '+curName;
  }

  // Drawn tile
  document.getElementById('my-fichas') && (document.getElementById('my-fichas').textContent = state.myFichas);
  const dtd = document.getElementById('drawn-tile-display');
  const dtDesc = document.getElementById('drawn-tile-desc');
  if (isMyTurn && state.drawnTile && !state.drawnTile.hidden) {
    const tile = state.drawnTile;
    dtd.innerHTML = tileEmoji(tile);
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

  // Guard section — auto-skip if rock or no dirs, otherwise show buttons
  const guardSec = document.getElementById('guard-section');
  const waitingTurn = document.getElementById('waiting-turn');
  const showGuard = isMyTurn && phase==='PLACE_GUARD';
  const showWaiting = !isMyTurn && phase!=='GAME_OVER';

  if (showGuard) {
    const avail = state.availableGuardDirs;
    const noFichas = state.myFichas <= 0;
    const canH = avail ? avail.h : true;
    const canV = avail ? avail.v : true;
    const noDirs = !canH && !canV;

    if (noDirs || noFichas) {
      // Rock or line-blocked or no fichas — auto-skip, no UI needed
      guardSec.style.opacity = '0';
      guardSec.style.pointerEvents = 'none';
      waitingTurn.style.opacity = '0';
      waitingTurn.style.pointerEvents = 'none';
      send({type:'SKIP_GUARD'});
    } else {
      guardSec.style.opacity = '1';
      guardSec.style.pointerEvents = 'auto';
      waitingTurn.style.opacity = '0';
      waitingTurn.style.pointerEvents = 'none';
      // Hide buttons that are not available instead of greying out
      const btnH = document.getElementById('btn-guard-h');
      const btnV = document.getElementById('btn-guard-v');
      const divH = document.getElementById('guard-div-h');
      btnH.style.display = canH ? '' : 'none';
      if (divH) divH.style.display = canH ? '' : 'none';
      btnV.style.display = canV ? '' : 'none';
      document.getElementById('btn-guard-skip').disabled = false;
    }
  } else {
    guardSec.style.opacity = '0';
    guardSec.style.pointerEvents = 'none';
    waitingTurn.style.opacity = showWaiting ? '1' : '0';
    waitingTurn.style.pointerEvents = showWaiting ? 'auto' : 'none';
  }

  // Board
  renderBoard(state);
  // Objectives
  renderObjs(state);
  // Mobile layout sync
  if (typeof applyMobileLayout === 'function') applyMobileLayout();
}

function renderBoard(state) {
  const canvas = document.getElementById('board-canvas');
  canvas.innerHTML = '';
  const isMobile = window.innerWidth <= 600;
  const TILE_SIZE = isMobile ? 60 : 84;
  const GAP = isMobile ? 4 : 6;
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
    emojiEl.innerHTML = tileEmoji(tile);
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
  document.getElementById('end-winner').textContent = winner.name+' ganhou!';
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

  // Countdown to auto-return to lobby (15s matches server reset)
  const countdownEl = document.getElementById('end-countdown');
  if (countdownEl) {
    let secs = 15;
    countdownEl.textContent = 'A voltar ao lobby em '+secs+'s…';
    const iv = setInterval(() => {
      secs--;
      if (secs <= 0) { clearInterval(iv); countdownEl.textContent = ''; }
      else countdownEl.textContent = 'A voltar ao lobby em '+secs+'s…';
    }, 1000);
  }
}

document.getElementById('btn-restart').onclick = () => {
  inGame=false;
  send({type:'LOBBIES'});
  showScreen('screen-lobby');
  renderLobbyList(_cachedLobbies);
};

// ── Guard Buttons ──────────────────────────────────────────────────────────────
document.getElementById('btn-guard-h').onclick = () => send({type:'PLACE_GUARD', dir:'h'});
document.getElementById('btn-guard-v').onclick = () => send({type:'PLACE_GUARD', dir:'v'});
document.getElementById('btn-guard-skip').onclick = () => send({type:'SKIP_GUARD'});

// ── Mobile: objectives toggle ──────────────────────────────────────────────────
const mobObjsBtn = document.getElementById('btn-mob-objs');
const objInner = document.getElementById('obj-inner');
let mobObjsOpen = false;

function applyMobileLayout() {
  const isMobile = window.innerWidth <= 600;
  mobObjsBtn.style.display = isMobile ? 'flex' : 'none';
  if (isMobile) {
    if (!mobObjsOpen) objInner.classList.add('mob-hidden');
  } else {
    objInner.classList.remove('mob-hidden');
  }
}

mobObjsBtn.onclick = () => {
  mobObjsOpen = !mobObjsOpen;
  mobObjsBtn.textContent = mobObjsOpen ? 'Objetivos ▴' : 'Objetivos ▾';
  if (mobObjsOpen) {
    objInner.classList.remove('mob-hidden');
  } else {
    objInner.classList.add('mob-hidden');
  }
};

window.addEventListener('resize', applyMobileLayout);
applyMobileLayout();

document.getElementById('btn-leave-game').onclick = () => {
  if (!confirm('Sair do jogo? Vais perder a tua posição.')) return;
  send({type:'LEAVE_LOBBY'});
  sessionStorage.removeItem('pp_token');
  myToken=''; inGame=false; currentLobbyId='';
  send({type:'LOBBIES'});
  showScreen('screen-lobby');
};

// ── Rules Modal ────────────────────────────────────────────────────────────────
document.getElementById('btn-show-rules').onclick = () => {
  document.getElementById('modal-rules').classList.add('open');
};
document.getElementById('btn-modal-close').onclick = () => {
  document.getElementById('modal-rules').classList.remove('open');
};
document.getElementById('modal-rules').onclick = (e) => {
  if (e.target === document.getElementById('modal-rules'))
    document.getElementById('modal-rules').classList.remove('open');
};

// ── Tile Helpers ───────────────────────────────────────────────────────────────
function tileImgName(tile) {
  if (!tile.variantIdx) return null;
  if (tile.type === 'normal') return 'tile-normal-' + tile.bathers + '-' + tile.variantIdx + '.png';
  return 'tile-' + tile.type + '-' + tile.variantIdx + '.png';
}
function tileEmojiStr(tile) {
  if (tile.type==='rock') return '🪨';
  if (tile.type==='surf') return '🏄';
  if (tile.type==='sand') return '🏖️';
  if (tile.bathers===1) return '🧍';
  if (tile.bathers===2) return '👫';
  return '👨‍👩‍👦';
}
function tileEmoji(tile) {
  const img = tileImgName(tile);
  if (img) {
    const emo = tileEmojiStr(tile);
    return '<img src="/public/' + img + '" class="tile-img" alt="' + emo + '" onerror="this.outerHTML=\'<span>' + emo + '</span>\'">';
  }
  return tileEmojiStr(tile);
}
function tileLabel(tile) {
  if (tile.type==='rock') return 'Rocha';
  if (tile.type==='surf') return 'Prancha ×2';
  if (tile.type==='sand') return 'Areia';
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
    // If game is already over, free the slot immediately — no grace period needed
    if (!lobby.game || lobby.game.phase === 'GAME_OVER') {
      hardLeaveBySlot(lobby, seat);
      return;
    }
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
