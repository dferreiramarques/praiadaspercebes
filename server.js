const WebSocket = require('ws');
const http = require('http');
const fs = require('fs');
const path = require('path');

const PORT = process.env.PORT || 3000;
const MAX_LOBBIES = 5;
const GRACE_MS = 45000;
const AUTOPLAY_MS = 8000; // Auto-play for disconnected or bots

const MIME = {
  '.png': 'image/png', '.jpg': 'image/jpeg',
  '.webp': 'image/webp', '.svg': 'image/svg+xml',
  '.mp4': 'video/mp4', '.mp3': 'audio/mpeg',
  '.webmanifest': 'application/manifest+json',
  '.json': 'application/json', '.js': 'application/javascript',
};

const lobbies = {};
const wsState = new WeakMap();
const sessions = {};

function initLobbies() {
  for (let i = 1; i <= MAX_LOBBIES; i++) {
    const id = `LOBBY${i}`;
    lobbies[id] = {
      id,
      name: `Mesa ${i}`,
      maxPlayers: 4,
      players: Array(4).fill(null),
      names: Array(4).fill(''),
      tokens: Array(4).fill(null),
      game: null,
      graceTimers: Array(4).fill(null),
      autoTimers: Array(4).fill(null),
      solo: false,
    };
  }
}

initLobbies();

function serveStatic(req, res) {
  const safe = path.normalize(req.url).replace(/^(\.\.[\\/])+/, '');
  const file = path.join(__dirname, 'public', safe.replace(/^\//, ''));
  const ext = path.extname(file).toLowerCase();
  const mime = MIME[ext];
  if (!mime) { res.writeHead(404); res.end(); return; }
  fs.readFile(file, (err, data) => {
    if (err) { res.writeHead(404); res.end(); return; }
    res.writeHead(200, { 'Content-Type': mime, 'Cache-Control': 'public,max-age=86400' });
    res.end(data);
  });
}

function generateToken() {
  return Math.random().toString(36).substring(2) + Date.now().toString(36);
}

function shuffle(array) {
  for (let i = array.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [array[i], array[j]] = [array[j], array[i]];
  }
  return array;
}

const OBJECTIVES = [
  {id: 0, type: 'square3', points: 2, desc: 'Quadrado de 3×3 tiles (9 tiles)'},
  {id: 1, type: 'row5', points: 4, desc: 'Linha de 5 tiles'},
  {id: 2, type: 'row7', points: 6, desc: 'Linha de 7 tiles'},
  {id: 3, type: 'square5', points: 2, desc: 'Quadrado de 5×5 tiles (25 tiles)'},
  {id: 4, type: 'col5', points: 4, desc: 'Coluna de 5 tiles'},
  {id: 5, type: 'col7', points: 6, desc: 'Coluna de 7 tiles'},
  {id: 6, type: 'surfAdj', points: 4, desc: '2 Surfistas adjacentes'},
  {id: 7, type: 'batherExc', points: 6, desc: 'Excursão Banhista (2×2 tiles com 3 banhistas cada)'},
];

function newGame(lobby) {
  const humanSeats = lobby.players.map((ws, seat) => ws ? seat : null).filter(s => s !== null);
  const isSolo = humanSeats.length === 1;
  const n = isSolo ? 4 : humanSeats.length;
  const players = [];
  const bots = Array(n).fill(false);
  const activeLobbySeats = isSolo ? [humanSeats[0], -1, -2, -3] : humanSeats; // Negative for bots
  for (let i = 0; i < n; i++) {
    const ls = activeLobbySeats[i];
    const name = ls >= 0 ? lobby.names[ls] : `Bot ${i}`;
    players.push({
      name,
      remainingGuards: 8,
      placedGuards: 0,
      objectives: [],
      score: 0,
    });
    if (ls < 0) bots[i] = true;
  }

  const deck = createDeck();
  const board = {};
  const startTile = {bathers: 1, isSurf: false, isRock: false};
  board['0,0'] = {tile: startTile, lifeguard: null};

  const objDeck = shuffle(OBJECTIVES.map(o => o.id));
  const revealed = objDeck.splice(0, 4);

  return {
    players,
    n,
    bots,
    activeLobbySeats, // Map game seat to lobby seat (negative for bot)
    deck,
    board,
    currentTurn: 0, // Game seat
    currentTile: null,
    phase: 'PLAYING',
    revealedObjectives: revealed,
    objDeck,
    claimedObjectives: {}, // id: gameSeat
    turnGen: 0,
    isSolo,
    extraTurns: false,
    extraCount: 0,
    whoEnded: -1,
  };
}

function createDeck() {
  const deck = [];
  for (let i = 0; i < 20; i++) deck.push({bathers: 1, isSurf: false, isRock: false});
  for (let i = 0; i < 15; i++) deck.push({bathers: 2, isSurf: false, isRock: false});
  for (let i = 0; i < 8; i++) deck.push({bathers: 3, isSurf: false, isRock: false});
  for (let i = 0; i < 5; i++) deck.push({bathers: 1, isSurf: true, isRock: false});
  deck.push({bathers: 0, isSurf: false, isRock: true});
  return shuffle(deck);
}

function getBoardBounds(board) {
  const keys = Object.keys(board);
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  keys.forEach(k => {
    const [x, y] = k.split(',').map(Number);
    minX = Math.min(minX, x); minY = Math.min(minY, y);
    maxX = Math.max(maxX, x); maxY = Math.max(maxY, y);
  });
  return {minX, minY, maxX, maxY};
}

function isAdjacent(x, y, board) {
  const dirs = [[0,1],[0,-1],[1,0],[-1,0]];
  return dirs.some(([dx, dy]) => board[`${x+dx},${y+dy}`]);
}

function checkLineLimit(x, y, board) {
  let rowCount = 0, colCount = 0;
  Object.keys(board).forEach(k => {
    const [bx, by] = k.split(',').map(Number);
    if (by === y) rowCount++;
    if (bx === x) colCount++;
  });
  return rowCount < 7 && colCount < 7;
}

function placeTile(g, x, y, tile) {
  g.board[`${x},${y}`] = {tile, lifeguard: null};
}

function computeSegmentSum(g, px, py, orient) {
  const board = g.board;
  const dirs = orient === 'h' ? [[-1,0],[1,0]] : [[0,-1],[0,1]];
  let totalBathers = board[`${px},${py}`].tile.bathers;
  let numSurfs = board[`${px},${py}`].tile.isSurf ? 1 : 0;

  function sumDir(cx, cy, dx, dy) {
    let sumB = 0, surfs = 0;
    while (true) {
      cx += dx; cy += dy;
      const key = `${cx},${cy}`;
      if (!board[key]) break;
      const t = board[key].tile;
      if (t.isRock) break;
      sumB += t.bathers;
      if (t.isSurf) surfs++;
    }
    return {sumB, surfs};
  }

  dirs.forEach(([dx, dy]) => {
    const {sumB, surfs} = sumDir(px, py, dx, dy);
    totalBathers += sumB;
    numSurfs += surfs;
  });

  return totalBathers * (2 ** numSurfs);
}

function endGameScoring(g) {
  const lifeguards = [];
  Object.entries(g.board).forEach(([key, data]) => {
    if (data.lifeguard) {
      const [x, y] = key.split(',').map(Number);
      lifeguards.push({player: data.lifeguard.player, orient: data.lifeguard.orient, x, y});
    }
  });

  g.players.forEach(p => {
    p.score = 0;
  });

  lifeguards.forEach(lg => {
    const sum = computeSegmentSum(g, lg.x, lg.y, lg.orient);
    g.players[lg.player].score += sum;
  });

  g.players.forEach((p, i) => {
    p.score += 2 * p.remainingGuards;
    p.objectives.forEach(objId => {
      const obj = OBJECTIVES.find(o => o.id === objId);
      p.score += obj.points;
    });
  });

  g.phase = 'GAME_OVER';
}

function findWinner(g) {
  let maxScore = -Infinity;
  let winners = [];
  g.players.forEach((p, i) => {
    if (p.score > maxScore) {
      maxScore = p.score;
      winners = [i];
    } else if (p.score === maxScore) {
      winners.push(i);
    }
  });
  if (winners.length > 1) {
    let maxPlaced = -Infinity;
    let newWinners = [];
    winners.forEach(w => {
      const placed = g.players[w].placedGuards;
      if (placed > maxPlaced) {
        maxPlaced = placed;
        newWinners = [w];
      } else if (placed === maxPlaced) {
        newWinners.push(w);
      }
    });
    winners = newWinners;
  }
  return winners;
}

function checkObjectives(g, currentPlayer) {
  const board = g.board;
  const keys = Object.keys(board).map(k => k.split(',').map(Number));
  const {minX, minY, maxX, maxY} = getBoardBounds(board);

  // Group by rows and cols
  const rows = {};
  const cols = {};
  keys.forEach(([x, y]) => {
    if (!rows[y]) rows[y] = [];
    rows[y].push(x);
    if (!cols[x]) cols[x] = [];
    cols[x].push(y);
  });
  Object.values(rows).forEach(r => r.sort((a,b)=>a-b));
  Object.values(cols).forEach(c => c.sort((a,b)=>a-b));

  function hasLine(length, isRow) {
    const groups = isRow ? rows : cols;
    return Object.values(groups).some(group => group.length >= length);
  }

  function hasSquare(size) {
    const side = size === '3' ? 3 : 5;
    for (let sx = minX; sx <= maxX - side + 1; sx++) {
      for (let sy = minY; sy <= maxY - side + 1; sy++) {
        let filled = true;
        for (let i = 0; i < side; i++) {
          for (let j = 0; j < side; j++) {
            if (!board[`${sx+i},${sy+j}`]) {
              filled = false;
              break;
            }
          }
          if (!filled) break;
        }
        if (filled) return true;
      }
    }
    return false;
  }

  function hasSurfAdj() {
    const surfs = keys.filter(([x,y]) => board[`${x},${y}`].tile.isSurf);
    for (let i = 0; i < surfs.length; i++) {
      const [sx, sy] = surfs[i];
      for (let j = i+1; j < surfs.length; j++) {
        const [tx, ty] = surfs[j];
        if (Math.abs(sx - tx) + Math.abs(sy - ty) === 1) return true;
      }
    }
    return false;
  }

  function hasBatherExc() {
    for (let sx = minX; sx <= maxX - 1; sx++) {
      for (let sy = minY; sy <= maxY - 1; sy++) {
        const tiles = [
          board[`${sx},${sy}`], board[`${sx+1},${sy}`],
          board[`${sx},${sy+1}`], board[`${sx+1},${sy+1}`]
        ];
        if (tiles.every(t => t && t.tile.bathers === 3)) return true;
      }
    }
    return false;
  }

  const newClaimed = [];
  g.revealedObjectives.forEach((objId, idx) => {
    if (g.claimedObjectives[objId] !== undefined) return;
    const obj = OBJECTIVES.find(o => o.id === objId);
    let completed = false;
    switch (obj.type) {
      case 'square3': completed = hasSquare('3'); break;
      case 'square5': completed = hasSquare('5'); break;
      case 'row5': completed = hasLine(5, true); break;
      case 'row7': completed = hasLine(7, true); break;
      case 'col5': completed = hasLine(5, false); break;
      case 'col7': completed = hasLine(7, false); break;
      case 'surfAdj': completed = hasSurfAdj(); break;
      case 'batherExc': completed = hasBatherExc(); break;
    }
    if (completed) {
      g.claimedObjectives[objId] = currentPlayer;
      g.players[currentPlayer].objectives.push(objId);
      newClaimed.push(idx);
      if (g.objDeck.length > 0) {
        g.revealedObjectives.push(g.objDeck.shift());
      }
    }
  });
  // Remove claimed in reverse order
  newClaimed.sort((a,b)=>b-a).forEach(idx => g.revealedObjectives.splice(idx, 1));
}

function nextTurn(lobby) {
  const g = lobby.game;
  g.turnGen++;
  g.currentTurn = (g.currentTurn + 1) % g.n;

  if (g.extraTurns) {
    if (g.currentTurn === g.whoEnded) {
      // Skip the one who ended
      g.currentTurn = (g.currentTurn + 1) % g.n;
    }
    g.extraCount--;
    if (g.extraCount <= 0) {
      endGame(lobby);
      return;
    }
  }

  if (g.deck.length === 0) {
    endGame(lobby);
    return;
  }

  g.currentTile = g.deck.pop();

  const gs = g.currentTurn;
  const ls = g.activeLobbySeats[gs];
  if (g.bots[gs] || (ls >= 0 && !lobby.players[ls])) {
    // Bot or disconnected, schedule auto-play
    const gen = g.turnGen;
    lobby.autoTimers[ls >= 0 ? ls : 0] = setTimeout(() => {
      if (g.turnGen !== gen || g.phase !== 'PLAYING') return;
      botPlay(lobby);
    }, AUTOPLAY_MS);
  }

  broadcastGame(lobby);
}

function botPlay(lobby) {
  const g = lobby.game;
  const gs = g.currentTurn;

  // Find possible placements
  const possible = [];
  const {minX, minY, maxX, maxY} = getBoardBounds(g.board);
  for (let x = minX - 1; x <= maxX + 1; x++) {
    for (let y = minY - 1; y <= maxY + 1; y++) {
      const key = `${x},${y}`;
      if (!g.board[key] && isAdjacent(x, y, g.board) && checkLineLimit(x, y, g.board)) {
        possible.push({x, y});
      }
    }
  }

  if (possible.length === 0) {
    // Impossible, skip or end?
    nextTurn(lobby);
    return;
  }

  // Random placement
  const pos = possible[Math.floor(Math.random() * possible.length)];
  placeTile(g, pos.x, pos.y, g.currentTile);
  checkObjectives(g, gs);

  // Decide lifeguard
  if (g.currentTile.isRock || g.players[gs].remainingGuards === 0) {
    completeTurn(lobby);
    return;
  }

  // Random orient or none (50% place)
  const rand = Math.random();
  if (rand < 0.5) {
    completeTurn(lobby);
    return;
  }
  const orient = Math.random() < 0.5 ? 'h' : 'v';
  g.board[`${pos.x},${pos.y}`].lifeguard = {player: gs, orient};
  g.players[gs].remainingGuards--;
  g.players[gs].placedGuards++;
  completeTurn(lobby);
}

function completeTurn(lobby) {
  const g = lobby.game;
  const gs = g.currentTurn;

  // Check if this player now has 0 guards and extra not started
  if (!g.extraTurns && g.players[gs].remainingGuards === 0) {
    g.extraTurns = true;
    g.whoEnded = gs;
    g.extraCount = g.n - 1; // Others play one more
  }

  nextTurn(lobby);
}

function endGame(lobby) {
  const g = lobby.game;
  endGameScoring(g);
  const winners = findWinner(g);
  broadcastGame(lobby);
}

function findGameSeat(lobby, lobbySeat) {
  const g = lobby.game;
  if (!g) return -1;
  return g.activeLobbySeats.indexOf(lobbySeat);
}

function buildView(g, gameSeat) {
  const view = {
    mySeat: gameSeat,
    players: g.players.map(p => ({
      name: p.name,
      remainingGuards: p.remainingGuards,
      objectives: p.objectives.map(id => OBJECTIVES.find(o => o.id === id)),
      score: g.phase === 'GAME_OVER' ? p.score : undefined,
    })),
    n: g.n,
    board: Object.fromEntries(Object.entries(g.board).map(([k, v]) => [k, {
      tile: v.tile,
      lifeguard: v.lifeguard ? {player: v.lifeguard.player, orient: v.lifeguard.orient} : null,
    }])),
    deckSize: g.deck.length,
    currentTurn: g.currentTurn,
    myTile: gameSeat === g.currentTurn ? g.currentTile : null,
    phase: g.phase,
    revealedObjectives: g.revealedObjectives.map(id => OBJECTIVES.find(o => o.id === id)),
    claimedObjectives: Object.fromEntries(Object.entries(g.claimedObjectives).map(([id, p]) => [id, {player: p, obj: OBJECTIVES.find(o => o.id === Number(id))}])),
    isSolo: g.isSolo,
    winners: g.phase === 'GAME_OVER' ? findWinner(g) : null,
  };
  return view;
}

function broadcastGame(lobby) {
  const g = lobby.game;
  if (!g) return;
  lobby.players.forEach((ws, ls) => {
    if (ws) {
      const gs = findGameSeat(lobby, ls);
      if (gs !== -1) {
        sendTo(ws, { type: 'GAME_STATE', state: buildView(g, gs) });
      }
    }
  });
}

function lobbyInfo(lobby) {
  return {
    id: lobby.id,
    name: lobby.name,
    players: lobby.names.filter(n => n).length,
    max: lobby.maxPlayers,
    inGame: !!lobby.game,
  };
}

function broadcastLobbyList() {
  const list = Object.values(lobbies).map(lobbyInfo);
  for (const ws of wss.clients) {
    const st = wsState.get(ws);
    if (st && !st.lobbyId) {
      sendTo(ws, { type: 'LOBBIES', lobbies: list });
    }
  }
}

function sendTo(ws, msg) {
  if (ws.readyState === WebSocket.OPEN) {
    ws.send(JSON.stringify(msg));
  }
}

function handleJoin(ws, msg) {
  const {lobbyId, playerName} = msg;
  const name = (playerName || '').trim().slice(0, 20);
  if (!name) {
    sendTo(ws, { type: 'ERROR', text: 'Nome inválido' });
    return;
  }
  const lobby = lobbies[lobbyId];
  if (!lobby) return;
  const seat = lobby.players.findIndex(p => !p);
  if (seat === -1) return;
  lobby.players[seat] = ws;
  lobby.names[seat] = name;
  const token = generateToken();
  lobby.tokens[seat] = token;
  sessions[token] = {lobbyId, seat, name};
  wsState.set(ws, {lobbyId, seat, token});
  sendTo(ws, { type: 'JOINED', seat, token, lobbyId, solo: lobby.solo });
  broadcastLobbyState(lobby);
  broadcastLobbyList();
}

function broadcastLobbyState(lobby) {
  lobby.players.forEach((ws, seat) => {
    if (ws) {
      sendTo(ws, { type: 'LOBBY_STATE', names: lobby.names, mySeat: seat });
    }
  });
}

function handleReconnect(ws, msg) {
  const sess = sessions[msg.token];
  if (!sess) { sendTo(ws, { type: 'RECONNECT_FAIL' }); return; }
  const lobby = lobbies[sess.lobbyId];
  if (!lobby) { sendTo(ws, { type: 'RECONNECT_FAIL' }); return; }
  const { seat, name } = sess;

  const existing = lobby.players[seat];
  if (existing && existing.readyState === WebSocket.OPEN) {
    sendTo(ws, { type: 'RECONNECT_FAIL' }); return;
  }

  clearTimeout(lobby.graceTimers[seat]);
  lobby.players[seat] = ws;
  lobby.names[seat] = name;
  wsState.set(ws, {lobbyId: sess.lobbyId, seat, token: msg.token});
  sendTo(ws, { type: 'RECONNECTED', seat, name, solo: lobby.solo });
  broadcastLobbyState(lobby);
  if (lobby.game) broadcastGame(lobby);
}

function hardLeaveBySlot(lobby, seat) {
  lobby.players[seat] = null;
  lobby.names[seat] = '';
  lobby.tokens[seat] = null;
  broadcastLobbyState(lobby);
  broadcastLobbyList();
  if (lobby.game) {
    // If all disconnected, reset game?
    if (lobby.players.every(p => !p)) {
      lobby.game = null;
    }
  }
}

function handleAction(ws, msg) {
  if (msg.type === 'PING') { sendTo(ws, { type: 'PONG' }); return; }
  if (msg.type === 'LOBBIES') { sendTo(ws, { type: 'LOBBIES', lobbies: Object.values(lobbies).map(lobbyInfo) }); return; }
  if (msg.type === 'RECONNECT') { handleReconnect(ws, msg); return; }
  if (msg.type === 'JOIN_LOBBY') { handleJoin(ws, msg); return; }

  const st = wsState.get(ws);
  if (!st || !st.lobbyId) return;
  const lobby = lobbies[st.lobbyId];
  if (!lobby) return;
  const ls = st.seat;
  const g = lobby.game;

  switch (msg.type) {
    case 'START':
      if (g) return;
      lobby.game = newGame(lobby);
      nextTurn(lobby); // Start first turn
      broadcastGame(lobby);
      broadcastLobbyList();
      break;

    case 'PLACE':
      if (!g || g.phase !== 'PLAYING' || findGameSeat(lobby, ls) !== g.currentTurn) return;
      const {x, y} = msg;
      if (g.board[`${x},${y}`] || !isAdjacent(x, y, g.board) || !checkLineLimit(x, y, g.board)) return;
      if (g.deck.length === 0 && !g.currentTile) return; // Should not happen
      placeTile(g, x, y, g.currentTile);
      g.currentTile = null; // Placed
      checkObjectives(g, g.currentTurn);
      broadcastGame(lobby);
      break;

    case 'LIFEGUARD':
      if (!g || g.phase !== 'PLAYING' || findGameSeat(lobby, ls) !== g.currentTurn) return;
      const {orient, pos} = msg; // pos {x,y} of the just placed
      const key = `${pos.x},${pos.y}`;
      if (g.board[key].lifeguard || g.board[key].tile.isRock) return;
      if (orient !== 'none' && g.players[g.currentTurn].remainingGuards === 0) return;
      if (orient !== 'none') {
        g.board[key].lifeguard = {player: g.currentTurn, orient};
        g.players[g.currentTurn].remainingGuards--;
        g.players[g.currentTurn].placedGuards++;
      }
      completeTurn(lobby);
      break;

    case 'RESTART':
      if (g && g.phase === 'GAME_OVER') {
        lobby.game = null;
        broadcastGame(lobby);
        broadcastLobbyList();
      }
      break;

    case 'REQUEST_STATE':
      if (g) {
        const gs = findGameSeat(lobby, ls);
        if (gs !== -1) sendTo(ws, { type: 'GAME_STATE', state: buildView(g, gs) });
      } else {
        sendTo(ws, { type: 'LOBBY_STATE', names: lobby.names, mySeat: ls });
      }
      break;
  }
}

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

const wss = new WebSocket.Server({ server });

wss.on('connection', ws => {
  ws.on('message', data => {
    try {
      const msg = JSON.parse(data);
      handleAction(ws, msg);
    } catch (e) {}
  });

  ws.on('close', () => {
    const st = wsState.get(ws);
    if (!st) return;
    const lobby = lobbies[st.lobbyId];
    if (!lobby) return;
    const seat = st.seat;
    lobby.players[seat] = null;
    broadcastLobbyState(lobby);
    broadcastLobbyList();
    if (lobby.game) {
      const gs = findGameSeat(lobby, seat);
      if (gs !== -1 && g.currentTurn === gs) {
        // Auto-play if disconnected during turn
        lobby.autoTimers[seat] = setTimeout(() => botPlay(lobby), AUTOPLAY_MS);
      }
    }
    lobby.graceTimers[seat] = setTimeout(() => hardLeaveBySlot(lobby, seat), GRACE_MS);
  });

  sendTo(ws, { type: 'LOBBIES', lobbies: Object.values(lobbies).map(lobbyInfo) });
});

server.listen(PORT, () => console.log(`Server running on port ${PORT}`));

setInterval(() => {
  wss.clients.forEach(ws => {
    if (ws.readyState === WebSocket.OPEN) ws.ping();
  });
}, 20000);

const MANIFEST = `{
  "name": "Na Praia das Percebes",
  "short_name": "Percebes",
  "start_url": "/",
  "display": "standalone",
  "background_color": "#f8f2e2",
  "theme_color": "#c47c28",
  "icons": [
    {"src": "/icon.png", "sizes": "192x192", "type": "image/png"}
  ]
}`;

const SW = `self.addEventListener('fetch', e => {});`;

const CLIENT_HTML = `<!DOCTYPE html>
<html lang="pt">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Na Praia das Percebes</title>
  <link rel="manifest" href="/manifest.webmanifest">
  <meta name="theme-color" content="#c47c28">
  <meta name="apple-mobile-web-app-capable" content="yes">
  <style>
    body { margin: 0; font-family: sans-serif; background: #f8f2e2; color: #333; }
    .screen { display: none; position: absolute; top: 0; left: 0; width: 100%; height: 100%; flex-direction: column; align-items: center; justify-content: center; }
    .active { display: flex; }
    #board { position: relative; width: 80vw; height: 80vh; overflow: auto; }
    .tile { position: absolute; width: 50px; height: 50px; border: 1px solid #000; display: flex; align-items: center; justify-content: center; background: #fff; }
    .surf { background: #add8e6; }
    .rock { background: #808080; }
    .lifeguard { font-size: 20px; }
    .player-colors { --p0: red; --p1: blue; --p2: green; --p3: yellow; }
  </style>
</head>
<body>
  <div id="screen-name" class="screen active">
    <input id="inp-name" placeholder="Teu nome">
    <button onclick="submitName()">Entrar</button>
  </div>
  <div id="screen-lobby" class="screen">
    <div id="lobby-list"></div>
  </div>
  <div id="screen-game" class="screen">
    <div id="board"></div>
    <div id="my-tile"></div>
    <div id="objectives"></div>
    <div id="players"></div>
  </div>
  <script>
    let ws, myName = '', myToken = sessionStorage.getItem('token') || '', myLobbyId, mySeat;
    let _cachedLobbies = [];

    function connect() {
      ws = new WebSocket(location.origin.replace('http', 'ws'));
      ws.onopen = () => {
        if (myToken) ws.send(JSON.stringify({type: 'RECONNECT', token: myToken}));
      };
      ws.onmessage = msg => {
        const data = JSON.parse(msg.data);
        switch (data.type) {
          case 'LOBBIES': renderLobbyList(data.lobbies); break;
          case 'JOINED': 
            myToken = data.token;
            sessionStorage.setItem('token', myToken);
            myLobbyId = data.lobbyId;
            mySeat = data.seat;
            showScreen('screen-game');
            break;
          case 'LOBBY_STATE': renderLobbyState(data); break;
          case 'GAME_STATE': renderGame(data.state); break;
          case 'RECONNECTED': 
            myLobbyId = data.lobbyId;
            mySeat = data.seat;
            showScreen('screen-game');
            break;
          case 'RECONNECT_FAIL': 
            sessionStorage.removeItem('token');
            myToken = '';
            myName = '';
            showScreen('screen-name');
            break;
          case 'ERROR': alert(data.text); break;
        }
      };
      ws.onclose = () => setTimeout(connect, 1000);
    }
    connect();

    function showScreen(id) {
      document.querySelectorAll('.screen').forEach(s => s.classList.remove('active'));
      document.getElementById(id).classList.add('active');
    }

    function submitName() {
      myName = document.getElementById('inp-name').value.trim();
      if (!myName) return;
      ws.send(JSON.stringify({type: 'LOBBIES'}));
      showScreen('screen-lobby');
    }

    function renderLobbyList(lobbies) {
      _cachedLobbies = lobbies;
      if (!myName) return;
      const el = document.getElementById('lobby-list');
      el.innerHTML = lobbies.map(l => \`<div onclick="joinLobby('\${l.id}')">\${l.name} (\${l.players}/\${l.max})</div>\`).join('');
    }

    function joinLobby(id) {
      ws.send(JSON.stringify({type: 'JOIN_LOBBY', lobbyId: id, playerName: myName}));
    }

    function renderLobbyState(state) {
      // Show waiting room, start button if host (seat 0)
      const el = document.getElementById('lobby-list'); // Reuse
      el.innerHTML = state.names.map((n, i) => \`<div>\${n || 'Vazio'}</div>\`).join('');
      if (mySeat === 0) el.innerHTML += '<button onclick="startGame()">Começar</button>';
    }

    function startGame() {
      ws.send(JSON.stringify({type: 'START'}));
    }

    function renderGame(state) {
      const boardEl = document.getElementById('board');
      boardEl.innerHTML = '';
      const bounds = {minX: Infinity, minY: Infinity, maxX: -Infinity, maxY: -Infinity};
      Object.keys(state.board).forEach(k => {
        const [x, y] = k.split(',').map(Number);
        bounds.minX = Math.min(bounds.minX, x);
        bounds.minY = Math.min(bounds.minY, y);
        bounds.maxX = Math.max(bounds.maxX, x);
        bounds.maxY = Math.max(bounds.maxY, y);
      });
      const offsetX = -bounds.minX * 50 + 100;
      const offsetY = -bounds.minY * 50 + 100;
      Object.entries(state.board).forEach(([k, v]) => {
        const [x, y] = k.split(',').map(Number);
        const tileEl = document.createElement('div');
        tileEl.className = 'tile';
        tileEl.style.left = \`\${(x - bounds.minX) * 50}px\`;
        tileEl.style.top = \`\${(y - bounds.minY) * 50}px\`;
        let content = v.tile.bathers;
        if (v.tile.isSurf) content = 'S' + v.tile.bathers;
        if (v.tile.isRock) content = 'R';
        tileEl.innerText = content;
        if (v.tile.isSurf) tileEl.classList.add('surf');
        if (v.tile.isRock) tileEl.classList.add('rock');
        if (v.lifeguard) {
          const lgEl = document.createElement('span');
          lgEl.className = 'lifeguard';
          lgEl.style.color = \`var(--p\${v.lifeguard.player})\`;
          lgEl.innerText = v.lifeguard.orient === 'h' ? '←→' : '↑↓';
          tileEl.appendChild(lgEl);
        }
        if (state.myTile && state.currentTurn === state.mySeat) {
          tileEl.onclick = () => placeTile(x, y);
        }
        boardEl.appendChild(tileEl);
      });

      // Possible placements if my turn
      if (state.myTile && state.currentTurn === state.mySeat) {
        // Compute possible
        for (let x = bounds.minX - 1; x <= bounds.maxX + 1; x++) {
          for (let y = bounds.minY - 1; y <= bounds.maxY + 1; y++) {
            if (!state.board[\`\${x},\${y}\`] && isAdjacentClient(x, y, state.board) && checkLineLimitClient(x, y, state.board)) {
              const possibleEl = document.createElement('div');
              possibleEl.className = 'tile possible';
              possibleEl.style.left = \`\${(x - bounds.minX) * 50}px\`;
              possibleEl.style.top = \`\${(y - bounds.minY) * 50}px\`;
              possibleEl.style.background = 'lightgreen';
              possibleEl.onclick = () => sendPlace(x, y);
              boardEl.appendChild(possibleEl);
            }
          }
        }
        document.getElementById('my-tile').innerText = \`Teu tile: \${state.myTile.bathers} \${state.myTile.isSurf ? 'Surf' : ''} \${state.myTile.isRock ? 'Rock' : ''}\`;
      } else {
        document.getElementById('my-tile').innerText = '';
      }

      // Objectives
      document.getElementById('objectives').innerHTML = state.revealedObjectives.map(o => \`<div>\${o.desc} +\${o.points}</div>\`).join('');

      // Players
      document.getElementById('players').innerHTML = state.players.map((p, i) => \`<div style="color: var(--p\${i})">\${p.name}: Guards \${p.remainingGuards}, Objs \${p.objectives.length}</div>\`).join('');

      if (state.phase === 'GAME_OVER') {
        alert(\`Jogo terminado! Vencedor: \${state.winners.map(w => state.players[w].name).join(', ')}\`);
        // Add restart button if host
        if (mySeat === 0) document.getElementById('players').innerHTML += '<button onclick="restartGame()">Reiniciar</button>';
      }
    }

    function isAdjacentClient(x, y, board) {
      const dirs = [[0,1],[0,-1],[1,0],[-1,0]];
      return dirs.some(([dx, dy]) => board[\`\${x+dx},\${y+dy}\`]);
    }

    function checkLineLimitClient(x, y, board) {
      let row = 0, col = 0;
      Object.keys(board).forEach(k => {
        const [bx, by] = k.split(',').map(Number);
        if (by === y) row++;
        if (bx === x) col++;
      });
      return row < 7 && col < 7;
    }

    function sendPlace(x, y) {
      ws.send(JSON.stringify({type: 'PLACE', x, y}));
      // After place, show lifeguard choices
      setTimeout(() => {
        const choice = prompt('Salva-vidas: none, h, v');
        ws.send(JSON.stringify({type: 'LIFEGUARD', orient: choice, pos: {x, y}}));
      }, 100);
    }

    function restartGame() {
      ws.send(JSON.stringify({type: 'RESTART'}));
    }

    setInterval(() => ws.send(JSON.stringify({type: 'PING'})), 15000);
  </script>
</body>
</html>`;
