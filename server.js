const express = require('express');
const http = require('http');
const path = require('path');
const fs = require('fs');
const { WebSocketServer } = require('ws');
const bcrypt = require('bcryptjs');
const { v4: uuidv4 } = require('uuid');

const PORT = process.env.PORT || 3000;
const HOST = '0.0.0.0';
const USERS_FILE = path.join(__dirname, 'users.json');
const MAX_PLAYERS_PER_ROOM = 4;
const MAX_ROOMS = 50;

let users = {};
if (fs.existsSync(USERS_FILE)) {
  try { users = JSON.parse(fs.readFileSync(USERS_FILE, 'utf-8')); } catch(e) { users = {}; }
}

function saveUsers() {
  fs.writeFileSync(USERS_FILE, JSON.stringify(users, null, 2));
}

const sessions = new Map();
const rooms = new Map();
const clients = new Map();

const TILE = 32;
const MAZE_W = 35;
const MAZE_H = 25;
const SLOW_SPEED = 1.4;
const NORMAL_SPEED = 2.2;
const MUMMY_SPEED = 1.0;
const MUMMY_CHASE_SPEED = 1.8;
const MUMMY_SIGHT = 6;
const BALL_PASS_RANGE = 8;

const COLORS = [
  '#4488ff','#44ff44','#ff44ff','#ff4444'
];

function generateMaze() {
  const maze = [];
  for (let y = 0; y < MAZE_H; y++) {
    maze[y] = [];
    for (let x = 0; x < MAZE_W; x++) maze[y][x] = 1;
  }
  function carve(x, y) {
    maze[y][x] = 0;
    const dirs = [[0,-2],[0,2],[-2,0],[2,0]];
    for (let i = dirs.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [dirs[i], dirs[j]] = [dirs[j], dirs[i]];
    }
    for (const [dx, dy] of dirs) {
      const nx = x + dx, ny = y + dy;
      if (nx > 0 && nx < MAZE_W - 1 && ny > 0 && ny < MAZE_H - 1 && maze[ny][nx] === 1) {
        maze[y + dy/2][x + dx/2] = 0;
        carve(nx, ny);
      }
    }
  }
  carve(1, 1);
  for (let y = 1; y < MAZE_H - 1; y++) {
    for (let x = 1; x < MAZE_W - 1; x++) {
      if (maze[y][x] === 1 && Math.random() < 0.08) {
        const hasOpen = (maze[y-1] && maze[y-1][x] === 0) ||
          (maze[y+1] && maze[y+1][x] === 0) ||
          (maze[y][x-1] === 0) || (maze[y][x+1] === 0);
        if (hasOpen) maze[y][x] = 0;
      }
    }
  }
  maze[1][1] = 0; maze[1][2] = 0; maze[2][1] = 0;
  return maze;
}

function canMove(maze, x, y) {
  const margin = 4;
  const checks = [
    [x + margin, y + margin],
    [x + TILE - margin - 1, y + margin],
    [x + margin, y + TILE - margin - 1],
    [x + TILE - margin - 1, y + TILE - margin - 1]
  ];
  for (const [cx, cy] of checks) {
    const tx = Math.floor(cx / TILE);
    const ty = Math.floor(cy / TILE);
    if (tx < 0 || tx >= MAZE_W || ty < 0 || ty >= MAZE_H) return false;
    if (maze[ty][tx] === 1) return false;
  }
  return true;
}

function lineOfSight(maze, x1, y1, x2, y2) {
  const dx = x2 - x1, dy = y2 - y1;
  const dist = Math.hypot(dx, dy);
  if (dist > MUMMY_SIGHT * TILE) return false;
  const steps = Math.ceil(dist / (TILE / 2));
  for (let i = 0; i <= steps; i++) {
    const t = i / steps;
    const cx = x1 + dx * t, cy = y1 + dy * t;
    const tx = Math.floor((cx + TILE/2) / TILE);
    const ty = Math.floor((cy + TILE/2) / TILE);
    if (tx < 0 || tx >= MAZE_W || ty < 0 || ty >= MAZE_H) return false;
    if (maze[ty][tx] === 1) return false;
  }
  return true;
}

function createGameState() {
  const maze = generateMaze();
  const spawns = [
    { x: 1, y: 1 }, { x: 1, y: 3 }, { x: 3, y: 1 },
    { x: 3, y: 3 }
  ];

  const mummySpawns = [
    { x: 10, y: 10 }, { x: 20, y: 5 }, { x: 15, y: 18 },
    { x: 25, y: 15 }, { x: 8, y: 20 }, { x: 28, y: 8 },
    { x: 30, y: 18 }, { x: 12, y: 22 }
  ];

  const mummies = mummySpawns.map(sp => {
    let fx = sp.x, fy = sp.y;
    while (maze[fy] && maze[fy][fx] === 1) { fx++; if (fx >= MAZE_W - 2) { fx = 1; fy++; } }
    const dirs = [[1,0],[-1,0],[0,1],[0,-1]];
    const validDirs = dirs.filter(([dx,dy]) => {
      const nx = fx + dx, ny = fy + dy;
      return nx >= 0 && nx < MAZE_W && ny >= 0 && ny < MAZE_H && maze[ny][nx] === 0;
    });
    const dir = validDirs.length > 0 ? validDirs[Math.floor(Math.random() * validDirs.length)] : [1,0];
    return {
      x: fx * TILE, y: fy * TILE,
      dirX: dir[0], dirY: dir[1],
      state: 'patrol', patrolTimer: 0,
      chaseTarget: null, alertTimer: 0
    };
  });

  return {
    maze,
    players: [],
    spawnIndex: 0,
    ball: { x: 5 * TILE, y: 5 * TILE, carried: false, carrier: null, active: false },
    lionStatue: { x: (MAZE_W - 2) * TILE, y: (MAZE_H - 2) * TILE, absorbed: false },
    doorOpen: false,
    doorX: (MAZE_W - 4) * TILE,
    doorY: (MAZE_H - 2) * TILE,
    key: { x: (MAZE_W - 2) * TILE, y: (MAZE_H - 3) * TILE, visible: false, collected: false },
    mummies,
    gameOver: false,
    winner: null,
    mummySpawnTimer: 0,
    tickCount: 0
  };
}

function createRoom(id) {
  const room = {
    id,
    state: createGameState(),
    playerConnections: new Map(),
    tickInterval: null
  };
  room.tickInterval = setInterval(() => {
    if (room.playerConnections.size === 0) {
      clearInterval(room.tickInterval);
      rooms.delete(id);
      return;
    }
    gameTick(room);
  }, 1000 / 20);
  return room;
}

function getOrCreateRoom() {
  for (const [id, room] of rooms) {
    if (room.playerConnections.size < MAX_PLAYERS_PER_ROOM) return room;
  }
  if (rooms.size >= MAX_ROOMS) return null;
  const id = `room_${uuidv4().slice(0,8)}`;
  const room = createRoom(id);
  rooms.set(id, room);
  return room;
}

function addPlayerToRoom(room, ws, username, color, token) {
  const state = room.state;
  const idx = state.spawnIndex % 4;
  const spawn = [
    { x: 1, y: 1 }, { x: 1, y: 3 }, { x: 3, y: 1 },
    { x: 3, y: 3 }
  ][state.spawnIndex % 4];
  state.spawnIndex++;

  const player = {
    id: uuidv4().slice(0,8),
    x: spawn.x * TILE,
    y: spawn.y * TILE,
    color: color || COLORS[state.players.length % COLORS.length],
    speed: NORMAL_SPEED,
    name: username,
    hasBall: false,
    inputDir: null,
    token
  };

  state.players.push(player);
  const conn = { ws, playerId: player.id, username, token };
  room.playerConnections.set(ws, conn);
  clients.set(ws, { roomId: room.id, playerId: player.id, token });

  const joinMsg = {
    type: 'joined',
    playerId: player.id,
    players: state.players.map(p => ({
      id: p.id, x: p.x, y: p.y, color: p.color, name: p.name, hasBall: p.hasBall
    })),
    maze: state.maze,
    ball: state.ball,
    lionStatue: state.lionStatue,
    doorOpen: state.doorOpen,
    doorX: state.doorX,
    doorY: state.doorY,
    key: { x: state.key.x, y: state.key.y, visible: state.key.visible, collected: state.key.collected },
    mummies: state.mummies.map(m => ({
      x: m.x, y: m.y, state: m.state, dirX: m.dirX, dirY: m.dirY
    }))
  };
  sendJSON(ws, joinMsg);

  broadcastToRoom(room, {
    type: 'player_joined',
    id: player.id, name: username, color: player.color,
    x: player.x, y: player.y
  }, ws);

  if (room.playerConnections.size >= 2 && !state.ball.active) {
    state.ball.active = true;
    broadcastToRoom(room, { type: 'ball_spawned', x: state.ball.x, y: state.ball.y });
  }

  return player;
}

function removePlayerFromRoom(room, ws) {
  const conn = room.playerConnections.get(ws);
  if (!conn) return;
  const playerId = conn.playerId;
  const state = room.state;
  const pIdx = state.players.findIndex(p => p.id === playerId);
  if (pIdx !== -1) {
    if (state.ball.carrier === state.players[pIdx].id) {
      state.ball.carried = false;
      state.ball.carrier = null;
    }
    state.players.splice(pIdx, 1);
  }
  room.playerConnections.delete(ws);
  clients.delete(ws);
  broadcastToRoom(room, { type: 'player_left', id: playerId });
}

function broadcastToRoom(room, msg, excludeWs) {
  const data = JSON.stringify(msg);
  for (const [ws, conn] of room.playerConnections) {
    if (ws === excludeWs) continue;
    if (ws.readyState === 1) ws.send(data);
  }
}

function sendJSON(ws, msg) {
  if (ws.readyState === 1) ws.send(JSON.stringify(msg));
}

function gameTick(room) {
  const state = room.state;
  if (state.gameOver) return;
  state.tickCount++;

  for (const m of state.mummies) {
    let targetPlayer = null;
    let minDist = Infinity;
    for (const p of state.players) {
      const dist = Math.hypot(p.x - m.x, p.y - m.y);
      if (dist < MUMMY_SIGHT * TILE && lineOfSight(state.maze, m.x, m.y, p.x, p.y)) {
        if (dist < minDist) { minDist = dist; targetPlayer = p; }
      }
    }
    if (targetPlayer) {
      m.state = 'chase'; m.chaseTarget = targetPlayer; m.alertTimer = 120;
    } else if (m.alertTimer > 0) {
      m.alertTimer--;
      if (m.alertTimer <= 0) { m.state = 'patrol'; m.chaseTarget = null; }
    }
    let speed = MUMMY_SPEED;
    let targetX, targetY;
    if (m.state === 'chase' && m.chaseTarget) {
      speed = MUMMY_CHASE_SPEED;
      targetX = m.chaseTarget.x; targetY = m.chaseTarget.y;
    } else {
      m.patrolTimer++;
      if (m.patrolTimer > 60 + Math.random() * 60) {
        m.patrolTimer = 0;
        const dirs = [[1,0],[-1,0],[0,1],[0,-1]];
        const validDirs = dirs.filter(([dx,dy]) => {
          const nx = Math.floor((m.x + dx * TILE) / TILE);
          const ny = Math.floor((m.y + dy * TILE) / TILE);
          return nx >= 0 && nx < MAZE_W && ny >= 0 && ny < MAZE_H && state.maze[ny][nx] === 0;
        });
        if (validDirs.length > 0) {
          const d = validDirs[Math.floor(Math.random() * validDirs.length)];
          m.dirX = d[0]; m.dirY = d[1];
        }
      }
      targetX = m.x + m.dirX * TILE; targetY = m.y + m.dirY * TILE;
    }
    const dx = targetX - m.x, dy = targetY - m.y;
    const dist = Math.hypot(dx, dy);
    if (dist > 1) {
      const nx = m.x + (dx / dist) * speed;
      const ny = m.y + (dy / dist) * speed;
      if (canMove(state.maze, nx, m.y)) m.x = nx;
      if (canMove(state.maze, m.x, ny)) m.y = ny;
    }
    for (const p of state.players) {
      if (Math.hypot(p.x - m.x, p.y - m.y) < TILE * 0.8) {
        state.gameOver = true;
        state.winner = null;
        broadcastToRoom(room, { type: 'game_over', reason: `A mummy caught ${p.name}!` });
        return;
      }
    }
  }

  for (const p of state.players) {
    if (p.inputDir) {
      const speed = p.hasBall ? SLOW_SPEED : NORMAL_SPEED;
      const [dx, dy] = p.inputDir;
      const nx = p.x + dx * speed;
      const ny = p.y + dy * speed;
      if (dx !== 0 && canMove(state.maze, nx, p.y)) p.x = nx;
      if (dy !== 0 && canMove(state.maze, p.x, ny)) p.y = ny;
    }
  }

  if (state.ball.carried && state.ball.carrier) {
    const carrier = state.players.find(p => p.id === state.ball.carrier);
    if (carrier) { state.ball.x = carrier.x; state.ball.y = carrier.y; }
  }

  if (!state.ball.carried && state.ball.active) {
    for (const p of state.players) {
      if (Math.hypot(p.x - state.ball.x, p.y - state.ball.y) < TILE) {
        state.ball.carried = true;
        state.ball.carrier = p.id;
        p.hasBall = true;
        broadcastToRoom(room, { type: 'ball_picked', playerId: p.id });
        break;
      }
    }
  }

  if (state.ball.carried && state.ball.carrier && !state.lionStatue.absorbed) {
    const carrier = state.players.find(p => p.id === state.ball.carrier);
    if (carrier && Math.hypot(carrier.x - state.lionStatue.x, carrier.y - state.lionStatue.y) < TILE * 1.5) {
      state.lionStatue.absorbed = true;
      state.ball.carried = false;
      state.ball.carrier = null;
      state.ball.active = false;
      if (carrier) { carrier.hasBall = false; }
      state.doorOpen = true;
      state.key.visible = true;
      state.maze[Math.floor(state.doorY / TILE)][Math.floor(state.doorX / TILE)] = 0;
      broadcastToRoom(room, {
        type: 'statue_activated',
        doorX: state.doorX, doorY: state.doorY,
        keyX: state.key.x, keyY: state.key.y
      });
    }
  }

  if (state.key.visible && !state.key.collected) {
    for (const p of state.players) {
      if (Math.hypot(p.x - state.key.x, p.y - state.key.y) < TILE) {
        state.key.collected = true;
        state.gameOver = true;
        state.winner = p.id;
        broadcastToRoom(room, { type: 'game_win', playerId: p.id, playerName: p.name });
        return;
      }
    }
  }

  if (state.tickCount % 3 === 0) {
    const updates = {
      type: 'state_update',
      players: state.players.map(p => ({
        id: p.id, x: Math.round(p.x), y: Math.round(p.y), hasBall: p.hasBall
      })),
      mummies: state.mummies.map(m => ({
        x: Math.round(m.x), y: Math.round(m.y), state: m.state
      })),
      ball: state.ball.carried ? null : { x: Math.round(state.ball.x), y: Math.round(state.ball.y) }
    };
    broadcastToRoom(room, updates);
  }
}

const app = express();
app.use(express.json());

app.use(express.static(path.join(__dirname, 'public')));

app.post('/api/register', (req, res) => {
  const { username, password } = req.body;
  if (!username || !password) return res.status(400).json({ error: 'Username and password required.' });
  if (username.length < 2) return res.status(400).json({ error: 'Username must be at least 2 characters.' });
  if (password.length < 4) return res.status(400).json({ error: 'Password must be at least 4 characters.' });
  if (users[username]) return res.status(409).json({ error: 'Username already taken.' });
  const hash = bcrypt.hashSync(password, 10);
  users[username] = { password: hash, created: Date.now() };
  saveUsers();
  res.json({ success: true, message: 'Account created!' });
});

app.post('/api/login', (req, res) => {
  const { username, password } = req.body;
  if (!username || !password) return res.status(400).json({ error: 'Username and password required.' });
  const user = users[username];
  if (!user) return res.status(401).json({ error: 'Invalid username or password.' });
  if (!bcrypt.compareSync(password, user.password)) return res.status(401).json({ error: 'Invalid username or password.' });
  const token = uuidv4();
  sessions.set(token, { username, createdAt: Date.now() });
  setTimeout(() => sessions.delete(token), 24 * 60 * 60 * 1000);
  res.json({ success: true, token, username });
});

app.get('/api/verify', (req, res) => {
  const token = req.headers.authorization;
  if (!token || !sessions.has(token)) return res.status(401).json({ error: 'Invalid token.' });
  res.json({ valid: true, username: sessions.get(token).username });
});

app.get('/api/stats', (req, res) => {
  res.json({
    totalPlayers: clients.size,
    totalRooms: rooms.size,
    maxCapacity: MAX_ROOMS * MAX_PLAYERS_PER_ROOM,
    rooms: Array.from(rooms.values()).map(r => ({
      id: r.id, players: r.playerConnections.size, maxPlayers: MAX_PLAYERS_PER_ROOM,
      gameActive: !r.state.gameOver, keyFound: r.state.key.collected
    }))
  });
});

const server = http.createServer(app);
const wss = new WebSocketServer({ server });

wss.on('connection', (ws, req) => {
  const urlParams = new URLSearchParams(req.url.slice(1) || '');
  const token = urlParams.get('token');
  if (!token || !sessions.has(token)) {
    sendJSON(ws, { type: 'error', message: 'Authentication required.' });
    ws.close();
    return;
  }
  const session = sessions.get(token);
  const username = session.username;

  const room = getOrCreateRoom();
  if (!room) {
    sendJSON(ws, { type: 'error', message: 'All rooms are full. Try again later.' });
    ws.close();
    return;
  }

  addPlayerToRoom(room, ws, username, null, token);

  ws.on('message', (data) => {
    try {
      const msg = JSON.parse(data);
      handleMessage(room, ws, msg);
    } catch(e) {}
  });

  ws.on('close', () => {
    const r = rooms.get(room.id);
    if (r) removePlayerFromRoom(r, ws);
  });

  ws.on('error', () => {
    const r = rooms.get(room.id);
    if (r) removePlayerFromRoom(r, ws);
  });
});

function handleMessage(room, ws, msg) {
  const conn = room.playerConnections.get(ws);
  if (!conn) return;
  const player = room.state.players.find(p => p.id === conn.playerId);
  if (!player) return;

  switch (msg.type) {
    case 'input':
      if (msg.dir) {
        player.inputDir = msg.dir;
      } else if (msg.dir === null) {
        player.inputDir = null;
      }
      break;

    case 'pass_ball':
      if (!room.state.ball.carried || room.state.ball.carrier !== player.id) return;
      if (!room.state.ball.active) return;
      let closest = null, closestDist = Infinity;
      for (const p of room.state.players) {
        if (p.id === player.id) continue;
        const dist = Math.hypot(p.x - player.x, p.y - player.y);
        if (dist < closestDist && dist < TILE * BALL_PASS_RANGE) {
          closestDist = dist; closest = p;
        }
      }
      if (closest) {
        player.hasBall = false;
        closest.hasBall = true;
        room.state.ball.carrier = closest.id;
        room.state.ball.x = closest.x;
        room.state.ball.y = closest.y;
        broadcastToRoom(room, { type: 'ball_passed', from: player.id, to: closest.id });
      }
      break;

    case 'chat':
      broadcastToRoom(room, { type: 'chat', from: player.name, message: msg.message });
      break;
  }
}

server.listen(PORT, HOST, () => {
  const addr = `http://localhost:${PORT}`;
  console.log('═══════════════════════════════════════');
  console.log('  PYRAMID MAZE — MULTIPLAYER SERVER');
  console.log('═══════════════════════════════════════');
  console.log(`  Server:   ${addr}`);
  console.log(`  Network:  http://YOUR_IP:${PORT}`);
  console.log(`  Players:  0 / ${MAX_ROOMS * MAX_PLAYERS_PER_ROOM}`);
  console.log(`  Rooms:    0 / ${MAX_ROOMS}`);
  console.log('═══════════════════════════════════════');
});
