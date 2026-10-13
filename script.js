'use strict';
/* =====================================================================
   SINUCA (Bola 8) - HTML + CSS + JS
   - Modo Local: todos jogam no mesmo aparelho (revezando)
   - Modo Online: salas via PeerJS; o anfitrião roda a física e
     envia o estado para os outros jogadores
   ===================================================================== */

/* ---------- Constantes ---------- */
const W = 1000, H = 500, R = 14, RAIL = 50;
const CW = W + RAIL * 2, CH = H + RAIL * 2, TAU = Math.PI * 2;
const POCKETS = [
  { x: 0, y: 0, r: 30 }, { x: W / 2, y: 0, r: 27 }, { x: W, y: 0, r: 30 },
  { x: 0, y: H, r: 30 }, { x: W / 2, y: H, r: 27 }, { x: W, y: H, r: 30 }
];
const RX = W * 0.7, DX = Math.sqrt(3) * (R + 0.3);   // posição do triângulo
const COL = ['#f4f4f4', '#f5c400', '#1f55d6', '#e5252a', '#6c2fa8', '#f2790f', '#0e8a3d', '#8b1a1a', '#151515'];
const colorOf = id => COL[id > 8 ? id - 8 : id];
const typeOf = id => id === 0 ? 'cue' : id === 8 ? 'eight' : id < 8 ? 'solid' : 'stripe';
const $ = s => document.querySelector(s);
const shuffle = a => { for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; };

/* ---------- Estado global ---------- */
let G = null;              // estado do jogo
let mode = 'local';        // 'local' | 'online'
let isHost = false;        // anfitrião online
let myIdx = -1;            // índice do jogador neste aparelho (online)
let peer = null, hostConn = null, lobby = [], started = false, leaving = false;
let ptr = { x: W / 2, y: H / 2 };   // ponteiro em coordenadas da mesa
let hovering = false;

/* =====================================================================
   LÓGICA DO JOGO
   ===================================================================== */
function newGame(names) {
  const players = names.map((n, i) => ({ name: n, team: i % 2 }));
  const teamPlayers = [[], []];
  players.forEach((p, i) => teamPlayers[p.team].push(i));
  const g = {
    players, teamPlayers, ptr: [0, 0], balls: [], phase: 'aim', cur: 0,
    groups: [null, null], hand: false, breakDone: false,
    aim: 0, power: 55, msg: '', winner: null, shot: null, hx: null, hy: null
  };
  rack(g);
  g.cur = nextShooter(g, 0);
  g.msg = 'Quebra de abertura: mire no triângulo e taque.';
  autoAim(g);
  return g;
}

function rack(g) {
  const solids = shuffle([1, 2, 3, 4, 5, 6, 7]);
  const stripes = shuffle([9, 10, 11, 12, 13, 14, 15]);
  const slots = new Array(15).fill(0);
  slots[4] = 8;
  slots[10] = solids.pop();
  slots[14] = stripes.pop();
  const rest = shuffle(solids.concat(stripes));
  for (let i = 0; i < 15; i++) if (!slots[i]) slots[i] = rest.pop();
  const balls = [];
  balls[0] = { id: 0, x: W * 0.25, y: H / 2, vx: 0, vy: 0, in: false };
  let k = 0;
  for (let row = 0; row < 5; row++) {
    for (let c = 0; c <= row; c++) {
      const id = slots[k++];
      balls[id] = { id, x: RX + row * DX, y: H / 2 + (c - row / 2) * 2 * (R + 0.3), vx: 0, vy: 0, in: false };
    }
  }
  g.balls = balls;
}

function nextShooter(g, team) {
  const list = g.teamPlayers[team];
  const p = list[g.ptr[team] % list.length];
  g.ptr[team]++;
  return p;
}
const teamName = (g, t) => g.teamPlayers[t].map(i => g.players[i].name).join(' & ');

function autoAim(g) {
  const c = g.balls[0]; let best = null, bd = 1e9;
  for (const b of g.balls) {
    if (b.id === 0 || b.in) continue;
    const d = Math.hypot(b.x - c.x, b.y - c.y);
    if (d < bd) { bd = d; best = b; }
  }
  if (best) g.aim = Math.atan2(best.y - c.y, best.x - c.x);
}

function validPlace(g, x, y) {
  if (x < R || x > W - R || y < R || y > H - R) return false;
  for (const b of g.balls) if (b.id !== 0 && !b.in && Math.hypot(b.x - x, b.y - y) < 2 * R + 1) return false;
  for (const p of POCKETS) if (Math.hypot(p.x - x, p.y - y) < p.r + R * 0.6) return false;
  return true;
}

function freeSpot(g, x, y, skipId) {
  let guard = 0;
  while (guard++ < 60 && g.balls.some(b => !b.in && b.id !== skipId && Math.hypot(b.x - x, b.y - y) < 2 * R + 1)) {
    x += 2 * R + 1;
    if (x > W - R) { x = W * 0.25; y += 2 * R + 1; }
  }
  return [x, y];
}

function doShot(g, a, p) {
  if (g.phase !== 'aim' || g.hand) return false;
  const cue = g.balls[0];
  const v = Math.max(1.5, p / 100 * 30);
  cue.vx = Math.cos(a) * v; cue.vy = Math.sin(a) * v;
  g.aim = a; g.power = p;
  g.phase = 'moving';
  g.shot = { first: null, pocketed: [], rail: false };
  g.msg = '';
  return true;
}

function doPlace(g, x, y) {
  if (g.phase !== 'aim' || !g.hand || !validPlace(g, x, y)) return false;
  const c = g.balls[0];
  c.x = x; c.y = y; c.vx = c.vy = 0;
  g.hand = false; g.hx = g.hy = null;
  autoAim(g);
  g.msg = `${g.players[g.cur].name}: mire e taque.`;
  return true;
}

/* ---------- Física ---------- */
const E_WALL = 0.78, E_BALL = 0.96, SUB = 4;

function pot(g, b) {
  b.in = true; b.vx = b.vy = 0;
  if (g.shot) g.shot.pocketed.push(b.id);
}

function wallsAndPockets(g, b) {
  for (const p of POCKETS) {
    if (Math.hypot(b.x - p.x, b.y - p.y) < p.r) { pot(g, b); return; }
  }
  let zone = false;
  for (const p of POCKETS) if (Math.hypot(b.x - p.x, b.y - p.y) < p.r + 9) { zone = true; break; }
  if (!zone) {
    let hit = false;
    if (b.x < R) { b.x = R; b.vx = Math.abs(b.vx) * E_WALL; hit = true; }
    else if (b.x > W - R) { b.x = W - R; b.vx = -Math.abs(b.vx) * E_WALL; hit = true; }
    if (b.y < R) { b.y = R; b.vy = Math.abs(b.vy) * E_WALL; hit = true; }
    else if (b.y > H - R) { b.y = H - R; b.vy = -Math.abs(b.vy) * E_WALL; hit = true; }
    if (hit && g.shot && g.shot.first !== null) g.shot.rail = true;
  }
  if (b.x < -R || b.x > W + R || b.y < -R || b.y > H + R) pot(g, b);
}

function collide(g, a, b) {
  if (a.in || b.in) return;
  const dx = b.x - a.x, dy = b.y - a.y, d2 = dx * dx + dy * dy, min = 2 * R;
  if (d2 >= min * min || d2 === 0) return;
  const d = Math.sqrt(d2), nx = dx / d, ny = dy / d, ov = (min - d) / 2;
  a.x -= nx * ov; a.y -= ny * ov; b.x += nx * ov; b.y += ny * ov;
  const rv = (b.vx - a.vx) * nx + (b.vy - a.vy) * ny;
  if (rv < 0) {
    const j = -(1 + E_BALL) * rv / 2;
    a.vx -= j * nx; a.vy -= j * ny; b.vx += j * nx; b.vy += j * ny;
  }
  if (g.shot && g.shot.first === null) {
    if (a.id === 0) g.shot.first = b.id; else if (b.id === 0) g.shot.first = a.id;
  }
}

function step(g) {
  const balls = g.balls;
  for (let s = 0; s < SUB; s++) {
    for (const b of balls) {
      if (b.in) continue;
      b.x += b.vx / SUB; b.y += b.vy / SUB;
      wallsAndPockets(g, b);
    }
    for (let i = 0; i < balls.length; i++) for (let j = i + 1; j < balls.length; j++) collide(g, balls[i], balls[j]);
    for (const b of balls) {
      if (b.in) continue;
      const sp = Math.hypot(b.vx, b.vy);
      if (sp < 0.05) { b.vx = b.vy = 0; continue; }
      const ns = Math.max(0, sp * 0.99649 - 0.00625), k = ns / sp;
      b.vx *= k; b.vy *= k;
    }
  }
}
const anyMoving = g => g.balls.some(b => !b.in && (b.vx !== 0 || b.vy !== 0));

/* ---------- Regras (bola 8) ---------- */
function finish(g, team, why) {
  g.phase = 'over'; g.winner = team; g.shot = null;
  g.msg = why;
}

function evaluate(g) {
  const sh = g.shot, team = g.players[g.cur].team, opp = 1 - team, pt = sh.pocketed;
  const objPot = pt.filter(i => i !== 0);
  const myGrp = g.groups[team];
  const wasBreak = !g.breakDone;
  const before = myGrp ? g.balls.filter(b => typeOf(b.id) === myGrp && (!b.in || pt.includes(b.id))).length : 99;
  const onEight = !!myGrp && before === 0;

  let foul = null;
  if (pt.includes(0)) foul = 'a bola branca caiu';
  else if (sh.first === null) foul = 'nenhuma bola foi tocada';
  else if (myGrp) {
    const want = onEight ? 'eight' : myGrp;
    if (typeOf(sh.first) !== want) foul = onEight ? 'era a vez da bola 8' : 'bola errada tocada primeiro';
  } else if (sh.first === 8) foul = 'bola 8 tocada primeiro';
  if (!foul && !objPot.length && !sh.rail) foul = 'nenhuma bola tocou a tabela';

  if (pt.includes(8)) {
    if (wasBreak) {
      const b8 = g.balls[8];
      const [x, y] = freeSpot(g, RX + 2 * DX, H / 2, 8);
      b8.x = x; b8.y = y; b8.in = false;
      objPot.splice(objPot.indexOf(8), 1);
    } else {
      const ok = !foul && onEight;
      finish(g, ok ? team : opp, ok
        ? `${teamName(g, team)} encaçapou a bola 8.`
        : (foul ? `A bola 8 caiu com falta (${foul}).` : 'A bola 8 caiu antes da hora.'));
      return;
    }
  }

  let msg = '';
  if (!myGrp && !foul && !wasBreak) {
    const f = objPot.find(i => i !== 8);
    if (f) {
      const t = typeOf(f);
      g.groups[team] = t; g.groups[opp] = t === 'solid' ? 'stripe' : 'solid';
      msg = `${teamName(g, team)} ficou com as ${t === 'solid' ? 'lisas' : 'listradas'}. `;
    }
  }
  const grp = g.groups[team];
  const potOwn = !foul && objPot.some(i => i !== 8 && (!grp || typeOf(i) === grp));
  g.breakDone = true;

  const cue = g.balls[0];
  if (cue.in) {
    cue.in = false; cue.vx = cue.vy = 0;
    const [x, y] = freeSpot(g, W * 0.25, H / 2, 0);
    cue.x = x; cue.y = y;
  }
  if (foul) {
    g.cur = nextShooter(g, opp); g.hand = true;
    msg += `Falta: ${foul}. Bola na mão para ${g.players[g.cur].name}.`;
  } else if (potOwn) {
    msg += `${g.players[g.cur].name} continua jogando.`;
  } else {
    g.cur = nextShooter(g, opp);
    msg += `Vez de ${g.players[g.cur].name}.`;
  }
  g.msg = msg; g.phase = 'aim'; g.shot = null; g.hx = g.hy = null;
  autoAim(g);
}

/* =====================================================================
   DESENHO
   ===================================================================== */
const cv = $('#cv'), ctx = cv.getContext('2d'), stage = $('#stage');
const NEON = '#19f0ff', PINK = '#ff3df2';
let rot = false;   // true = mesa girada (celular na vertical)

function layout() {
  rot = window.innerHeight > window.innerWidth * 1.02;
  const w = rot ? CH : CW, h = rot ? CW : CH;
  if (cv.width !== w || cv.height !== h) { cv.width = w; cv.height = h; }
  const bw = stage.clientWidth, bh = stage.clientHeight;
  if (!bw || !bh) return;
  const s = Math.min(bw / w, bh / h);
  cv.style.width = Math.floor(w * s) + 'px';
  cv.style.height = Math.floor(h * s) + 'px';
}
window.addEventListener('resize', layout);
window.addEventListener('orientationchange', () => setTimeout(layout, 200));
if (window.ResizeObserver) new ResizeObserver(layout).observe(stage);

const tableImg = buildTable();

function rr(c, x, y, w, h, r) {
  c.beginPath(); c.moveTo(x + r, y);
  c.arcTo(x + w, y, x + w, y + h, r); c.arcTo(x + w, y + h, x, y + h, r);
  c.arcTo(x, y + h, x, y, r); c.arcTo(x, y, x + w, y, r); c.closePath();
}

function buildTable() {
  const c = document.createElement('canvas'); c.width = CW; c.height = CH;
  const x = c.getContext('2d');
  // borda (trilho) em grafite com contorno neon
  let gr = x.createLinearGradient(0, 0, 0, CH);
  gr.addColorStop(0, '#26304a'); gr.addColorStop(1, '#090d17');
  x.fillStyle = gr; rr(x, 0, 0, CW, CH, 30); x.fill();
  x.save(); x.shadowColor = NEON; x.shadowBlur = 12; x.lineWidth = 3; x.strokeStyle = NEON;
  rr(x, 3, 3, CW - 6, CH - 6, 28); x.stroke(); x.restore();
  x.strokeStyle = 'rgba(25,240,255,.2)'; x.lineWidth = 1; rr(x, 12, 12, CW - 24, CH - 24, 22); x.stroke();
  // tabela (cushion)
  x.fillStyle = '#0b4f86'; x.fillRect(RAIL - 13, RAIL - 13, W + 26, H + 26);
  x.strokeStyle = 'rgba(25,240,255,.8)'; x.lineWidth = 2; x.strokeRect(RAIL - 13, RAIL - 13, W + 26, H + 26);
  // feltro
  gr = x.createRadialGradient(CW / 2, CH / 2, 40, CW / 2, CH / 2, CW * 0.6);
  gr.addColorStop(0, '#12609c'); gr.addColorStop(1, '#06223f');
  x.fillStyle = gr; x.fillRect(RAIL, RAIL, W, H);
  x.strokeStyle = 'rgba(25,240,255,.07)'; x.lineWidth = 1;
  for (let i = 0; i <= W; i += 50) { x.beginPath(); x.moveTo(RAIL + i, RAIL); x.lineTo(RAIL + i, RAIL + H); x.stroke(); }
  for (let j = 0; j <= H; j += 50) { x.beginPath(); x.moveTo(RAIL, RAIL + j); x.lineTo(RAIL + W, RAIL + j); x.stroke(); }
  // marcações
  x.save(); x.setLineDash([8, 8]); x.strokeStyle = 'rgba(25,240,255,.35)'; x.lineWidth = 2;
  x.beginPath(); x.moveTo(RAIL + W * 0.25, RAIL); x.lineTo(RAIL + W * 0.25, RAIL + H); x.stroke(); x.restore();
  x.fillStyle = 'rgba(25,240,255,.6)';
  x.beginPath(); x.arc(RAIL + RX + 2 * DX, RAIL + H / 2, 3, 0, TAU); x.fill();
  // caçapas
  for (const p of POCKETS) {
    const ox = p.x === 0 ? -6 : p.x === W ? 6 : 0, oy = p.y === 0 ? -6 : p.y === H ? 6 : 0;
    const rad = p.r === 30 ? 28 : 24, cx = RAIL + p.x + ox, cy = RAIL + p.y + oy;
    x.save(); x.shadowColor = PINK; x.shadowBlur = 10; x.strokeStyle = PINK; x.lineWidth = 3;
    x.beginPath(); x.arc(cx, cy, rad + 3, 0, TAU); x.stroke(); x.restore();
    x.fillStyle = '#02040a'; x.beginPath(); x.arc(cx, cy, rad, 0, TAU); x.fill();
  }
  // diamantes
  x.fillStyle = NEON;
  const m = (RAIL - 13) / 2;
  for (let i = 1; i < 8; i++) {
    if (i === 4) continue;
    const px = RAIL + W * i / 8;
    x.beginPath(); x.arc(px, m, 3.5, 0, TAU); x.arc(px, CH - m, 3.5, 0, TAU); x.fill();
  }
  for (let i = 1; i < 4; i++) {
    const py = RAIL + H * i / 4;
    x.beginPath(); x.arc(m, py, 3.5, 0, TAU); x.arc(CW - m, py, 3.5, 0, TAU); x.fill();
  }
  return c;
}

function drawBall(b, x, y, alpha) {
  const col = colorOf(b.id), stripe = b.id > 8;
  ctx.save();
  ctx.globalAlpha = alpha;
  ctx.fillStyle = 'rgba(0,0,0,.38)';
  ctx.beginPath(); ctx.arc(x + 2, y + 3, R, 0, TAU); ctx.fill();
  if (b.id === 0) { ctx.shadowColor = NEON; ctx.shadowBlur = 12; }
  ctx.fillStyle = stripe ? '#f2f6fb' : col;
  ctx.beginPath(); ctx.arc(x, y, R, 0, TAU); ctx.fill();
  ctx.shadowBlur = 0;
  if (stripe) {
    ctx.save(); ctx.beginPath(); ctx.arc(x, y, R, 0, TAU); ctx.clip();
    ctx.fillStyle = col; ctx.fillRect(x - R, y - R * 0.6, 2 * R, R * 1.2); ctx.restore();
  }
  if (b.id > 0) {
    ctx.fillStyle = '#fff'; ctx.beginPath(); ctx.arc(x, y, R * 0.5, 0, TAU); ctx.fill();
    ctx.save(); ctx.translate(x, y); if (rot) ctx.rotate(-Math.PI / 2);
    ctx.fillStyle = '#111'; ctx.font = 'bold 9px Arial'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText(b.id, 0, 0.5); ctx.restore();
  }
  const sh = ctx.createRadialGradient(x - 5, y - 6, 1, x - 3, y - 4, R);
  sh.addColorStop(0, 'rgba(255,255,255,.75)'); sh.addColorStop(.35, 'rgba(255,255,255,0)');
  ctx.fillStyle = sh; ctx.beginPath(); ctx.arc(x, y, R, 0, TAU); ctx.fill();
  ctx.strokeStyle = 'rgba(255,255,255,.22)'; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.arc(x, y, R - 0.5, 0, TAU); ctx.stroke();
  ctx.restore();
}

function rayCast(g, x, y, dx, dy) {
  let best = { t: 1e9, ball: null };
  const walls = [];
  if (dx > 0) walls.push((W - R - x) / dx); else if (dx < 0) walls.push((R - x) / dx);
  if (dy > 0) walls.push((H - R - y) / dy); else if (dy < 0) walls.push((R - y) / dy);
  for (const t of walls) if (t > 0 && t < best.t) best = { t, ball: null };
  for (const b of g.balls) {
    if (b.id === 0 || b.in) continue;
    const fx = x - b.x, fy = y - b.y, bb = fx * dx + fy * dy, c = fx * fx + fy * fy - 4 * R * R, disc = bb * bb - c;
    if (disc < 0) continue;
    const t = -bb - Math.sqrt(disc);
    if (t > 0 && t < best.t) best = { t, ball: b };
  }
  return best;
}

function drawAim(g) {
  const c = g.balls[0], a = g.aim, dx = Math.cos(a), dy = Math.sin(a);
  const hit = rayCast(g, c.x, c.y, dx, dy);
  const gx = c.x + dx * hit.t, gy = c.y + dy * hit.t;
  ctx.save();
  ctx.shadowColor = NEON; ctx.shadowBlur = 8;
  ctx.setLineDash([8, 7]); ctx.lineWidth = 2; ctx.strokeStyle = 'rgba(200,250,255,.95)';
  ctx.beginPath(); ctx.moveTo(c.x + dx * R, c.y + dy * R); ctx.lineTo(gx, gy); ctx.stroke();
  ctx.setLineDash([]);
  ctx.beginPath(); ctx.arc(gx, gy, R, 0, TAU); ctx.stroke();
  if (hit.ball) {
    let nx = hit.ball.x - gx, ny = hit.ball.y - gy; const n = Math.hypot(nx, ny) || 1; nx /= n; ny /= n;
    ctx.setLineDash([6, 6]);
    ctx.beginPath(); ctx.moveTo(hit.ball.x, hit.ball.y); ctx.lineTo(hit.ball.x + nx * 70, hit.ball.y + ny * 70); ctx.stroke();
    const dot = dx * nx + dy * ny; const tx = dx - dot * nx, ty = dy - dot * ny, tl = Math.hypot(tx, ty);
    if (tl > 0.05) {
      ctx.shadowColor = PINK; ctx.strokeStyle = 'rgba(255,140,250,.9)';
      ctx.beginPath(); ctx.moveTo(gx, gy); ctx.lineTo(gx + tx / tl * 45, gy + ty / tl * 45); ctx.stroke();
    }
  }
  ctx.restore();
  // taco
  const off = R + 6 + g.power / 100 * 60, len = 330;
  const x1 = c.x - dx * off, y1 = c.y - dy * off, x2 = c.x - dx * (off + len), y2 = c.y - dy * (off + len);
  const gr = ctx.createLinearGradient(x1, y1, x2, y2);
  gr.addColorStop(0, '#d9f7ff'); gr.addColorStop(.12, NEON); gr.addColorStop(.3, '#bcc9e0'); gr.addColorStop(.75, '#39435c'); gr.addColorStop(1, '#0c111c');
  ctx.save(); ctx.lineCap = 'round';
  ctx.strokeStyle = 'rgba(0,0,0,.35)'; ctx.lineWidth = 8;
  ctx.beginPath(); ctx.moveTo(x1 + 3, y1 + 4); ctx.lineTo(x2 + 3, y2 + 4); ctx.stroke();
  ctx.shadowColor = NEON; ctx.shadowBlur = 8;
  ctx.strokeStyle = gr; ctx.lineWidth = 7;
  ctx.beginPath(); ctx.moveTo(x1, y1); ctx.lineTo(x2, y2); ctx.stroke();
  ctx.restore();
}

function draw() {
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.clearRect(0, 0, cv.width, cv.height);
  if (rot) ctx.setTransform(0, 1, -1, 0, CH, 0);   // gira 90° para telas em pé
  ctx.drawImage(tableImg, 0, 0);
  if (!G) return;
  ctx.save(); ctx.translate(RAIL, RAIL);
  const ctrl = canControl(), placing = G.phase === 'aim' && G.hand;
  for (const b of G.balls) {
    if (b.in) continue;
    if (b.id === 0 && placing) {
      let p = null, ok = true;
      if (ctrl && hovering) { p = { x: Math.min(W - R, Math.max(R, ptr.x)), y: Math.min(H - R, Math.max(R, ptr.y)) }; ok = validPlace(G, p.x, p.y); }
      else if (G.hx != null) p = { x: G.hx, y: G.hy };
      else p = b;
      drawBall(b, p.x, p.y, ok ? 0.85 : 0.4);
      ctx.strokeStyle = ok ? '#b6ff3c' : '#ff4d6d'; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.arc(p.x, p.y, R + 4, 0, TAU); ctx.stroke();
      continue;
    }
    drawBall(b, b.x, b.y, 1);
  }
  if (G.phase === 'aim' && !G.hand) drawAim(G);
  ctx.restore();
}

/* =====================================================================
   HUD
   ===================================================================== */
let lastKey = '';
function updateHud(force) {
  const g = G; if (!g) return;
  const key = JSON.stringify([g.cur, g.groups, g.balls.map(b => b.in ? 1 : 0).join(''), g.msg, g.phase, g.winner, g.hand, myIdx]);
  if (key !== lastKey || force) {
    lastKey = key;
    const over = g.phase === 'over';
    for (const t of [0, 1]) {
      const el = $('#team' + t);
      el.classList.toggle('active', !over && g.players[g.cur].team === t);
      el.querySelector('.tname').textContent = 'Time ' + (t ? 'B' : 'A');
      el.querySelector('.names').replaceChildren(...g.teamPlayers[t].map(i => {
        const s = document.createElement('span');
        s.textContent = g.players[i].name + (mode === 'online' && i === myIdx ? ' (você)' : '');
        if (!over && i === g.cur) s.className = 'shooter';
        return s;
      }));
      const grp = g.groups[t];
      el.querySelector('.grp').textContent = grp ? (grp === 'solid' ? 'Lisas' : 'Listradas') : 'Mesa aberta';
      const bx = el.querySelector('.balls'); bx.replaceChildren();
      for (let k = 1; k <= 7; k++) {
        const d = document.createElement('i');
        if (!grp) d.className = 'mini ghost';
        else {
          const id = grp === 'stripe' ? k + 8 : k;
          d.className = 'mini ' + grp + (g.balls[id].in ? ' out' : '');
          d.style.setProperty('--c', colorOf(id));
        }
        bx.appendChild(d);
      }
    }
    $('#turn').textContent = over ? 'Fim de jogo' : `Vez de ${g.players[g.cur].name}`;
    $('#msg').textContent = g.msg;
    $('#end').classList.toggle('show', over);
    if (over) {
      $('#endTitle').textContent = g.winner === null ? 'Partida encerrada' : `${teamName(g, g.winner)} venceu!`;
      $('#endMsg').textContent = g.msg;
      $('#again').style.display = (mode === 'online' && !isHost) ? 'none' : '';
    }
  }
  const can = canControl();
  const pw = $('#power'); if (pw.disabled === can) pw.disabled = !can;
  const fb = $('#fire'); const fd = !(can && !g.hand); if (fb.disabled !== fd) fb.disabled = fd;
  if (!can || document.activeElement !== pw) { pw.value = g.power; }
  $('#powVal').textContent = Math.round(g.power);
}

function toast(t) {
  const el = $('#toast'); el.textContent = t; el.classList.add('show');
  clearTimeout(toast.t); toast.t = setTimeout(() => el.classList.remove('show'), 2600);
}

/* =====================================================================
   ENTRADA (mouse / toque / teclado)
   ===================================================================== */
const authority = () => mode === 'local' || isHost;
const canControl = () => !!G && G.phase === 'aim' && (mode === 'local' || G.cur === myIdx);

function toTable(e) {
  const r = cv.getBoundingClientRect();
  const cx = (e.clientX - r.left) * cv.width / r.width, cy = (e.clientY - r.top) * cv.height / r.height;
  return rot ? { x: cy - RAIL, y: CH - cx - RAIL } : { x: cx - RAIL, y: cy - RAIL };
}

function pointerUpdate(e) {
  ptr = toTable(e); hovering = true;
  if (!canControl()) return;
  if (!G.hand) {
    const c = G.balls[0];
    if (Math.hypot(ptr.x - c.x, ptr.y - c.y) > 4) G.aim = Math.atan2(ptr.y - c.y, ptr.x - c.x);
  }
  sendAim();
}
cv.addEventListener('pointermove', pointerUpdate);
cv.addEventListener('pointerleave', () => { hovering = false; });
cv.addEventListener('pointerdown', e => {
  try { cv.setPointerCapture(e.pointerId); } catch (_) { }
  pointerUpdate(e);
});
cv.addEventListener('pointerup', e => {
  ptr = toTable(e);
  if (canControl() && G.hand) tryPlace(ptr.x, ptr.y);
  if (e.pointerType !== 'mouse') hovering = false;
});

function tryPlace(x, y) {
  x = Math.min(W - R, Math.max(R, x)); y = Math.min(H - R, Math.max(R, y));
  if (!validPlace(G, x, y)) { toast('Posição inválida'); return; }
  if (authority()) { if (doPlace(G, x, y)) pushState(); }
  else hostConn.send({ t: 'place', x, y });
}

function fire() {
  if (!canControl() || G.hand) return;
  if (authority()) { if (doShot(G, G.aim, G.power)) pushState(); }
  else hostConn.send({ t: 'shot', a: G.aim, p: G.power });
}

$('#fire').addEventListener('click', fire);
$('#power').addEventListener('input', e => { if (canControl()) { G.power = +e.target.value; sendAim(true); } });
document.addEventListener('keydown', e => {
  if (!G || e.target.type === 'text') return;
  if (e.code === 'Space' || e.code === 'Enter') { if (e.target.tagName !== 'BUTTON') { e.preventDefault(); fire(); } return; }
  if (!canControl() || G.hand) return;
  const fine = e.shiftKey ? 0.002 : 0.01;
  if (e.key === 'ArrowLeft') { G.aim -= fine; sendAim(); e.preventDefault(); }
  else if (e.key === 'ArrowRight') { G.aim += fine; sendAim(); e.preventDefault(); }
  else if (e.key === 'ArrowUp') { G.power = Math.min(100, G.power + 3); sendAim(true); e.preventDefault(); }
  else if (e.key === 'ArrowDown') { G.power = Math.max(5, G.power - 3); sendAim(true); e.preventDefault(); }
});

/* =====================================================================
   LOOP PRINCIPAL
   ===================================================================== */
let last = 0, acc = 0, frame = 0;
function loop(t) {
  requestAnimationFrame(loop);
  const dt = Math.min(100, t - last); last = t; acc += dt;
  if (!G) return;
  let n = 0;
  while (acc >= 16.667 && n < 5) { acc -= 16.667; n++; tick(); }
  draw(); updateHud();
}
function tick() {
  if (G.phase !== 'moving') return;
  step(G); frame++;
  if (authority()) {
    if (!anyMoving(G)) { evaluate(G); pushState(); }
    else if (mode === 'online' && frame % 2 === 0) pushState();
  }
}
requestAnimationFrame(loop);

/* =====================================================================
   ONLINE (PeerJS)
   ===================================================================== */
const snapshot = g => ({
  ...g,
  balls: g.balls.map(b => ({ id: b.id, x: +b.x.toFixed(2), y: +b.y.toFixed(2), vx: +b.vx.toFixed(3), vy: +b.vy.toFixed(3), in: b.in }))
});
function pushState() { if (mode === 'online' && isHost) bcast({ t: 'state', g: snapshot(G) }); }
function bcast(m, except) { lobby.forEach(l => { if (l.conn && l.conn !== except && l.conn.open) l.conn.send(m); }); }

let lastAim = 0;
function sendAim(force) {
  if (mode !== 'online' || !G) return;
  const now = performance.now();
  if (!force && now - lastAim < 60) return;
  lastAim = now;
  const m = { t: 'aim', a: G.aim, p: G.power, from: myIdx, hx: G.hand && hovering ? ptr.x : null, hy: G.hand && hovering ? ptr.y : null };
  if (isHost) bcast(m); else if (hostConn && hostConn.open) hostConn.send(m);
}

const PEER_OPTS = {
  debug: 0,
  config: {
    iceServers: [
      { urls: 'stun:stun.l.google.com:19302' },
      { urls: 'stun:global.stun.twilio.com:3478' },
      { urls: ['turn:openrelay.metered.ca:80', 'turn:openrelay.metered.ca:443', 'turn:openrelay.metered.ca:443?transport=tcp'],
        username: 'openrelayproject', credential: 'openrelayproject' }
    ]
  }
};
const CODE_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
const genCode = () => Array.from({ length: 5 }, () => CODE_CHARS[Math.floor(Math.random() * CODE_CHARS.length)]).join('');
const myName = () => ($('#pname').value.trim() || 'Jogador').slice(0, 14);

function createRoom() {
  const code = genCode();
  const p = new Peer('sinuca-' + code, PEER_OPTS);
  peer = p;
  p.on('open', () => {
    mode = 'online'; isHost = true; started = false; myIdx = 0;
    lobby = [{ name: myName(), conn: null }];
    $('#roomCode').textContent = code;
    broadcastLobby(); show('lobby');
  });
  p.on('error', err => {
    if (err.type === 'unavailable-id') { p.destroy(); createRoom(); }
    else { toast('Erro de conexão com o servidor'); resetNet(); }
  });
  p.on('connection', onGuest);
  p.on('disconnected', () => { if (!p.destroyed) p.reconnect(); });
}

function onGuest(conn) {
  conn.on('open', () => {
    if (started || lobby.length >= 4) { conn.send({ t: 'full' }); setTimeout(() => conn.close(), 400); return; }
    lobby.push({ name: String((conn.metadata && conn.metadata.name) || 'Jogador').slice(0, 14), conn });
    broadcastLobby();
  });
  conn.on('data', d => hostData(conn, d));
  conn.on('close', () => guestLeft(conn));
}

function broadcastLobby() {
  const names = lobby.map(l => l.name);
  lobby.forEach((l, i) => { if (l.conn && l.conn.open) l.conn.send({ t: 'lobby', names, you: i }); });
  renderLobby(names);
}

function guestLeft(conn) {
  const i = lobby.findIndex(l => l.conn === conn);
  if (i < 0) return;
  const name = lobby[i].name;
  if (!started) { lobby.splice(i, 1); broadcastLobby(); return; }
  if (G && G.phase !== 'over') {
    G.phase = 'over'; G.winner = null; G.msg = `${name} saiu da sala.`;
    pushState(); updateHud(true);
  }
}

const num = v => typeof v === 'number' && isFinite(v);
function hostData(conn, d) {
  const i = lobby.findIndex(l => l.conn === conn);
  if (i < 0 || !d) return;
  if (!started || !G || G.cur !== i) return;
  if (d.t === 'shot' && num(d.a) && num(d.p)) {
    if (doShot(G, d.a, Math.min(100, Math.max(5, d.p)))) pushState();
  } else if (d.t === 'place' && num(d.x) && num(d.y)) {
    if (doPlace(G, d.x, d.y)) pushState();
  } else if (d.t === 'aim' && G.phase === 'aim' && num(d.a) && num(d.p)) {
    G.aim = d.a; G.power = Math.min(100, Math.max(5, d.p));
    G.hx = num(d.hx) ? d.hx : null; G.hy = num(d.hy) ? d.hy : null;
    bcast({ t: 'aim', a: G.aim, p: G.power, from: i, hx: G.hx, hy: G.hy }, conn);
  }
}

function joinRoom() {
  const code = $('#jcode').value.trim().toUpperCase();
  if (code.length < 5) { toast('Digite o código da sala'); return; }
  const p = new Peer(undefined, PEER_OPTS);
  peer = p; mode = 'online'; isHost = false; leaving = false;
  p.on('open', () => {
    hostConn = p.connect('sinuca-' + code, { reliable: true, serialization: 'json', metadata: { name: myName() } });
    hostConn.on('data', clientData);
    hostConn.on('close', () => { if (!leaving) { toast('Conexão com a sala encerrada'); leave(true); } });
    hostConn.on('error', () => { toast('Não foi possível entrar'); resetNet(); });
    setTimeout(() => { if (hostConn && !hostConn.open && !leaving) { toast('Sala não encontrada'); resetNet(); } }, 15000);
  });
  p.on('disconnected', () => { if (!p.destroyed && !hostConn) p.reconnect(); });
  p.on('error', err => { toast(err.type === 'peer-unavailable' ? 'Sala não encontrada' : 'Erro de conexão'); resetNet(); });
}

function clientData(d) {
  if (!d) return;
  if (d.t === 'lobby') { myIdx = d.you; renderLobby(d.names); show('lobby'); $('#roomCode').textContent = ($('#jcode').value || '').toUpperCase(); }
  else if (d.t === 'full') { toast('Sala cheia ou partida em andamento'); resetNet(); }
  else if (d.t === 'start') { myIdx = d.you; G = d.g; started = true; lastKey = ''; show('game'); updateHud(true); }
  else if (d.t === 'state') { G = d.g; frame = 0; }
  else if (d.t === 'aim' && G && d.from !== myIdx && G.phase === 'aim') {
    G.aim = d.a; G.power = d.p; G.hx = d.hx; G.hy = d.hy;
  }
}

function renderLobby(names) {
  const ul = $('#plist'); ul.replaceChildren();
  for (let i = 0; i < 4; i++) {
    const li = document.createElement('li');
    const n = document.createElement('span'), b = document.createElement('span');
    b.className = 'badge';
    if (names[i]) {
      li.className = 't' + (i % 2);
      n.textContent = names[i] + (i === 0 ? ' (anfitrião)' : '') + (i === myIdx ? ' (você)' : '');
      b.textContent = 'Time ' + (i % 2 ? 'B' : 'A');
    } else { li.className = 'empty'; n.textContent = 'Aguardando jogador…'; }
    li.append(n, b); ul.appendChild(li);
  }
  const cnt = names.length;
  $('#startOnline').style.display = isHost ? '' : 'none';
  $('#startOnline').disabled = cnt < 2;
  $('#lobbyHint').textContent = isHost
    ? (cnt < 2 ? 'Compartilhe o código. Mínimo de 2 jogadores.' : cnt === 4 ? 'Duplas: 1º e 3º contra 2º e 4º.' : cnt === 3 ? 'Com 3 jogadores: 1º e 3º contra o 2º.' : 'Partida 1 contra 1.')
    : 'Aguardando o anfitrião iniciar a partida…';
}

function startOnline() {
  if (!isHost || lobby.length < 2) return;
  started = true; mode = 'online'; myIdx = 0; lastKey = '';
  G = newGame(lobby.map(l => l.name));
  lobby.forEach((l, i) => { if (l.conn) l.conn.send({ t: 'start', you: i, g: snapshot(G) }); });
  show('game'); updateHud(true);
}

function resetNet() {
  leaving = true;
  try { if (hostConn) hostConn.close(); } catch (e) { }
  try { if (peer) peer.destroy(); } catch (e) { }
  peer = null; hostConn = null; lobby = []; started = false; isHost = false; myIdx = -1;
  setTimeout(() => { leaving = false; }, 300);
  if (!G) show('online');
}

function leave(silent) {
  resetNet(); G = null; mode = 'local'; lastKey = '';
  $('#end').classList.remove('show');
  show('menu');
}

/* =====================================================================
   NAVEGAÇÃO / MENUS
   ===================================================================== */
function keepAwake() {
  try { if (navigator.wakeLock) navigator.wakeLock.request('screen').catch(() => { }); } catch (e) { }
}
function show(id) {
  document.querySelectorAll('.screen').forEach(s => s.classList.toggle('active', s.id === id));
  if (id === 'game') { keepAwake(); layout(); requestAnimationFrame(layout); setTimeout(layout, 120); }
}
document.addEventListener('visibilitychange', () => { if (!document.hidden && G) keepAwake(); });

$('#btnOnline').onclick = () => show('online');
$('#btnLocal').onclick = () => { buildNames(2); show('localSetup'); };
$('#backFromOnline').onclick = () => show('menu');
$('#backFromLocal').onclick = () => show('menu');
$('#btnCreate').onclick = () => { leaving = false; createRoom(); };
$('#btnJoin').onclick = joinRoom;
$('#startOnline').onclick = startOnline;
$('#leaveLobby').onclick = () => { leave(); };
$('#leave').onclick = () => { leave(); };
$('#toMenu').onclick = () => { leave(); };
$('#copyLink').onclick = () => {
  const l = location.origin + location.pathname + '?sala=' + $('#roomCode').textContent;
  if (navigator.clipboard) navigator.clipboard.writeText(l).then(() => toast('Link copiado'), () => toast(l));
  else toast(l);
};
$('#copyCode').onclick = () => {
  const c = $('#roomCode').textContent;
  if (navigator.clipboard) navigator.clipboard.writeText(c).then(() => toast('Código copiado'), () => toast(c));
  else toast(c);
};
$('#again').onclick = () => {
  if (!G) return;
  if (mode === 'local' || isHost) {
    G = newGame(G.players.map(p => p.name)); lastKey = '';
    pushState(); updateHud(true);
  }
};

/* Modo local: nomes */
let localCount = 2;
function buildNames(n) {
  localCount = n;
  document.querySelectorAll('#cnt button').forEach(b => b.classList.toggle('on', +b.dataset.n === n));
  const box = $('#names'), old = [...box.querySelectorAll('input')].map(i => i.value);
  box.replaceChildren();
  for (let i = 0; i < n; i++) {
    const inp = document.createElement('input');
    inp.type = 'text'; inp.maxLength = 14; inp.placeholder = `Jogador ${i + 1} (Time ${i % 2 ? 'B' : 'A'})`;
    inp.value = old[i] || ''; inp.setAttribute('aria-label', `Nome do jogador ${i + 1}`);
    box.appendChild(inp);
  }
  $('#localHint').textContent = n === 2 ? 'Partida 1 contra 1.' : n === 3 ? '1º e 3º jogam contra o 2º.' : 'Duplas: 1º e 3º contra 2º e 4º.';
}
document.querySelectorAll('#cnt button').forEach(b => b.onclick = () => buildNames(+b.dataset.n));
$('#startLocal').onclick = () => {
  const names = [...document.querySelectorAll('#names input')].map((i, k) => i.value.trim() || `Jogador ${k + 1}`);
  mode = 'local'; isHost = false; myIdx = -1; lastKey = '';
  G = newGame(names);
  show('game'); updateHud(true);
};

$('#jcode').addEventListener('input', e => { e.target.value = e.target.value.toUpperCase().replace(/[^A-Z0-9]/g, ''); });

/* Link de convite (?sala=CODIGO) */
(function () {
  const q = new URLSearchParams(location.search).get('sala');
  if (q) { $('#jcode').value = q.toUpperCase().replace(/[^A-Z0-9]/g, '').slice(0, 5); show('online'); }
})();
layout();
