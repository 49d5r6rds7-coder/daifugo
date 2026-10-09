'use strict';
/**
 * 大富豪 オンライン対戦サーバー（外部ライブラリ不要）
 *   node server.js   →  http://localhost:3000
 *
 * - ゲームの進行・カード配布・CPU はすべてサーバー側で行います（手札は本人にしか送りません）。
 * - サーバー → ブラウザは Server-Sent Events、ブラウザ → サーバーは POST です。
 */
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = Number(process.env.PORT) || 3000;
const DROP_MS = Number(process.env.DROP_MS) || 8000;     // 切断してから「離席」とみなすまで
const TURN_MS = Number(process.env.TURN_MS) || 60000;    // 1手の持ち時間
const EX_MS = Number(process.env.EX_MS) || 45000;        // カード交換の持ち時間
const CPU_MS = Number(process.env.CPU_MS) || 900;        // CPU が考える時間
const MAX_ROOMS = 500;

const CPU_NAMES = ['ハルカ', 'タケル', 'ミナ'];
const TITLES = ['大富豪', '富豪', '貧民', '大貧民'];
const POINTS = [4, 3, 2, 1];
const SUITS = ['S', 'H', 'D', 'C'];
const SYM = { S: '♠', H: '♥', D: '♦', C: '♣' };
const LABEL = r => (r <= 10 ? String(r) : { 11: 'J', 12: 'Q', 13: 'K', 14: 'A', 15: '2' }[r]);

/* ======================= カードとルール ======================= */
function makeDeck() {
  const d = []; let id = 0;
  for (const s of SUITS) for (let r = 3; r <= 15; r++) d.push({ id: id++, s, r });
  d.push({ id: id++, s: 'J', r: 16 }, { id: id++, s: 'J', r: 16 });
  return d;
}
function shuffle(a) {
  for (let i = a.length - 1; i > 0; i--) {
    const j = crypto.randomInt(i + 1);
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}
const byBase = (a, b) => a.r - b.r || SUITS.indexOf(a.s) - SUITS.indexOf(b.s);
const top = (arr, n) => arr.slice().sort((a, b) => byBase(b, a)).slice(0, n);
const low = (arr, n) => arr.slice().sort(byBase).slice(0, n);
const cardText = c => (c.s === 'J' ? 'ジョーカー' : SYM[c.s] + LABEL(c.r));
const cardsText = cs => cs.map(cardText).join(' ');
const strength = (g, r) => (r === 16 ? 16 : g.rev ? 18 - r : r);
const active = g => [0, 1, 2, 3].filter(i => !g.finished.includes(i));
function nextActive(g, p) {
  for (let k = 1; k <= 4; k++) {
    const i = (p + k) % 4;
    if (!g.finished.includes(i)) return i;
  }
  return p;
}

function validate(g, cards) {
  const n = cards.length;
  if (!n) return { ok: false, reason: '' };
  if (n > 4) return { ok: false, reason: '一度に出せるのは4枚までです' };
  const nat = cards.filter(c => c.s !== 'J');
  if (nat.some(c => c.r !== nat[0].r)) return { ok: false, reason: '同じ数字のカードだけまとめて出せます' };
  const rank = nat.length ? nat[0].r : 16;
  const f = g.field;
  if (!f) return { ok: true, rank };
  if (f.count === 1 && f.cards[0].s === 'J' && n === 1 && cards[0].s === 'S' && cards[0].r === 3) {
    return { ok: true, rank: 3, ret: true };
  }
  if (n !== f.count) return { ok: false, reason: `場は${f.count}枚です。${f.count}枚で出してください` };
  if (strength(g, rank) <= strength(g, f.rank)) return { ok: false, reason: '場より強いカードを選んでください' };
  return { ok: true, rank };
}

function candidates(hand) {
  const jokers = hand.filter(c => c.s === 'J');
  const nat = hand.filter(c => c.s !== 'J');
  const byRank = {};
  nat.forEach(c => (byRank[c.r] = byRank[c.r] || []).push(c));
  const out = [];
  for (const r in byRank) {
    const arr = byRank[r].slice().sort((a, b) => (a.s === 'S') - (b.s === 'S'));
    const max = Math.min(4, arr.length + jokers.length);
    for (let s = 1; s <= max; s++) {
      const useN = Math.min(s, arr.length);
      out.push([...arr.slice(0, useN), ...jokers.slice(0, s - useN)]);
    }
  }
  for (let s = 1; s <= jokers.length; s++) out.push(jokers.slice(0, s));
  const s3 = nat.find(c => c.s === 'S' && c.r === 3);
  if (s3) out.push([s3]);
  return out;
}

function chooseCpu(g, p, mustPlay) {
  const hand = g.hands[p];
  const legal = candidates(hand).filter(c => validate(g, c).ok);
  if (!legal.length) return null;
  const win = legal.find(c => c.length === hand.length);
  if (win) return win;
  const score = c => {
    const v = validate(g, c);
    const jk = c.filter(x => x.s === 'J').length;
    return strength(g, v.rank) + jk * 6 - c.length * 0.8;
  };
  legal.sort((a, b) => score(a) - score(b));
  const best = legal[0];
  if (g.field && hand.length > 5 && !mustPlay) {
    const danger = active(g).some(i => i !== p && g.hands[i].length <= 2);
    const v = validate(g, best);
    const heavy = strength(g, v.rank) >= 14 || best.some(x => x.s === 'J');
    if (!danger && heavy && Math.random() < 0.55) return null;
  }
  return best;
}

/* ======================= 部屋 ======================= */
const rooms = new Map();

function newGameState() {
  return {
    phase: 'lobby', seq: 0, gameNo: 0, score: [0, 0, 0, 0], prevOrder: null, seats: null,
    hands: [[], [], [], []], finished: [], fresh: [], log: [], field: null, ghost: null,
    rev: false, turn: -1, passes: 0, ex: null, fx: null, deadline: null
  };
}

function genCode() {
  const A = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
  for (let t = 0; t < 50; t++) {
    let s = '';
    for (let i = 0; i < 4; i++) s += A[crypto.randomInt(A.length)];
    if (!rooms.has(s)) return s;
  }
  return null;
}

function cleanName(n) {
  const s = String(n == null ? '' : n).replace(/[\u0000-\u001f\u007f<>]/g, '').trim();
  return Array.from(s).slice(0, 8).join('') || 'プレイヤー';
}

function newPlayer(name) {
  return { id: crypto.randomBytes(16).toString('hex'), name: cleanName(name), seat: -1, conns: new Set(), dropAt: Date.now() };
}

const playerBySeat = (room, i) => room.players.find(p => p.seat === i);
function absent(room, i) {
  const p = playerBySeat(room, i);
  return !!p && p.conns.size === 0 && p.dropAt != null && Date.now() - p.dropAt > DROP_MS;
}
const isAuto = (room, i) => !!room.g.seats[i].cpu || absent(room, i);

function curHost(room) {
  const order = [room.players.find(p => p.id === room.hostId), ...room.players];
  return order.find(p => p && p.conns.size > 0) || order.find(Boolean) || null;
}

function log(g, msg) {
  g.log.push(msg);
  if (g.log.length > 30) g.log.splice(0, g.log.length - 30);
}

function viewFor(room, p) {
  const g = room.g, host = curHost(room);
  const v = {
    code: room.code, phase: g.phase, gameNo: g.gameNo, isHost: !!host && host.id === p.id,
    seq: g.seq, fx: g.fx, score: g.score, prevOrder: g.prevOrder
  };
  if (g.phase === 'lobby') {
    v.players = room.players.map(q => ({ name: q.name, host: !!host && q.id === host.id, you: q.id === p.id, connected: q.conns.size > 0 }));
    return v;
  }
  v.you = p.seat;
  v.seats = g.seats.map((s, i) => ({ name: s.name, cpu: !!s.cpu, away: !s.cpu && absent(room, i), count: g.hands[i].length }));
  v.hand = p.seat >= 0 ? g.hands[p.seat] : [];
  const mine = new Set(v.hand.map(c => c.id));
  v.fresh = g.fresh.filter(id => mine.has(id));
  v.field = g.field; v.ghost = g.ghost; v.rev = g.rev; v.turn = g.turn; v.finished = g.finished;
  v.log = g.log.slice(-4);
  v.msLeft = g.deadline ? Math.max(0, g.deadline - Date.now()) : null;
  v.exNeed = g.ex ? (g.ex.need[p.seat] || 0) : 0;
  v.exSent = !!(g.ex && g.ex.sub[p.seat]);
  return v;
}

function broadcast(room) {
  for (const p of room.players) {
    if (!p.conns.size) continue;
    const data = `data: ${JSON.stringify(viewFor(room, p))}\n\n`;
    for (const res of p.conns) { try { res.write(data); } catch (e) { /* 切断は close で処理 */ } }
  }
}

function touch(room, fx) {
  const g = room.g;
  g.seq++;
  if (fx) g.fx = { seq: g.seq, text: fx };
  room.lastActive = Date.now();
  schedule(room);
  broadcast(room);
}

/* ----- ゲームの進行 ----- */
function startRoom(room, solo) {
  const g = room.g;
  const host = curHost(room);
  const ordered = [host, ...room.players.filter(p => p !== host)].filter(Boolean).slice(0, 4);
  const used = new Set();
  g.seats = ordered.map((p, i) => {
    let n = p.name, k = 2;
    while (used.has(n)) n = p.name + k++;
    used.add(n);
    p.seat = i;
    return { name: n, cpu: false, pid: p.id };
  });
  room.players = ordered;
  let ci = 0;
  while (g.seats.length < 4) g.seats.push({ name: CPU_NAMES[ci++], cpu: true, pid: null });
  newGame(room);
}

function newGame(room) {
  const g = room.g;
  const deck = shuffle(makeDeck());
  const hands = [[], [], [], []];
  deck.forEach((c, i) => hands[i % 4].push(c));
  hands.forEach(h => h.sort(byBase));
  Object.assign(g, {
    hands, field: null, ghost: null, rev: false, passes: 0, finished: [], phase: 'play',
    fresh: [], log: [], ex: null, gameNo: g.gameNo + 1, turn: -1, fx: null
  });
  if (g.prevOrder) { startExchange(room); return; }
  g.turn = hands.findIndex(h => h.some(c => c.s === 'D' && c.r === 3));
  log(g, `${g.seats[g.turn].name}が♦3を持っているので先攻です`);
  touch(room);
}

function startExchange(room) {
  const g = room.g;
  const [d, f, h, dh] = g.prevOrder;
  const H = g.hands;
  g.ex = { d, f, h, dh, gDh: top(H[dh], 2), gH: top(H[h], 1), need: {}, sub: {} };
  if (!isAuto(room, d)) g.ex.need[d] = 2;
  if (!isAuto(room, f)) g.ex.need[f] = 1;
  if (Object.keys(g.ex.need).length) {
    g.phase = 'exchange';
    log(g, 'カード交換：大富豪と富豪が渡すカードを選んでいます');
    touch(room);
    return;
  }
  finishExchange(room);
}

function exchangeReady(g) {
  return Object.keys(g.ex.need).every(s => g.ex.sub[s]);
}

function finishExchange(room) {
  const g = room.g;
  const { d, f, h, dh, gDh, gH, sub } = g.ex;
  const H = g.hands;
  const pick = (seat, n, fb) => {
    const ids = sub[seat];
    if (ids) {
      const cs = H[seat].filter(c => ids.includes(c.id));
      if (cs.length === n) return cs;
    }
    return fb();
  };
  const giftD = pick(d, 2, () => low(H[d], 2));
  const giftF = pick(f, 1, () => low(H[f], 1));
  const move = (from, to, cards) => {
    const ids = new Set(cards.map(c => c.id));
    H[from] = H[from].filter(c => !ids.has(c.id));
    H[to].push(...cards);
    cards.forEach(c => g.fresh.push(c.id));
  };
  move(d, dh, giftD); move(dh, d, gDh);
  move(f, h, giftF); move(h, f, gH);
  H.forEach(x => x.sort(byBase));
  log(g, 'カード交換を行いました');
  log(g, `${TITLES[3]}の${g.seats[dh].name}から開始`);
  g.turn = dh; g.phase = 'play'; g.ex = null;
  touch(room);
}

function doPlay(room, p, cards) {
  const g = room.g;
  const v = validate(g, cards);
  if (!v.ok) return false;
  const ids = new Set(cards.map(c => c.id));
  g.hands[p] = g.hands[p].filter(c => !ids.has(c.id));
  const own = new Set(g.hands[p].map(c => c.id));
  g.fresh = g.fresh.filter(id => !ids.has(id) && !own.has(id));
  const shown = cards.slice().sort(byBase);
  const name = g.seats[p].name;
  g.ghost = null;
  g.field = { cards: shown, count: cards.length, rank: v.rank, owner: p };
  g.passes = 0;
  log(g, `${name}：${cardsText(shown)}${v.ret ? '（スペ3返し）' : ''}`);

  let fx = '';
  if (cards.length >= 4) {
    g.rev = !g.rev;
    log(g, g.rev ? '革命！ カードの強さが逆転' : '革命返し！ 強さが元に戻った');
    fx = '革命';
  }
  let out = false;
  if (g.hands[p].length === 0) {
    g.finished.push(p);
    out = true;
    log(g, `${name}があがり（${TITLES[g.finished.length - 1]}）`);
  }
  if (active(g).length <= 1) { endGame(room, fx); return true; }

  let next;
  if (v.rank === 8 && !v.ret) {
    g.ghost = { cards: shown, owner: p, note: `${name}の八切り` };
    g.field = null;
    log(g, '八切り！ 場が流れた');
    if (!fx) fx = '八切り';
    next = out ? nextActive(g, p) : p;
  } else {
    next = nextActive(g, p);
  }
  g.turn = next;
  touch(room, fx);
  return true;
}

function doPass(room, p) {
  const g = room.g;
  g.passes++;
  log(g, `${g.seats[p].name}：パス`);
  const f = g.field;
  const ownerActive = !g.finished.includes(f.owner);
  const need = ownerActive ? active(g).length - 1 : active(g).length;
  if (g.passes >= need) {
    g.ghost = { cards: f.cards, owner: f.owner, note: '全員パスで場が流れました' };
    g.field = null;
    g.passes = 0;
    log(g, '全員パス。場が流れた');
    g.turn = ownerActive ? f.owner : nextActive(g, f.owner);
  } else {
    g.turn = nextActive(g, p);
  }
  touch(room);
}

function endGame(room, fx) {
  const g = room.g;
  active(g).forEach(i => g.finished.push(i));
  g.phase = 'over';
  g.prevOrder = g.finished.slice();
  g.prevOrder.forEach((p, i) => { g.score[p] += POINTS[i]; });
  log(g, `対戦終了。${g.seats[g.prevOrder[0]].name}が大富豪`);
  g.turn = -1;
  touch(room, fx);
}

/* ----- 自動進行（CPU・離席・時間切れ） ----- */
function schedule(room) {
  clearTimeout(room.timer);
  const g = room.g;
  g.deadline = null;
  try {
    if (g.phase === 'exchange' && g.ex) {
      for (const s of Object.keys(g.ex.need)) {
        if (!g.ex.sub[s] && absent(room, Number(s))) g.ex.sub[s] = low(g.hands[s], g.ex.need[s]).map(c => c.id);
      }
      if (exchangeReady(g)) { finishExchange(room); return; }
      if (room.deadlineSeq !== g.seq) { room.deadlineSeq = g.seq; room.deadlineAt = Date.now() + EX_MS; }
      g.deadline = room.deadlineAt;
      const key = g.seq;
      room.timer = setTimeout(() => safe(() => {
        if (room.g.seq !== key || room.g.phase !== 'exchange') return;
        const ex = room.g.ex;
        for (const s of Object.keys(ex.need)) if (!ex.sub[s]) ex.sub[s] = low(room.g.hands[s], ex.need[s]).map(c => c.id);
        finishExchange(room);
      }), Math.max(0, room.deadlineAt - Date.now()));
      return;
    }
    if (g.phase !== 'play') return;
    const t = g.turn;
    if (t < 0) return;
    const key = g.seq;
    if (isAuto(room, t)) {
      const humansDone = g.seats.every((s, i) => s.cpu || g.finished.includes(i) || absent(room, i));
      const delay = humansDone ? 300 : CPU_MS + Math.random() * 350;
      room.timer = setTimeout(() => safe(() => autoMove(room, t, key, false)), delay);
    } else {
      if (room.deadlineSeq !== g.seq) { room.deadlineSeq = g.seq; room.deadlineAt = Date.now() + TURN_MS; }
      g.deadline = room.deadlineAt;
      room.timer = setTimeout(() => safe(() => autoMove(room, t, key, true)), Math.max(0, room.deadlineAt - Date.now()));
    }
  } catch (e) { console.error('schedule', e); }
}

function autoMove(room, p, seq, timedOut) {
  const g = room.g;
  if (g.seq !== seq || g.phase !== 'play' || g.turn !== p) return;
  if (timedOut) log(g, `${g.seats[p].name}は時間切れのため自動で進行します`);
  const choice = chooseCpu(g, p, timedOut);
  if (choice) doPlay(room, p, choice); else doPass(room, p);
}

function safe(fn) { try { fn(); } catch (e) { console.error(e); } }

/* ----- プレイヤーの操作 ----- */
class ApiError extends Error { constructor(msg, status) { super(msg); this.status = status || 400; } }

function handAction(room, p, ids) {
  if (!Array.isArray(ids) || ids.length > 4 || !ids.every(Number.isInteger)) throw new ApiError('カードの指定が正しくありません');
  const cards = room.g.hands[p.seat].filter(c => ids.includes(c.id));
  if (cards.length !== new Set(ids).size) throw new ApiError('そのカードは持っていません');
  return cards;
}

function act(room, p, body) {
  const g = room.g;
  const host = curHost(room);
  const isHost = !!host && host.id === p.id;
  switch (body.type) {
    case 'start':
      if (g.phase !== 'lobby') throw new ApiError('すでに始まっています');
      if (!isHost) throw new ApiError('ホストだけが開始できます', 403);
      startRoom(room);
      return;
    case 'play': {
      if (g.phase !== 'play' || g.turn !== p.seat) throw new ApiError('あなたの番ではありません');
      const cards = handAction(room, p, body.ids);
      const v = validate(g, cards);
      if (!v.ok) throw new ApiError(v.reason || '出せないカードです');
      doPlay(room, p.seat, cards);
      return;
    }
    case 'pass':
      if (g.phase !== 'play' || g.turn !== p.seat) throw new ApiError('あなたの番ではありません');
      if (!g.field) throw new ApiError('最初の手番ではパスできません');
      doPass(room, p.seat);
      return;
    case 'exchange': {
      if (g.phase !== 'exchange' || !g.ex) throw new ApiError('いまはカード交換の時間ではありません');
      const need = g.ex.need[p.seat];
      if (!need) throw new ApiError('あなたは渡すカードを選ぶ必要がありません');
      const cards = handAction(room, p, body.ids);
      if (cards.length !== need) throw new ApiError(`${need}枚を選んでください`);
      g.ex.sub[p.seat] = cards.map(c => c.id);
      if (exchangeReady(g)) finishExchange(room); else touch(room);
      return;
    }
    case 'next':
      if (g.phase !== 'over') throw new ApiError('対戦中です');
      if (!isHost) throw new ApiError('ホストだけが次の対戦を始められます', 403);
      newGame(room);
      return;
    case 'reset':
      if (g.phase !== 'over') throw new ApiError('対戦中です');
      if (!isHost) throw new ApiError('ホストだけが操作できます', 403);
      g.score = [0, 0, 0, 0]; g.prevOrder = null; g.gameNo = 0;
      newGame(room);
      return;
    case 'leave':
      if (g.phase === 'lobby') {
        room.players = room.players.filter(q => q !== p);
        if (!room.players.length) { destroyRoom(room); return; }
        if (room.hostId === p.id) room.hostId = room.players[0].id;
        for (const res of p.conns) { try { res.end(); } catch (e) {} }
        p.conns.clear();
        touch(room);
      }
      return;
    default:
      throw new ApiError('不明な操作です');
  }
}

function destroyRoom(room) {
  clearTimeout(room.timer);
  for (const p of room.players) for (const res of p.conns) { try { res.end(); } catch (e) {} }
  rooms.delete(room.code);
}

setInterval(() => {
  const now = Date.now();
  for (const room of rooms.values()) {
    const live = room.players.some(p => p.conns.size > 0);
    if (!live && now - room.lastActive > 20 * 60 * 1000) destroyRoom(room);
  }
}, 60 * 1000).unref();

setInterval(() => {
  for (const room of rooms.values()) {
    for (const p of room.players) for (const res of p.conns) { try { res.write(': ping\n\n'); } catch (e) {} }
  }
}, 15000).unref();

/* ======================= HTTP ======================= */
function sendJson(res, status, obj) {
  const body = JSON.stringify(obj);
  res.writeHead(status, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
  res.end(body);
}

function readBody(req) {
  return new Promise((resolve, reject) => {
    let size = 0; const chunks = [];
    req.on('data', c => {
      size += c.length;
      if (size > 8192) { reject(new ApiError('データが大きすぎます', 413)); req.destroy(); return; }
      chunks.push(c);
    });
    req.on('end', () => {
      if (!chunks.length) return resolve({});
      try { resolve(JSON.parse(Buffer.concat(chunks).toString('utf8'))); }
      catch (e) { reject(new ApiError('リクエストが正しくありません')); }
    });
    req.on('error', reject);
  });
}

function findAuth(code, token) {
  const room = rooms.get(String(code || '').toUpperCase());
  if (!room) throw new ApiError('部屋が見つかりません', 404);
  const player = room.players.find(p => p.id === token);
  if (!player) throw new ApiError('この部屋に参加していません', 403);
  return { room, player };
}

const INDEX = path.join(__dirname, 'public', 'index.html');

async function handle(req, res) {
  const url = new URL(req.url, 'http://localhost');
  const p = url.pathname;

  if (req.method === 'GET' && p === '/healthz') { res.writeHead(200); res.end('ok'); return; }

  if (req.method === 'GET' && p === '/api/events') {
    const { room, player } = findAuth(url.searchParams.get('code'), url.searchParams.get('token'));
    res.writeHead(200, {
      'Content-Type': 'text/event-stream; charset=utf-8', 'Cache-Control': 'no-cache, no-transform',
      'Connection': 'keep-alive', 'X-Accel-Buffering': 'no'
    });
    res.write('retry: 2000\n\n');
    player.conns.add(res);
    player.dropAt = null;
    room.lastActive = Date.now();
    res.write(`data: ${JSON.stringify(viewFor(room, player))}\n\n`);
    broadcast(room);
    req.on('close', () => {
      player.conns.delete(res);
      if (player.conns.size === 0) {
        player.dropAt = Date.now();
        const seq = room.g.seq;
        setTimeout(() => {
          if (!rooms.has(room.code) || player.conns.size > 0) return;
          broadcast(room);
          if (room.g.seq === seq) schedule(room);
        }, DROP_MS + 100).unref();
      }
    });
    return;
  }

  if (req.method === 'POST' && p.startsWith('/api/')) {
    const body = await readBody(req);
    if (p === '/api/create') {
      if (rooms.size >= MAX_ROOMS) throw new ApiError('現在、新しい部屋をつくれません。しばらくしてからお試しください', 503);
      const code = genCode();
      if (!code) throw new ApiError('部屋コードを作れませんでした', 503);
      const player = newPlayer(body.name);
      const room = { code, players: [player], hostId: player.id, g: newGameState(), timer: null, lastActive: Date.now(), deadlineSeq: -1, deadlineAt: 0 };
      rooms.set(code, room);
      if (body.solo) startRoom(room, true);
      sendJson(res, 200, { code, token: player.id });
      return;
    }
    if (p === '/api/join') {
      const room = rooms.get(String(body.code || '').toUpperCase());
      if (!room) throw new ApiError('その部屋は見つかりません', 404);
      const existing = body.token && room.players.find(q => q.id === body.token);
      if (existing) { sendJson(res, 200, { code: room.code, token: existing.id }); return; }
      if (room.g.phase !== 'lobby') throw new ApiError('この部屋の対戦はすでに始まっています', 409);
      if (room.players.length >= 4) throw new ApiError('この部屋は満席です', 409);
      const player = newPlayer(body.name);
      room.players.push(player);
      touch(room);
      sendJson(res, 200, { code: room.code, token: player.id });
      return;
    }
    if (p === '/api/act') {
      const { room, player } = findAuth(body.code, body.token);
      act(room, player, body);
      sendJson(res, 200, { ok: true });
      return;
    }
    throw new ApiError('見つかりません', 404);
  }

  if (req.method === 'GET') {
    fs.readFile(INDEX, (err, data) => {
      if (err) { res.writeHead(500); res.end('index.html が見つかりません'); return; }
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' });
      res.end(data);
    });
    return;
  }
  res.writeHead(405); res.end();
}

const server = http.createServer((req, res) => {
  handle(req, res).catch(e => {
    if (res.headersSent) { try { res.end(); } catch (x) {} return; }
    if (e instanceof ApiError) sendJson(res, e.status, { error: e.message });
    else { console.error(e); sendJson(res, 500, { error: 'サーバーでエラーが起きました' }); }
  });
});

if (require.main === module) {
  server.listen(PORT, () => console.log(`大富豪サーバーを起動しました: http://localhost:${PORT}`));
}

module.exports = { server, rooms, validate, candidates, chooseCpu };
