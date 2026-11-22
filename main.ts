// Sokoban solver: push-optimal A* search with room decomposition.
//
// Why this shape: the score rewards the fewest *pushes*, not the fewest
// moves, and a solution even one push over the optimum earns less than
// half marks. So the core search works in push space (a state is the set
// of box squares plus the player's reachable region), never in move
// space, and its cost is pushes alone. A* over pushes with an admissible
// assignment heuristic finds the push optimum while expanding far fewer
// states than plain breadth-first search.
//
// Levels drawn by this contest's generator are a hallway with small
// rooms off it; a box pushed out of a room into the hallway can never
// come back, so each room is an independent sub-problem and the level
// optimum is the sum of the rooms' optima. We detect the rooms (the
// hallway squares are dead squares: a box there reaches no goal), solve
// each room on its own with the other rooms' boxes standing as walls,
// and fall back to a whole-level push search when a level does not
// decompose that way.
//
// Pruning, all sound (never removes a solvable state):
//   - dead squares: a box on a square from which no goal is reachable
//     by pushes (ignoring other boxes) can never be solved;
//   - frozen 2x2 blocks: four squares of wall/box with a box off its
//     goal can never move again;
//   - assignment bound: if some box cannot reach any goal, prune.
//
// Determinism: no clock, no randomness, no environment reads beyond the
// harness's input/output directories. All budgets count states (work),
// never time, so two runs write identical bytes.

import { chmodSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Fixed search budgets, in states created (work, not time).
const ROOM_STATE_CAP = 600000;
const LEVEL_STATE_CAP = 1200000;
let globalStateBudget = 3000000;

const DIRS = [
  [0, -1, 'u', 'U'],
  [0, 1, 'd', 'D'],
  [-1, 0, 'l', 'L'],
  [1, 0, 'r', 'R'],
];

// ---------- level parsing ----------

function parseLevel(text) {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals = [];
  const boxes = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x];
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
    }
  }
  boxes.sort((a, b) => a - b);
  goals.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player };
}

// ---------- static analysis ----------

// Squares from which a lone box can be pushed onto some goal, found by
// pulling boxes backwards from the goals over open floor.
function liveSquares(w, wall, goals) {
  const live = new Uint8Array(wall.length);
  const queue = [];
  for (const g of goals) {
    live[g] = 1;
    queue.push(g);
  }
  for (let qi = 0; qi < queue.length; qi++) {
    const t = queue[qi];
    for (const [dx, dy] of DIRS) {
      const d = dy * w + dx;
      const b = t - d; // box stood here before the push that landed on t
      const stand = b - d; // and the player stood here
      if (!wall[b] && !wall[stand] && !live[b]) {
        live[b] = 1;
        queue.push(b);
      }
    }
  }
  return live;
}

// Push distance from every square to each goal, for a lone box.
// dist[g][i] = fewest pushes taking a box from i to goal g (Infinity if none).
function pushDistances(w, wall, goals) {
  const size = wall.length;
  return goals.map((goal) => {
    const dist = new Float64Array(size).fill(Infinity);
    dist[goal] = 0;
    const queue = [goal];
    for (let qi = 0; qi < queue.length; qi++) {
      const t = queue[qi];
      for (const [dx, dy] of DIRS) {
        const d = dy * w + dx;
        const b = t - d;
        const stand = b - d;
        if (!wall[b] && !wall[stand] && dist[b] === Infinity) {
          dist[b] = dist[t] + 1;
          queue.push(b);
        }
      }
    }
    return dist;
  });
}

// Admissible push lower bound for a set of boxes: the cheapest assignment
// of distinct goals to boxes by lone-box push distance (brute force over
// permutations for up to 5 boxes; sum of per-box minima beyond that, which
// is also admissible because each push moves exactly one box).
function heuristic(boxes, dists) {
  const n = boxes.length;
  if (n === 0) return 0;
  if (n > 5) {
    let sum = 0;
    for (const b of boxes) {
      let best = Infinity;
      for (const dist of dists) if (dist[b] < best) best = dist[b];
      if (best === Infinity) return Infinity;
      sum += best;
    }
    return sum;
  }
  const goalsIdx = dists.map((_, i) => i);
  let bestTotal = Infinity;
  const used = new Uint8Array(dists.length);
  const walk = (bi, acc) => {
    if (acc >= bestTotal) return;
    if (bi === n) {
      bestTotal = acc;
      return;
    }
    for (const gi of goalsIdx) {
      if (used[gi]) continue;
      const d = dists[gi][boxes[bi]];
      if (d === Infinity) continue;
      used[gi] = 1;
      walk(bi + 1, acc + d);
      used[gi] = 0;
    }
  };
  walk(0, 0);
  return bestTotal;
}

// ---------- reachability ----------

// Flood fill from `from` around walls and boxes. Fills `seen` with `stamp`
// over the reachable region and returns the region's lowest square, the
// canonical name of the region.
function reach(w, wall, occupied, from, seen, stamp, stack) {
  let low = from;
  let n = 0;
  stack[n++] = from;
  seen[from] = stamp;
  while (n > 0) {
    const p = stack[--n];
    if (p < low) low = p;
    const up = p - w;
    const down = p + w;
    const left = p - 1;
    const right = p + 1;
    if (!wall[up] && !occupied[up] && seen[up] !== stamp) { seen[up] = stamp; stack[n++] = up; }
    if (!wall[down] && !occupied[down] && seen[down] !== stamp) { seen[down] = stamp; stack[n++] = down; }
    if (!wall[left] && !occupied[left] && seen[left] !== stamp) { seen[left] = stamp; stack[n++] = left; }
    if (!wall[right] && !occupied[right] && seen[right] !== stamp) { seen[right] = stamp; stack[n++] = right; }
  }
  return low;
}

// Is the box just pushed onto `t` part of a frozen 2x2 block?
function frozenBlock(w, wall, occupied, goalSet, t) {
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1;
    const c = a + w;
    const d = c + 1;
    if (a < 0 || d >= wall.length) continue;
    const solid = (wall[a] || occupied[a]) && (wall[b] || occupied[b]) && (wall[c] || occupied[c]) && (wall[d] || occupied[d]);
    if (!solid) continue;
    if ((occupied[a] && !goalSet.has(a)) || (occupied[b] && !goalSet.has(b)) ||
        (occupied[c] && !goalSet.has(c)) || (occupied[d] && !goalSet.has(d))) return true;
  }
  return false;
}

// Shortest walk from `from` to `to` avoiding walls and boxes, lower-case
// LURD letters, first direction first on ties.
function walkTo(w, wall, occupied, from, to) {
  if (from === to) return '';
  const prev = new Int32Array(wall.length).fill(-1);
  const how = new Array(wall.length);
  const queue = [from];
  prev[from] = from;
  for (let qi = 0; qi < queue.length; qi++) {
    const p = queue[qi];
    if (p === to) break;
    for (const [dx, dy, letter] of DIRS) {
      const q = p + dy * w + dx;
      if (wall[q] || occupied[q] || prev[q] !== -1) continue;
      prev[q] = p;
      how[q] = letter;
      queue.push(q);
    }
  }
  if (prev[to] === -1) return null;
  let s = '';
  for (let p = to; p !== from; p = prev[p]) s = how[p] + s;
  return s;
}

// ---------- the push-optimal A* ----------

// Solve one (sub-)level push-optimally. Returns {pushes, moves} or null
// when the state budget runs out or the level cannot be solved.
function solvePush(level, stateCap) {
  const { w, wall, goals, boxes: startBoxes, player: startPlayer } = level;
  const size = wall.length;
  const goalSet = new Set(goals);
  const live = liveSquares(w, wall, goals);
  for (const b of startBoxes) if (!live[b]) return null;
  const dists = pushDistances(w, wall, goals);
  const h0 = heuristic(startBoxes, dists);
  if (h0 === Infinity) return null;
  const solved = (boxes) => boxes.every((b) => goalSet.has(b));
  if (solved(startBoxes)) return { pushes: 0, moves: '' };

  const occupied = new Uint8Array(size);
  const seen = new Int32Array(size);
  const mark = new Int32Array(size);
  const stack = new Int32Array(size);
  let stamp = 0;

  const keyOf = (boxes, rep) => String.fromCharCode(rep, ...boxes);

  // Node store, parallel arrays.
  const nodeBoxes = [startBoxes];
  const nodePlayer = [startPlayer];
  const nodeParent = [-1];
  const nodeG = [0];
  const bestG = new Map();

  for (const b of startBoxes) occupied[b] = 1;
  const rep0 = reach(w, wall, occupied, startPlayer, seen, ++stamp, stack);
  for (const b of startBoxes) occupied[b] = 0;
  bestG.set(keyOf(startBoxes, rep0), 0);

  // Binary heap on (f, -g, sequence): cheapest estimate first, deeper
  // nodes first on a tie, insertion order last so runs are identical.
  const heap = [];
  let seq = 0;
  const entry = (f, g, node) => ({ f, g, node, seq: seq++ });
  const before = (a, b) => a.f < b.f || (a.f === b.f && (a.g > b.g || (a.g === b.g && a.seq < b.seq)));
  const heapPush = (e) => {
    let i = heap.length;
    heap.push(e);
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!before(heap[i], heap[p])) break;
      [heap[i], heap[p]] = [heap[p], heap[i]];
      i = p;
    }
  };
  const heapPop = () => {
    const top = heap[0];
    const last = heap.pop();
    if (heap.length > 0) {
      heap[0] = last;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= heap.length) break;
        if (c + 1 < heap.length && before(heap[c + 1], heap[c])) c++;
        if (!before(heap[c], heap[i])) break;
        [heap[i], heap[c]] = [heap[c], heap[i]];
        i = c;
      }
    }
    return top;
  };
  heapPush(entry(h0, 0, 0));

  let found = -1;
  while (heap.length > 0) {
    const { g, node } = heapPop();
    const boxes = nodeBoxes[node];
    if (g !== nodeG[node]) continue;
    if (solved(boxes)) { found = node; break; }
    if (nodeBoxes.length > stateCap || nodeBoxes.length > globalStateBudget) return null;

    for (const b of boxes) occupied[b] = 1;
    reach(w, wall, occupied, nodePlayer[node], seen, ++stamp, stack);
    const here = stamp;

    for (let bi = 0; bi < boxes.length; bi++) {
      const b = boxes[bi];
      for (const [dx, dy] of DIRS) {
        const d = dy * w + dx;
        const target = b + d;
        const stand = b - d;
        if (seen[stand] !== here) continue;
        if (wall[target] || occupied[target] || !live[target]) continue;
        occupied[b] = 0;
        occupied[target] = 1;
        const frozen = frozenBlock(w, wall, occupied, goalSet, target);
        let next = null;
        let key = null;
        if (!frozen) {
          next = boxes.slice();
          next[bi] = target;
          next.sort((x, y) => x - y);
          const rep = reach(w, wall, occupied, b, mark, ++stamp, stack);
          key = keyOf(next, rep);
        }
        occupied[target] = 0;
        occupied[b] = 1;
        if (frozen) continue;
        const g2 = g + 1;
        const known = bestG.get(key);
        if (known !== undefined && known <= g2) continue;
        const h = heuristic(next, dists);
        if (h === Infinity) continue;
        bestG.set(key, g2);
        const idx = nodeBoxes.length;
        nodeBoxes.push(next);
        nodePlayer.push(b); // after the push the player stands where the box was
        nodeParent.push(node);
        nodeG.push(g2);
        heapPush(entry(g2 + h, g2, idx));
      }
    }
    for (const b of boxes) occupied[b] = 0;
  }
  if (found < 0) return null;
  globalStateBudget -= nodeBoxes.length;

  // Rebuild the move string: replay the push path, walking the player to
  // each push's stand square along a shortest walk.
  const path = [];
  for (let s = found; s > 0; s = nodeParent[s]) path.push(s);
  path.reverse();
  let moves = '';
  let player = startPlayer;
  let boxes = startBoxes;
  for (const s of path) {
    const nextBoxes = nodeBoxes[s];
    const from = boxes.find((b) => !nextBoxes.includes(b));
    const to = nextBoxes.find((b) => !boxes.includes(b));
    const d = to - from;
    const dir = DIRS.find(([dx, dy]) => dy * w + dx === d);
    for (const b of boxes) occupied[b] = 1;
    const walk = walkTo(w, wall, occupied, player, from - d);
    for (const b of boxes) occupied[b] = 0;
    if (walk === null) return null;
    moves += walk + dir[3];
    player = from;
    boxes = nextBoxes;
  }
  return { pushes: path.length, moves };
}

// ---------- room decomposition ----------

// Split a level into rooms by cutting the player's row's dead squares
// (the hallway). Returns [{boxes, goals}] or null when the level is not
// a clean set of rooms.
function roomsOf(level) {
  const { w, wall, goals, boxes, player } = level;
  const live = liveSquares(w, wall, goals);
  const row = Math.floor(player / w);
  const cut = new Uint8Array(wall.length);
  for (let i = row * w; i < (row + 1) * w; i++) {
    if (!wall[i] && !live[i]) cut[i] = 1;
  }
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(wall.length).fill(-1);
  const rooms = [];
  for (let s = 0; s < wall.length; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const squares = [s];
    part[s] = rooms.length;
    for (let i = 0; i < squares.length; i++) {
      for (const [dx, dy] of DIRS) {
        const q = squares[i] + dy * w + dx;
        if (q < 0 || q >= wall.length) continue;
        if (!wall[q] && !cut[q] && part[q] < 0) {
          part[q] = rooms.length;
          squares.push(q);
        }
      }
    }
    rooms.push({ squares, boxes: [], goals: [] });
  }
  for (const b of boxes) rooms[part[b]].boxes.push(b);
  for (const g of goals) {
    if (part[g] < 0) return null;
    rooms[part[g]].goals.push(g);
  }
  if (rooms.some((r) => r.boxes.length !== r.goals.length)) return null;
  const withBoxes = rooms.filter((r) => r.boxes.length > 0);
  return withBoxes.length > 0 ? withBoxes : null;
}

function endPosition(w, from, moves) {
  let p = from;
  for (const ch of moves.toLowerCase()) {
    p += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
  }
  return p;
}

// Solve room by room: each room push-optimally, the boxes of the other
// rooms standing as walls. Returns {pushes, moves} or null.
function solveByRooms(level) {
  const rooms = roomsOf(level);
  if (rooms === null) return null;
  let player = level.player;
  let currentBoxes = level.boxes.slice();
  let pushes = 0;
  let moves = '';
  for (const room of rooms) {
    const roomBoxSet = new Set(room.boxes);
    const wall = level.wall.slice();
    for (const b of currentBoxes) if (!roomBoxSet.has(b)) wall[b] = 1;
    const sub = {
      w: level.w,
      h: level.h,
      wall,
      goals: room.goals.slice().sort((a, b) => a - b),
      boxes: room.boxes.slice().sort((a, b) => a - b),
      player,
    };
    const solvedRoom = solvePush(sub, ROOM_STATE_CAP);
    if (solvedRoom === null) return null;
    pushes += solvedRoom.pushes;
    moves += solvedRoom.moves;
    player = endPosition(level.w, player, solvedRoom.moves);
    // The room's boxes now rest on its goals; the rest are unmoved.
    currentBoxes = currentBoxes.filter((b) => !roomBoxSet.has(b)).concat(room.goals).sort((a, b) => a - b);
  }
  return { pushes, moves };
}

// ---------- entry point ----------

function solve(levelText) {
  const level = parseLevel(levelText);
  if (level.boxes.length === 0 || level.player < 0) return '';
  const byRooms = solveByRooms(level);
  if (byRooms !== null) return byRooms.moves;
  const whole = solvePush(level, LEVEL_STATE_CAP);
  if (whole !== null) return whole.moves;
  return '';
}

for (const id of readdirSync(INPUT_DIR).sort()) {
  const moves = solve(readFileSync(join(INPUT_DIR, id, 'level.txt'), 'utf8'));
  const dir = join(OUTPUT_DIR, id);
  mkdirSync(dir, { recursive: true });
  const file = join(dir, 'solution.txt');
  writeFileSync(file, `${moves}\n`);
  try {
    chmodSync(dir, 0o755);
    chmodSync(file, 0o644);
  } catch {
    // permissions are a courtesy on top of the umask; never fail a run on them
  }
}
