import React, { useState, useEffect, useRef, useCallback, useMemo } from "react";
import {
  PenLine,
  Eraser,
  Undo2,
  Lightbulb,
  Pause,
  Play as PlayIcon,
  Flame,
  Trophy,
  Clock,
  RefreshCw,
  RotateCcw,
  CheckCircle2,
} from "lucide-react";
import {
  ResponsiveContainer,
  LineChart,
  Line,
  XAxis,
  YAxis,
  CartesianGrid,
  Tooltip,
} from "recharts";

/* =========================================================================
   常數與工具
   ========================================================================= */

const K_STATS = "career-stats";
const K_DAILY = "daily-progress";
const K_ACTIVE_NORMAL = "active-normal-game";
const K_ACTIVE_DAILY = "active-daily-game";

const DIFF_LABEL = { easy: "簡單", medium: "中等", hard: "困難", expert: "專家" };
const DIFF_GIVENS = { easy: 42, medium: 34, hard: 28, expert: 24 };
const DIFF_ORDER = ["easy", "medium", "hard", "expert"];
const WEEKDAY_DIFF = ["medium", "easy", "easy", "medium", "medium", "hard", "expert"]; // 週日~週六

function pad2(n) {
  return String(n).padStart(2, "0");
}
function todayStr() {
  const d = new Date();
  return `${d.getFullYear()}-${pad2(d.getMonth() + 1)}-${pad2(d.getDate())}`;
}
function addDays(dateStr, delta) {
  const [y, m, d] = dateStr.split("-").map(Number);
  const dt = new Date(y, m - 1, d);
  dt.setDate(dt.getDate() + delta);
  return `${dt.getFullYear()}-${pad2(dt.getMonth() + 1)}-${pad2(dt.getDate())}`;
}
function weekdayOf(dateStr) {
  const [y, m, d] = dateStr.split("-").map(Number);
  return new Date(y, m - 1, d).getDay();
}
function formatDateLabel(dateStr) {
  const [, m, d] = dateStr.split("-").map(Number);
  return `${m}/${d}`;
}
function formatTime(totalSeconds) {
  const s = Math.max(0, Math.floor(totalSeconds));
  const h = Math.floor(s / 3600);
  const m = Math.floor((s % 3600) / 60);
  const sec = s % 60;
  if (h > 0) return `${h}:${pad2(m)}:${pad2(sec)}`;
  return `${m}:${pad2(sec)}`;
}
function arraysEqual(a, b) {
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false;
  return true;
}

/* =========================================================================
   亂數（可用字串播種，讓每日挑戰對同一天可重現）
   ========================================================================= */

function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a |= 0;
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
function seedFromString(str) {
  let h = 1779033703 ^ str.length;
  for (let i = 0; i < str.length; i++) {
    h = Math.imul(h ^ str.charCodeAt(i), 3432918353);
    h = (h << 13) | (h >>> 19);
  }
  return h >>> 0;
}
function shuffle(arr, rng) {
  const a = arr.slice();
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

/* =========================================================================
   數獨核心：產生與求解（位元遮罩 + 最少候選數優先）
   ========================================================================= */

function boxIndex(r, c) {
  return Math.floor(r / 3) * 3 + Math.floor(c / 3);
}

function solve(board, { countLimit = 1, randomize = false, rng = Math.random } = {}) {
  const rows = new Array(9).fill(0);
  const cols = new Array(9).fill(0);
  const boxes = new Array(9).fill(0);
  const empties = [];
  for (let i = 0; i < 81; i++) {
    const r = Math.floor(i / 9);
    const c = i % 9;
    const b = boxIndex(r, c);
    if (board[i] !== 0) {
      const bit = 1 << (board[i] - 1);
      rows[r] |= bit;
      cols[c] |= bit;
      boxes[b] |= bit;
    } else {
      empties.push(i);
    }
  }
  const working = board.slice();
  let count = 0;
  let firstSolution = null;

  function candidatesFor(i) {
    const r = Math.floor(i / 9);
    const c = i % 9;
    const b = boxIndex(r, c);
    const used = rows[r] | cols[c] | boxes[b];
    const cand = [];
    for (let d = 1; d <= 9; d++) {
      if (!(used & (1 << (d - 1)))) cand.push(d);
    }
    return cand;
  }

  function backtrack(remaining) {
    if (count >= countLimit) return;
    if (remaining.length === 0) {
      count++;
      if (!firstSolution) firstSolution = working.slice();
      return;
    }
    let bestIdx = -1;
    let bestCand = null;
    let bestLen = 10;
    for (const i of remaining) {
      const cand = candidatesFor(i);
      if (cand.length < bestLen) {
        bestLen = cand.length;
        bestCand = cand;
        bestIdx = i;
        if (bestLen === 0) break;
      }
    }
    if (bestLen === 0) return;
    const rest = remaining.filter((x) => x !== bestIdx);
    const r = Math.floor(bestIdx / 9);
    const c = bestIdx % 9;
    const b = boxIndex(r, c);
    const order = randomize ? shuffle(bestCand, rng) : bestCand;
    for (const d of order) {
      const bit = 1 << (d - 1);
      working[bestIdx] = d;
      rows[r] |= bit;
      cols[c] |= bit;
      boxes[b] |= bit;
      backtrack(rest);
      rows[r] &= ~bit;
      cols[c] &= ~bit;
      boxes[b] &= ~bit;
      working[bestIdx] = 0;
      if (count >= countLimit) return;
    }
  }
  backtrack(empties);
  return { count, solution: firstSolution };
}

function generateSolvedBoard(rng) {
  const board = new Array(81).fill(0);
  const { solution } = solve(board, { countLimit: 1, randomize: true, rng });
  return solution;
}

function generatePuzzle(rng, difficulty) {
  const solution = generateSolvedBoard(rng);
  const puzzle = solution.slice();
  const target = DIFF_GIVENS[difficulty] || 34;
  let givens = 81;
  const order = shuffle(
    Array.from({ length: 81 }, (_, i) => i),
    rng
  );
  for (const idx of order) {
    if (givens <= target) break;
    const backup = puzzle[idx];
    if (backup === 0) continue;
    puzzle[idx] = 0;
    const { count } = solve(puzzle, { countLimit: 2 });
    if (count !== 1) {
      puzzle[idx] = backup;
    } else {
      givens--;
    }
  }
  return { puzzle, solution };
}

function peersOf(idx) {
  const r = Math.floor(idx / 9);
  const c = idx % 9;
  const b = boxIndex(r, c);
  const peers = [];
  for (let i = 0; i < 81; i++) {
    if (i === idx) continue;
    const ri = Math.floor(i / 9);
    const ci = i % 9;
    if (ri === r || ci === c || boxIndex(ri, ci) === b) peers.push(i);
  }
  return peers;
}

/* =========================================================================
   遊戲物件建立 / 讀存
   ========================================================================= */

function createGame(mode, difficulty, rng, dateStr) {
  const { puzzle, solution } = generatePuzzle(rng, difficulty);
  const firstEmpty = puzzle.findIndex((v) => v === 0);
  return {
    mode,
    difficulty,
    date: dateStr || null,
    puzzle,
    solution,
    given: puzzle.map((v) => v !== 0),
    board: puzzle.slice(),
    notes: Array.from({ length: 81 }, () => []),
    seconds: 0,
    running: true,
    mistakes: 0,
    hints: 0,
    notesMode: false,
    selected: firstEmpty >= 0 ? firstEmpty : null,
    victory: false,
  };
}

function serializeGame(g) {
  const { undoStack, ...rest } = g;
  return JSON.stringify(rest);
}

function defaultStats() {
  return {
    totalGames: 0,
    totalSeconds: 0,
    totalMistakes: 0,
    totalHints: 0,
    counts: { easy: 0, medium: 0, hard: 0, expert: 0 },
    bestTimes: { easy: null, medium: null, hard: null, expert: null },
    history: [],
  };
}
function defaultDaily() {
  return { completedDates: [], currentStreak: 0, bestStreak: 0, lastCompletedDate: null };
}

/* =========================================================================
   小元件
   ========================================================================= */

function SegButton({ active, onClick, children, disabled }) {
  return (
    <button className={`sj-seg${active ? " sj-seg-active" : ""}`} onClick={onClick} disabled={disabled}>
      {children}
    </button>
  );
}

function Board({ game, onSelect, sameGroup }) {
  const { board, given, notes, selected, mistakesMap } = game;
  const selVal = selected != null ? board[selected] : 0;
  const selR = selected != null ? Math.floor(selected / 9) : -1;
  const selC = selected != null ? selected % 9 : -1;
  const selB = selected != null ? boxIndex(selR, selC) : -1;

  return (
    <div className="sj-board" role="grid" aria-label="數獨棋盤">
      {board.map((val, i) => {
        const r = Math.floor(i / 9);
        const c = i % 9;
        const b = boxIndex(r, c);
        const isGiven = given[i];
        const isSel = i === selected;
        const isPeer = selected != null && (r === selR || c === selC || b === selB) && !isSel;
        const isSameVal = selVal !== 0 && val === selVal;
        const isWrong = !isGiven && val !== 0 && val !== game.solution[i];
        const classes = [
          "sj-cell",
          isGiven ? "sj-cell-given" : "sj-cell-entry",
          isSel ? "sj-cell-selected" : "",
          isPeer ? "sj-cell-peer" : "",
          isSameVal && !isSel ? "sj-cell-echo" : "",
          isWrong ? "sj-cell-wrong" : "",
          c % 3 === 0 ? "sj-border-l3" : "",
          r % 3 === 0 ? "sj-border-t3" : "",
        ]
          .filter(Boolean)
          .join(" ");
        return (
          <button key={i} className={classes} onClick={() => onSelect(i)} aria-label={`第${r + 1}列第${c + 1}行`}>
            {val !== 0 ? (
              <span className="sj-cell-value">{val}</span>
            ) : notes[i] && notes[i].length > 0 ? (
              <span className="sj-notes-grid">
                {Array.from({ length: 9 }, (_, n) => n + 1).map((n) => (
                  <span key={n} className="sj-note">
                    {notes[i].includes(n) ? n : ""}
                  </span>
                ))}
              </span>
            ) : null}
          </button>
        );
      })}
    </div>
  );
}

function NumberPad({ onDigit, boardCounts }) {
  return (
    <div className="sj-numpad">
      {Array.from({ length: 9 }, (_, i) => i + 1).map((n) => (
        <button key={n} className="sj-numkey" onClick={() => onDigit(n)}>
          <span>{n}</span>
          <span className="sj-numkey-remain">{Math.max(0, 9 - (boardCounts[n] || 0))}</span>
        </button>
      ))}
    </div>
  );
}

function StampCalendar({ completedDates, today }) {
  const days = [];
  for (let i = 27; i >= 0; i--) days.push(addDays(today, -i));
  return (
    <div className="sj-stampcal">
      {days.map((d) => {
        const done = completedDates.includes(d);
        const isToday = d === today;
        const rot = ((seedFromString(d) % 21) - 10) * 0.6;
        return (
          <div key={d} className={`sj-stampday${isToday ? " sj-stampday-today" : ""}`} title={d}>
            {done ? (
              <div className="sj-stamp" style={{ transform: `rotate(${rot}deg)` }}>
                <CheckCircle2 size={14} />
              </div>
            ) : (
              <div className="sj-stamp-empty">{Number(d.slice(-2))}</div>
            )}
          </div>
        );
      })}
    </div>
  );
}

/* =========================================================================
   主程式
   ========================================================================= */

export default function SudokuJournal() {
  const [tab, setTab] = useState("play");
  const [loaded, setLoaded] = useState(false);
  const [stats, setStats] = useState(defaultStats());
  const [daily, setDaily] = useState(defaultDaily());
  const [normalGame, setNormalGame] = useState(null);
  const [dailyGame, setDailyGame] = useState(null);
  const [pendingDifficulty, setPendingDifficulty] = useState("easy");
  const [confirmNew, setConfirmNew] = useState(false);
  const [generating, setGenerating] = useState(false);
  const [savedPulse, setSavedPulse] = useState(false);
  const undoRef = useRef({ normal: [], daily: [] });
  const saveTimerRef = useRef(null);

  /* ---------------- 初次載入 ---------------- */
  useEffect(() => {
    (async () => {
      let s = defaultStats();
      let d = defaultDaily();
      try {
        const r = await window.storage.get(K_STATS);
        if (r) s = { ...defaultStats(), ...JSON.parse(r.value) };
      } catch (e) {}
      try {
        const r = await window.storage.get(K_DAILY);
        if (r) d = { ...defaultDaily(), ...JSON.parse(r.value) };
      } catch (e) {}
      setStats(s);
      setDaily(d);

      // 一般模式：讀取進行中的存檔，否則產生新題
      let ng = null;
      try {
        const r = await window.storage.get(K_ACTIVE_NORMAL);
        if (r) ng = JSON.parse(r.value);
      } catch (e) {}
      if (ng) {
        ng.running = false;
        setPendingDifficulty(ng.difficulty);
        setNormalGame(ng);
      } else {
        const diff = "easy";
        setPendingDifficulty(diff);
        const rng = mulberry32((Math.random() * 1e9) | 0);
        setNormalGame(createGame("normal", diff, rng));
      }

      // 每日挑戰
      const today = todayStr();
      const alreadyDone = d.completedDates.includes(today);
      let dg = null;
      try {
        const r = await window.storage.get(K_ACTIVE_DAILY);
        if (r) dg = JSON.parse(r.value);
      } catch (e) {}
      if (!alreadyDone) {
        if (dg && dg.date === today) {
          dg.running = false;
          setDailyGame(dg);
        } else {
          const diff = WEEKDAY_DIFF[weekdayOf(today)];
          const rng = mulberry32(seedFromString("daily-" + today));
          setDailyGame(createGame("daily", diff, rng, today));
        }
      } else {
        setDailyGame(dg && dg.date === today ? dg : null);
      }

      setLoaded(true);
    })();
  }, []);

  /* ---------------- 自動存檔（debounce） ---------------- */
  const scheduleSave = useCallback((key, gameObj) => {
    if (saveTimerRef.current) clearTimeout(saveTimerRef.current[key]);
    if (!saveTimerRef.current) saveTimerRef.current = {};
    saveTimerRef.current[key] = setTimeout(async () => {
      try {
        await window.storage.set(key, serializeGame(gameObj), false);
        setSavedPulse(true);
        setTimeout(() => setSavedPulse(false), 1200);
      } catch (e) {}
    }, 600);
  }, []);

  useEffect(() => {
    if (!loaded || !normalGame) return;
    scheduleSave(K_ACTIVE_NORMAL, normalGame);
  }, [normalGame, loaded, scheduleSave]);

  useEffect(() => {
    if (!loaded || !dailyGame) return;
    scheduleSave(K_ACTIVE_DAILY, dailyGame);
  }, [dailyGame, loaded, scheduleSave]);

  /* ---------------- 計時器 ---------------- */
  useEffect(() => {
    if (tab !== "play" || !normalGame || !normalGame.running || normalGame.victory) return;
    const t = setInterval(() => {
      setNormalGame((g) => (g ? { ...g, seconds: g.seconds + 1 } : g));
    }, 1000);
    return () => clearInterval(t);
  }, [tab, normalGame && normalGame.running, normalGame && normalGame.victory, normalGame === null]);

  useEffect(() => {
    if (tab !== "daily" || !dailyGame || !dailyGame.running || dailyGame.victory) return;
    const t = setInterval(() => {
      setDailyGame((g) => (g ? { ...g, seconds: g.seconds + 1 } : g));
    }, 1000);
    return () => clearInterval(t);
  }, [tab, dailyGame && dailyGame.running, dailyGame && dailyGame.victory, dailyGame === null]);

  /* ---------------- 完成處理 ---------------- */
  const finalizeStats = useCallback((g) => {
    setStats((prev) => {
      const next = {
        ...prev,
        totalGames: prev.totalGames + 1,
        totalSeconds: prev.totalSeconds + g.seconds,
        totalMistakes: prev.totalMistakes + g.mistakes,
        totalHints: prev.totalHints + g.hints,
        counts: { ...prev.counts, [g.difficulty]: (prev.counts[g.difficulty] || 0) + 1 },
        bestTimes: {
          ...prev.bestTimes,
          [g.difficulty]:
            prev.bestTimes[g.difficulty] == null ? g.seconds : Math.min(prev.bestTimes[g.difficulty], g.seconds),
        },
        history: [
          ...prev.history,
          {
            id: `${Date.now()}-${Math.random().toString(36).slice(2, 7)}`,
            date: todayStr(),
            mode: g.mode,
            difficulty: g.difficulty,
            seconds: g.seconds,
            mistakes: g.mistakes,
            hints: g.hints,
          },
        ].slice(-60),
      };
      window.storage.set(K_STATS, JSON.stringify(next), false).catch(() => {});
      return next;
    });
  }, []);

  const finalizeDaily = useCallback((g) => {
    setDaily((prev) => {
      const today = todayStr();
      if (prev.completedDates.includes(today)) return prev;
      const yesterday = addDays(today, -1);
      const streak = prev.lastCompletedDate === yesterday ? prev.currentStreak + 1 : 1;
      const next = {
        completedDates: [...prev.completedDates, today].slice(-120),
        currentStreak: streak,
        bestStreak: Math.max(prev.bestStreak, streak),
        lastCompletedDate: today,
      };
      window.storage.set(K_DAILY, JSON.stringify(next), false).catch(() => {});
      window.storage.delete(K_ACTIVE_DAILY, false).catch(() => {});
      return next;
    });
  }, []);

  /* ---------------- 遊戲動作（一般 / 每日 共用邏輯） ---------------- */
  function makeActions(game, setGame, undoKey, onWin) {
    function pushUndo() {
      const stack = undoRef.current[undoKey];
      stack.push({ board: game.board.slice(), notes: game.notes.map((n) => n.slice()), mistakes: game.mistakes });
      if (stack.length > 50) stack.shift();
    }

    function checkVictory(board) {
      return board.every((v) => v !== 0) && arraysEqual(board, game.solution);
    }

    function select(i) {
      setGame((g) => ({ ...g, selected: i }));
    }

    function inputDigit(d) {
      if (!game || game.victory || game.selected == null) return;
      const idx = game.selected;
      if (game.given[idx]) return;
      pushUndo();
      if (game.notesMode) {
        setGame((g) => {
          const notes = g.notes.map((n) => n.slice());
          const cur = notes[idx];
          const pos = cur.indexOf(d);
          if (pos >= 0) cur.splice(pos, 1);
          else {
            cur.push(d);
            cur.sort((a, b) => a - b);
          }
          return { ...g, notes };
        });
        return;
      }
      setGame((g) => {
        const board = g.board.slice();
        board[idx] = d;
        const notes = g.notes.map((n) => n.slice());
        notes[idx] = [];
        for (const p of peersOf(idx)) {
          const pos = notes[p].indexOf(d);
          if (pos >= 0) notes[p] = notes[p].filter((x) => x !== d);
        }
        const wrong = d !== g.solution[idx];
        const win = checkVictory(board);
        const nextG = {
          ...g,
          board,
          notes,
          mistakes: wrong ? g.mistakes + 1 : g.mistakes,
          victory: win,
          running: win ? false : g.running,
        };
        if (win) onWin(nextG);
        return nextG;
      });
    }

    function erase() {
      if (!game || game.victory || game.selected == null) return;
      const idx = game.selected;
      if (game.given[idx]) return;
      pushUndo();
      setGame((g) => {
        const board = g.board.slice();
        board[idx] = 0;
        const notes = g.notes.map((n) => n.slice());
        notes[idx] = [];
        return { ...g, board, notes };
      });
    }

    function undo() {
      const stack = undoRef.current[undoKey];
      if (stack.length === 0) return;
      const snap = stack.pop();
      setGame((g) => ({ ...g, board: snap.board, notes: snap.notes, mistakes: snap.mistakes, victory: false, running: true }));
    }

    function hint() {
      if (!game || game.victory) return;
      let target = game.selected;
      if (target == null || game.board[target] !== 0) {
        target = game.board.findIndex((v) => v === 0);
      }
      if (target == null || target < 0) return;
      pushUndo();
      setGame((g) => {
        const board = g.board.slice();
        board[target] = g.solution[target];
        const notes = g.notes.map((n) => n.slice());
        notes[target] = [];
        for (const p of peersOf(target)) {
          notes[p] = notes[p].filter((x) => x !== g.solution[target]);
        }
        const win = checkVictory(board);
        const nextG = { ...g, board, notes, hints: g.hints + 1, selected: target, victory: win, running: win ? false : g.running };
        if (win) onWin(nextG);
        return nextG;
      });
    }

    function toggleNotes() {
      setGame((g) => ({ ...g, notesMode: !g.notesMode }));
    }

    function togglePause() {
      setGame((g) => (g.victory ? g : { ...g, running: !g.running }));
    }

    function move(dr, dc) {
      if (!game || game.selected == null) return;
      const r = Math.floor(game.selected / 9);
      const c = game.selected % 9;
      const nr = Math.min(8, Math.max(0, r + dr));
      const nc = Math.min(8, Math.max(0, c + dc));
      select(nr * 9 + nc);
    }

    return { select, inputDigit, erase, undo, hint, toggleNotes, togglePause, move };
  }

  const normalActions = useMemo(
    () =>
      normalGame
        ? makeActions(normalGame, setNormalGame, "normal", (g) => finalizeStats(g))
        : null,
    [normalGame, finalizeStats]
  );
  const dailyActions = useMemo(
    () =>
      dailyGame
        ? makeActions(dailyGame, setDailyGame, "daily", (g) => {
            finalizeStats(g);
            finalizeDaily(g);
          })
        : null,
    [dailyGame, finalizeStats, finalizeDaily]
  );

  /* ---------------- 鍵盤 ---------------- */
  useEffect(() => {
    function onKey(e) {
      const isPlay = tab === "play" && normalGame && normalActions;
      const isDaily = tab === "daily" && dailyGame && dailyActions && !dailyGame.victory;
      if (!isPlay && !isDaily) return;
      const actions = isPlay ? normalActions : dailyActions;
      const g = isPlay ? normalGame : dailyGame;
      if (g.victory) return;
      if (e.key >= "1" && e.key <= "9") {
        actions.inputDigit(Number(e.key));
        e.preventDefault();
      } else if (e.key === "0" || e.key === "Backspace" || e.key === "Delete") {
        actions.erase();
        e.preventDefault();
      } else if (e.key === "ArrowUp") {
        actions.move(-1, 0);
        e.preventDefault();
      } else if (e.key === "ArrowDown") {
        actions.move(1, 0);
        e.preventDefault();
      } else if (e.key === "ArrowLeft") {
        actions.move(0, -1);
        e.preventDefault();
      } else if (e.key === "ArrowRight") {
        actions.move(0, 1);
        e.preventDefault();
      }
    }
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [tab, normalGame, dailyGame, normalActions, dailyActions]);

  /* ---------------- 新局 ---------------- */
  function startNewNormalGame(diff) {
    setGenerating(true);
    setTimeout(() => {
      const rng = mulberry32((Math.random() * 1e9) | 0);
      const g = createGame("normal", diff, rng);
      undoRef.current.normal = [];
      setNormalGame(g);
      setGenerating(false);
      setConfirmNew(false);
    }, 30);
  }

  function restartSamePuzzle(which) {
    if (which === "normal" && normalGame) {
      undoRef.current.normal = [];
      setNormalGame((g) => ({
        ...g,
        board: g.puzzle.slice(),
        notes: Array.from({ length: 81 }, () => []),
        seconds: 0,
        mistakes: 0,
        hints: 0,
        victory: false,
        running: true,
        selected: g.puzzle.findIndex((v) => v === 0),
      }));
    }
  }

  const inProgress = (g) => g && (g.seconds > 0 || g.board.some((v, i) => !g.given[i] && v !== 0));

  /* ---------------- 統計數字 ---------------- */
  const boardDigitCounts = (board) => {
    const counts = {};
    for (const v of board) if (v !== 0) counts[v] = (counts[v] || 0) + 1;
    return counts;
  };

  const chartData = useMemo(
    () =>
      stats.history.slice(-16).map((h, i) => ({
        idx: i + 1,
        label: formatDateLabel(h.date),
        seconds: h.seconds,
        difficulty: DIFF_LABEL[h.difficulty],
      })),
    [stats.history]
  );

  const today = todayStr();
  const dailyDoneToday = daily.completedDates.includes(today);
  const todayEntry = stats.history.filter((h) => h.mode === "daily" && h.date === today).slice(-1)[0];

  if (!loaded) {
    return (
      <div className="sj-root sj-loading">
        <style>{CSS}</style>
        <div className="sj-loading-text">正在攤開棋盤...</div>
      </div>
    );
  }

  return (
    <div className="sj-root">
      <style>{CSS}</style>

      <header className="sj-header">
        <div className="sj-brand">
          <div className="sj-brand-mark">數</div>
          <div>
            <div className="sj-brand-title">數獨手帳</div>
            <div className="sj-brand-sub">SUDOKU JOURNAL</div>
          </div>
        </div>
        <nav className="sj-tabs">
          <SegButton active={tab === "play"} onClick={() => setTab("play")}>對局</SegButton>
          <SegButton active={tab === "daily"} onClick={() => setTab("daily")}>
            每日挑戰{daily.currentStreak > 0 ? ` 🔥${daily.currentStreak}` : ""}
          </SegButton>
          <SegButton active={tab === "stats"} onClick={() => setTab("stats")}>生涯總覽</SegButton>
        </nav>
      </header>

      {tab === "play" && normalGame && (
        <section className="sj-panel">
          <div className="sj-toolrow">
            <div className="sj-diffseg">
              {DIFF_ORDER.map((d) => (
                <SegButton
                  key={d}
                  active={pendingDifficulty === d}
                  onClick={() => {
                    setPendingDifficulty(d);
                    if (inProgress(normalGame) && d !== normalGame.difficulty) setConfirmNew(true);
                    else if (d !== normalGame.difficulty) startNewNormalGame(d);
                  }}
                >
                  {DIFF_LABEL[d]}
                </SegButton>
              ))}
            </div>
            <button
              className="sj-iconbtn"
              onClick={() => (inProgress(normalGame) ? setConfirmNew(true) : startNewNormalGame(pendingDifficulty))}
              title="開新局"
            >
              <RefreshCw size={16} /> 開新局
            </button>
          </div>

          {confirmNew && (
            <div className="sj-confirm">
              <span>目前進度尚未完成，確定要開始新的一局嗎？</span>
              <div className="sj-confirm-btns">
                <button className="sj-confirm-yes" onClick={() => startNewNormalGame(pendingDifficulty)}>
                  確定
                </button>
                <button
                  className="sj-confirm-no"
                  onClick={() => {
                    setPendingDifficulty(normalGame.difficulty);
                    setConfirmNew(false);
                  }}
                >
                  取消
                </button>
              </div>
            </div>
          )}

          <div className="sj-infobar">
            <span className="sj-badge">{DIFF_LABEL[normalGame.difficulty]}</span>
            <span className="sj-info">
              <Clock size={14} /> {formatTime(normalGame.seconds)}
            </span>
            <span className="sj-info">錯誤 {normalGame.mistakes}</span>
            <span className="sj-info">提示 {normalGame.hints}</span>
            <button className="sj-iconbtn sj-iconbtn-ghost" onClick={normalActions.togglePause}>
              {normalGame.running ? <Pause size={15} /> : <PlayIcon size={15} />}
            </button>
            <span className={`sj-savepulse${savedPulse ? " sj-savepulse-on" : ""}`}>已自動儲存</span>
          </div>

          <div className="sj-boardwrap">
            {!normalGame.running && !normalGame.victory && (
              <div className="sj-pauseoverlay" onClick={normalActions.togglePause}>
                <PlayIcon size={28} />
                <span>已暫停，點擊繼續</span>
              </div>
            )}
            <Board game={normalGame} onSelect={normalActions.select} />
          </div>

          {generating && <div className="sj-generating">產生題目中...</div>}

          {normalGame.victory ? (
            <div className="sj-victory">
              <Trophy size={22} />
              <div>
                <div className="sj-victory-title">完成！{DIFF_LABEL[normalGame.difficulty]}難度</div>
                <div className="sj-victory-sub">
                  用時 {formatTime(normalGame.seconds)}・錯誤 {normalGame.mistakes} 次・提示 {normalGame.hints} 次
                </div>
              </div>
              <button className="sj-primarybtn" onClick={() => startNewNormalGame(pendingDifficulty)}>
                再來一局
              </button>
            </div>
          ) : (
            <>
              <NumberPad
                onDigit={normalActions.inputDigit}
                boardCounts={boardDigitCounts(normalGame.board)}
              />
              <div className="sj-actionrow">
                <button className="sj-actionbtn" onClick={normalActions.undo}>
                  <Undo2 size={16} /> 復原
                </button>
                <button
                  className={`sj-actionbtn${normalGame.notesMode ? " sj-actionbtn-active" : ""}`}
                  onClick={normalActions.toggleNotes}
                >
                  <PenLine size={16} /> 筆記{normalGame.notesMode ? "中" : ""}
                </button>
                <button className="sj-actionbtn" onClick={normalActions.erase}>
                  <Eraser size={16} /> 清除
                </button>
                <button className="sj-actionbtn" onClick={normalActions.hint}>
                  <Lightbulb size={16} /> 提示
                </button>
                <button className="sj-actionbtn" onClick={() => restartSamePuzzle("normal")}>
                  <RotateCcw size={16} /> 重新開始
                </button>
              </div>
            </>
          )}
        </section>
      )}

      {tab === "daily" && (
        <section className="sj-panel">
          <div className="sj-dailyhead">
            <div>
              <div className="sj-dailydate">{today}</div>
              <div className="sj-dailysub">
                今日難度：{WEEKDAY_DIFF[weekdayOf(today)] && DIFF_LABEL[WEEKDAY_DIFF[weekdayOf(today)]]}
              </div>
            </div>
            <div className="sj-streakbox">
              <Flame size={18} />
              <div>
                <div className="sj-streaknum">{daily.currentStreak}</div>
                <div className="sj-streaklabel">連勝天數</div>
              </div>
            </div>
          </div>

          <StampCalendar completedDates={daily.completedDates} today={today} />

          {dailyDoneToday ? (
            <div className="sj-victory sj-victory-static">
              <CheckCircle2 size={22} />
              <div>
                <div className="sj-victory-title">今日挑戰已完成</div>
                <div className="sj-victory-sub">
                  {todayEntry
                    ? `用時 ${formatTime(todayEntry.seconds)}・最佳連勝 ${daily.bestStreak} 天`
                    : `最佳連勝 ${daily.bestStreak} 天`}
                </div>
              </div>
            </div>
          ) : dailyGame && dailyActions ? (
            <>
              <div className="sj-infobar">
                <span className="sj-badge">{DIFF_LABEL[dailyGame.difficulty]}</span>
                <span className="sj-info">
                  <Clock size={14} /> {formatTime(dailyGame.seconds)}
                </span>
                <span className="sj-info">錯誤 {dailyGame.mistakes}</span>
                <span className="sj-info">提示 {dailyGame.hints}</span>
                <button className="sj-iconbtn sj-iconbtn-ghost" onClick={dailyActions.togglePause}>
                  {dailyGame.running ? <Pause size={15} /> : <PlayIcon size={15} />}
                </button>
              </div>
              <div className="sj-boardwrap">
                {!dailyGame.running && !dailyGame.victory && (
                  <div className="sj-pauseoverlay" onClick={dailyActions.togglePause}>
                    <PlayIcon size={28} />
                    <span>已暫停，點擊繼續</span>
                  </div>
                )}
                <Board game={dailyGame} onSelect={dailyActions.select} />
              </div>
              <NumberPad
                onDigit={dailyActions.inputDigit}
                boardCounts={boardDigitCounts(dailyGame.board)}
              />
              <div className="sj-actionrow">
                <button className="sj-actionbtn" onClick={dailyActions.undo}>
                  <Undo2 size={16} /> 復原
                </button>
                <button
                  className={`sj-actionbtn${dailyGame.notesMode ? " sj-actionbtn-active" : ""}`}
                  onClick={dailyActions.toggleNotes}
                >
                  <PenLine size={16} /> 筆記{dailyGame.notesMode ? "中" : ""}
                </button>
                <button className="sj-actionbtn" onClick={dailyActions.erase}>
                  <Eraser size={16} /> 清除
                </button>
                <button className="sj-actionbtn" onClick={dailyActions.hint}>
                  <Lightbulb size={16} /> 提示
                </button>
              </div>
            </>
          ) : (
            <div className="sj-generating">產生題目中...</div>
          )}
        </section>
      )}

      {tab === "stats" && (
        <section className="sj-panel">
          <div className="sj-statgrid">
            <div className="sj-statcard">
              <div className="sj-statnum">{stats.totalGames}</div>
              <div className="sj-statlabel">總完成局數</div>
            </div>
            <div className="sj-statcard">
              <div className="sj-statnum">{formatTime(stats.totalSeconds)}</div>
              <div className="sj-statlabel">累積遊玩時間</div>
            </div>
            <div className="sj-statcard">
              <div className="sj-statnum">{daily.bestStreak}</div>
              <div className="sj-statlabel">最佳連勝</div>
            </div>
            <div className="sj-statcard">
              <div className="sj-statnum">{stats.totalHints}</div>
              <div className="sj-statlabel">使用提示次數</div>
            </div>
          </div>

          <div className="sj-bestgrid">
            {DIFF_ORDER.map((d) => (
              <div key={d} className="sj-bestcard">
                <div className="sj-bestdiff">{DIFF_LABEL[d]}</div>
                <div className="sj-besttime">{stats.bestTimes[d] != null ? formatTime(stats.bestTimes[d]) : "—"}</div>
                <div className="sj-bestcount">{stats.counts[d] || 0} 局</div>
              </div>
            ))}
          </div>

          <div className="sj-chartbox">
            <div className="sj-chartlabel">最近作答時間（秒）</div>
            {chartData.length > 1 ? (
              <ResponsiveContainer width="100%" height={160}>
                <LineChart data={chartData} margin={{ top: 8, right: 12, bottom: 0, left: -18 }}>
                  <CartesianGrid stroke="#39415133" vertical={false} />
                  <XAxis dataKey="label" tick={{ fontSize: 10, fill: "#9CA7B8" }} axisLine={{ stroke: "#39415155" }} tickLine={false} />
                  <YAxis tick={{ fontSize: 10, fill: "#9CA7B8" }} axisLine={false} tickLine={false} />
                  <Tooltip
                    contentStyle={{ background: "#232935", border: "1px solid #3A4254", borderRadius: 8, fontSize: 12 }}
                    labelStyle={{ color: "#E8E2D0" }}
                    formatter={(v, n, p) => [formatTime(v), p.payload.difficulty]}
                  />
                  <Line type="monotone" dataKey="seconds" stroke="#C9A227" strokeWidth={2} dot={{ r: 3, fill: "#B23A2E" }} />
                </LineChart>
              </ResponsiveContainer>
            ) : (
              <div className="sj-emptynote">完成 2 局以上即可看到進步曲線</div>
            )}
          </div>

          <div className="sj-historylist">
            <div className="sj-chartlabel">近期紀錄</div>
            {stats.history.length === 0 && <div className="sj-emptynote">還沒有完成紀錄，去解一局吧！</div>}
            {stats.history
              .slice()
              .reverse()
              .slice(0, 12)
              .map((h) => (
                <div key={h.id} className="sj-historyrow">
                  <span className="sj-historydate">{h.date}</span>
                  <span className="sj-historytag">{h.mode === "daily" ? "每日" : DIFF_LABEL[h.difficulty]}</span>
                  <span className="sj-historytime">{formatTime(h.seconds)}</span>
                  <span className="sj-historymeta">錯{h.mistakes}・提示{h.hints}</span>
                </div>
              ))}
          </div>
        </section>
      )}
    </div>
  );
}

/* =========================================================================
   樣式
   ========================================================================= */

const CSS = `
@import url('https://fonts.googleapis.com/css2?family=Noto+Serif+TC:wght@500;700&family=Noto+Sans+TC:wght@400;500;700&family=Spectral:ital,wght@0,500;1,500&display=swap');

.sj-root {
  --ink-900: #14181F;
  --ink-800: #1A1F28;
  --ink-700: #232935;
  --ink-600: #2C3341;
  --line: #3A4254;
  --paper: #F3ECD9;
  --paper-line: #D9CCA6;
  --paper-line-strong: #A8996E;
  --blue: #3E6B94;
  --blue-deep: #2A4D6E;
  --red: #B23A2E;
  --gold: #C9A227;
  --sage: #6E9277;
  --text: #E8E2D0;
  --text-dim: #9CA7B8;
  font-family: 'Noto Sans TC', -apple-system, BlinkMacSystemFont, sans-serif;
  background: radial-gradient(circle at 20% 0%, #1B2130 0%, var(--ink-900) 55%);
  color: var(--text);
  min-height: 100vh;
  padding: 20px 14px 40px;
  box-sizing: border-box;
}
.sj-root * { box-sizing: border-box; }
.sj-loading { display: flex; align-items: center; justify-content: center; }
.sj-loading-text { color: var(--text-dim); font-family: 'Noto Serif TC', serif; letter-spacing: 0.08em; }

.sj-header {
  max-width: 480px;
  margin: 0 auto 18px;
  display: flex;
  flex-direction: column;
  gap: 14px;
}
.sj-brand { display: flex; align-items: center; gap: 10px; }
.sj-brand-mark {
  width: 40px; height: 40px;
  border-radius: 10px;
  background: linear-gradient(160deg, var(--blue), var(--blue-deep));
  color: var(--paper);
  display: flex; align-items: center; justify-content: center;
  font-family: 'Noto Serif TC', serif;
  font-weight: 700;
  font-size: 19px;
  box-shadow: 0 3px 10px #00000055;
}
.sj-brand-title { font-family: 'Noto Serif TC', serif; font-weight: 700; font-size: 19px; letter-spacing: 0.02em; }
.sj-brand-sub { font-family: 'Spectral', serif; font-style: italic; font-size: 10.5px; color: var(--text-dim); letter-spacing: 0.16em; margin-top: 1px; }

.sj-tabs { display: flex; gap: 6px; background: var(--ink-700); padding: 4px; border-radius: 12px; border: 1px solid var(--line); }
.sj-seg {
  flex: 1;
  background: transparent;
  border: none;
  color: var(--text-dim);
  font-family: 'Noto Sans TC', sans-serif;
  font-size: 12.5px;
  font-weight: 500;
  padding: 8px 6px;
  border-radius: 8px;
  cursor: pointer;
  transition: background .15s, color .15s;
  white-space: nowrap;
}
.sj-seg-active { background: var(--blue-deep); color: var(--paper); }
.sj-seg:disabled { opacity: 0.5; cursor: default; }

.sj-panel { max-width: 480px; margin: 0 auto; display: flex; flex-direction: column; gap: 14px; }

.sj-toolrow { display: flex; align-items: center; justify-content: space-between; gap: 8px; }
.sj-diffseg { display: flex; gap: 4px; background: var(--ink-700); border: 1px solid var(--line); border-radius: 10px; padding: 3px; flex: 1; }
.sj-diffseg .sj-seg { font-size: 11.5px; padding: 6px 4px; }

.sj-iconbtn {
  display: flex; align-items: center; gap: 6px;
  background: var(--ink-700); color: var(--text);
  border: 1px solid var(--line); border-radius: 10px;
  padding: 7px 11px; font-size: 12px; cursor: pointer;
  white-space: nowrap;
}
.sj-iconbtn-ghost { padding: 6px 8px; margin-left: auto; }

.sj-confirm {
  background: #2A1F1D; border: 1px solid #5A362E; border-radius: 10px;
  padding: 10px 12px; font-size: 12.5px; display: flex; flex-direction: column; gap: 8px;
}
.sj-confirm-btns { display: flex; gap: 8px; }
.sj-confirm-yes, .sj-confirm-no {
  border-radius: 8px; border: none; padding: 6px 12px; font-size: 12px; cursor: pointer; font-family: inherit;
}
.sj-confirm-yes { background: var(--red); color: #fff; }
.sj-confirm-no { background: var(--ink-600); color: var(--text); }

.sj-infobar { display: flex; align-items: center; gap: 10px; flex-wrap: wrap; font-size: 12.5px; color: var(--text-dim); }
.sj-badge { background: var(--blue-deep); color: var(--paper); border-radius: 20px; padding: 3px 10px; font-size: 11px; font-weight: 600; }
.sj-info { display: flex; align-items: center; gap: 4px; }
.sj-savepulse { margin-left: auto; font-size: 10.5px; opacity: 0; transition: opacity .4s; }
.sj-savepulse-on { opacity: 0.8; }

.sj-boardwrap { position: relative; width: min(94vw, 440px); margin: 0 auto; }
.sj-pauseoverlay {
  position: absolute; inset: 0; z-index: 5;
  background: #14181Fdd; backdrop-filter: blur(3px);
  display: flex; flex-direction: column; align-items: center; justify-content: center; gap: 8px;
  border-radius: 8px; cursor: pointer; color: var(--paper); font-size: 13px;
}

.sj-board {
  display: grid;
  grid-template-columns: repeat(9, 1fr);
  width: 100%;
  aspect-ratio: 1;
  background: var(--paper);
  border: 2.5px solid var(--paper-line-strong);
  border-radius: 6px;
  overflow: hidden;
  box-shadow: 0 8px 24px #00000066;
}
.sj-cell {
  position: relative;
  border: none;
  border-right: 1px solid var(--paper-line);
  border-bottom: 1px solid var(--paper-line);
  background: transparent;
  display: flex; align-items: center; justify-content: center;
  cursor: pointer;
  padding: 0;
}
.sj-border-l3 { border-left: 1.5px solid var(--paper-line-strong); }
.sj-border-t3 { border-top: 1.5px solid var(--paper-line-strong); }
.sj-cell-value { font-size: clamp(13px, 3.6vw, 19px); font-variant-numeric: tabular-nums; }
.sj-cell-given .sj-cell-value { color: var(--blue-deep); font-weight: 700; font-family: 'Noto Serif TC', serif; }
.sj-cell-entry .sj-cell-value { color: #3A3226; font-weight: 500; }
.sj-cell-peer { background: #E4DBC1; }
.sj-cell-echo { background: #D9CBA0; }
.sj-cell-selected { background: #C9DCEA; }
.sj-cell-wrong .sj-cell-value { color: var(--red); }
.sj-notes-grid { display: grid; grid-template-columns: repeat(3, 1fr); width: 84%; height: 84%; }
.sj-note { font-size: clamp(6px, 1.6vw, 8.5px); color: #8A7F63; display: flex; align-items: center; justify-content: center; }

.sj-generating { text-align: center; font-size: 12.5px; color: var(--text-dim); padding: 6px; }

.sj-numpad { display: grid; grid-template-columns: repeat(9, 1fr); gap: 5px; width: min(94vw, 440px); margin: 0 auto; }
.sj-numkey {
  aspect-ratio: 1; background: var(--ink-700); border: 1px solid var(--line); border-radius: 8px;
  color: var(--text); display: flex; flex-direction: column; align-items: center; justify-content: center;
  cursor: pointer; font-size: 15px; font-weight: 600; gap: 1px;
}
.sj-numkey-remain { font-size: 8px; color: var(--text-dim); font-weight: 400; }

.sj-actionrow { display: flex; flex-wrap: wrap; gap: 6px; width: min(94vw, 440px); margin: 0 auto; }
.sj-actionbtn {
  flex: 1 1 18%; min-width: 60px; display: flex; flex-direction: column; align-items: center; gap: 3px;
  background: var(--ink-700); border: 1px solid var(--line); border-radius: 10px;
  color: var(--text-dim); font-size: 10.5px; padding: 8px 4px; cursor: pointer;
}
.sj-actionbtn-active { background: var(--blue-deep); color: var(--paper); border-color: var(--blue); }

.sj-victory {
  display: flex; align-items: center; gap: 12px;
  background: linear-gradient(135deg, #2B3A2E, #1F2A22);
  border: 1px solid #4A6650; border-radius: 12px; padding: 14px; color: var(--sage);
}
.sj-victory-static { justify-content: flex-start; }
.sj-victory-title { font-family: 'Noto Serif TC', serif; font-weight: 700; font-size: 15px; color: var(--paper); }
.sj-victory-sub { font-size: 11.5px; color: #A9C2AE; margin-top: 2px; }
.sj-primarybtn {
  margin-left: auto; background: var(--gold); color: #2A2110; border: none; border-radius: 9px;
  padding: 9px 14px; font-size: 12.5px; font-weight: 700; cursor: pointer; white-space: nowrap;
}

.sj-dailyhead { display: flex; align-items: center; justify-content: space-between; }
.sj-dailydate { font-family: 'Noto Serif TC', serif; font-size: 17px; font-weight: 700; }
.sj-dailysub { font-size: 11.5px; color: var(--text-dim); margin-top: 2px; }
.sj-streakbox { display: flex; align-items: center; gap: 8px; background: #2E241A; border: 1px solid #6B4A28; border-radius: 12px; padding: 8px 12px; color: var(--gold); }
.sj-streaknum { font-size: 18px; font-weight: 700; line-height: 1; }
.sj-streaklabel { font-size: 9.5px; color: #C9A96A; }

.sj-stampcal { display: grid; grid-template-columns: repeat(7, 1fr); gap: 5px; }
.sj-stampday { aspect-ratio: 1; display: flex; align-items: center; justify-content: center; }
.sj-stampday-today { outline: 1.5px dashed var(--gold); border-radius: 8px; }
.sj-stamp { color: var(--red); border: 1.5px solid var(--red); border-radius: 50%; width: 78%; height: 78%; display: flex; align-items: center; justify-content: center; background: #B23A2E1a; }
.sj-stamp-empty { color: var(--line); font-size: 10px; width: 100%; height: 100%; display: flex; align-items: center; justify-content: center; }

.sj-statgrid { display: grid; grid-template-columns: repeat(2, 1fr); gap: 8px; }
.sj-statcard { background: var(--ink-700); border: 1px solid var(--line); border-radius: 12px; padding: 12px; text-align: center; }
.sj-statnum { font-family: 'Noto Serif TC', serif; font-size: 20px; font-weight: 700; color: var(--gold); }
.sj-statlabel { font-size: 10.5px; color: var(--text-dim); margin-top: 3px; }

.sj-bestgrid { display: grid; grid-template-columns: repeat(4, 1fr); gap: 6px; }
.sj-bestcard { background: var(--ink-700); border: 1px solid var(--line); border-radius: 10px; padding: 8px 4px; text-align: center; }
.sj-bestdiff { font-size: 10.5px; color: var(--text-dim); }
.sj-besttime { font-size: 13px; font-weight: 700; margin-top: 3px; font-variant-numeric: tabular-nums; }
.sj-bestcount { font-size: 9.5px; color: var(--text-dim); margin-top: 2px; }

.sj-chartbox { background: var(--ink-700); border: 1px solid var(--line); border-radius: 12px; padding: 12px; }
.sj-chartlabel { font-size: 11.5px; color: var(--text-dim); margin-bottom: 6px; }
.sj-emptynote { font-size: 12px; color: var(--text-dim); text-align: center; padding: 14px 0; }

.sj-historylist { display: flex; flex-direction: column; gap: 6px; }
.sj-historyrow {
  display: flex; align-items: center; gap: 10px;
  background: var(--ink-700); border: 1px solid var(--line); border-radius: 9px;
  padding: 8px 10px; font-size: 11.5px;
}
.sj-historydate { color: var(--text-dim); width: 62px; flex-shrink: 0; }
.sj-historytag { background: var(--ink-600); border-radius: 6px; padding: 2px 7px; font-size: 10px; }
.sj-historytime { font-weight: 700; font-variant-numeric: tabular-nums; margin-left: auto; }
.sj-historymeta { color: var(--text-dim); font-size: 10px; }

@media (min-width: 520px) {
  .sj-header { max-width: 520px; }
  .sj-panel { max-width: 520px; }
}
`;
