// Tiered Dip Hunter: a long-only cbBTC dip-buying bot for the make.fun 24h BTC race.
//
// The idea: BTC sells off in waves and bounces. The bot waits for the close to
// dip below the trailing 120-bar high, then scales into the dip in three tiers
// (-1.5% / -3% / -5% of the anchor), but only after a 1-minute bar closes above
// the previous bar's high — a small sign the selling has paused. It banks half
// the position at +1.2% over its average buy price, lets the rest run to +4.5%,
// and trails the remainder 0.8% below the highest close once the first profit
// is taken. A hard stop at -6.5% below the frozen anchor caps every cycle, and
// an equity brake at -15% from the peak halts the bot for the rest of the run.
// If nothing has traded by bar 1200 it buys once, full size, so the entry still
// has a chance to clear the dev gate.
//
// The bot is a pure function of the bars it is fed: no clock, no randomness,
// no environment reads, so two runs on the same window answer identically.

import { runBars } from './vendor/makefun-bars.ts';
import type { BarsState, Batch, OrderInput } from './vendor/makefun-bars.ts';

const SYMBOL = 'CBBTC';

// --- strategy parameters (percents are in basis points) ---
const LOOKBACK_BARS = 120; // anchor = highest close of the last 120 bars
const TIER_DIP_BPS = [150, 300, 500]; // buy tiers, as dips below the anchor
const TIER_NOTIONAL = [334_000_000n, 333_000_000n, 333_000_000n]; // quote units: $334 / $333 / $333
const REQUIRE_CONFIRMATION = true; // buy only after a bar closes above the previous bar's high
const TP1_BPS = 120; // sell half at +1.2% over the cycle's average buy price
const TP2_BPS = 450; // sell the rest at +4.5%
const TRAIL_BPS = 80; // after TP1, sell the rest on a 0.8% pullback from the highest close
const HARD_STOP_BPS = 650; // liquidate at -6.5% below the frozen anchor
const BRAKE_BPS = 1500; // halt everything on a 15% equity drawdown from the peak
const MAX_CYCLES = 2;
const FALLBACK_BAR = 1200; // no trade by here: buy full size once
const LAST_BAR = 1439; // orders on the final bar are rejected, so never send any
const MAX_SLIPPAGE_BPS = 200; // fills more than 2% from the decision close are refused
const MIN_NOTIONAL = 1_000_000n; // 1 USDC, in quote units
const BPS = 10_000n;

interface PendingOrder {
  kind: 'buy' | 'tp1' | 'exit';
  tiers: number[];
}

interface BotState {
  closes: bigint[];
  highs: bigint[];
  frozenAnchor: bigint | null;
  armed: boolean[];
  ordered: boolean[];
  filled: boolean[];
  cycleActive: boolean;
  cyclesStarted: number;
  everTraded: boolean;
  tp1Sent: boolean;
  tp1Filled: boolean;
  highestSinceTp1: bigint | null;
  peakEquity: bigint;
  halted: boolean;
  fallbackSent: boolean;
  pending: Map<string, PendingOrder>;
  orderCounter: number;
}

const state: BotState = {
  closes: [],
  highs: [],
  frozenAnchor: null,
  armed: [false, false, false],
  ordered: [false, false, false],
  filled: [false, false, false],
  cycleActive: false,
  cyclesStarted: 0,
  everTraded: false,
  tp1Sent: false,
  tp1Filled: false,
  highestSinceTp1: null,
  peakEquity: 0n,
  halted: false,
  fallbackSent: false,
  pending: new Map(),
  orderCounter: 0,
};

function nextId(prefix: string): string {
  state.orderCounter += 1;
  return `${prefix}${state.orderCounter}`;
}

function trailingHigh(closes: bigint[], n: number): bigint {
  let hi = 0n;
  const start = Math.max(0, closes.length - n);
  for (let i = start; i < closes.length; i++) {
    if (closes[i] > hi) hi = closes[i];
  }
  return hi;
}

// The position's average buy price, in the symbol's price units, from its
// fee-inclusive cost basis: price = cost * 10^(qty+price-quote scales) / qty.
function averageBuyPrice(st: BarsState, cost: bigint, qty: bigint): bigint {
  const sym = st.symbols.get(SYMBOL);
  const exp = (sym?.qty_scale ?? 8) + (sym?.price_scale ?? 5) - st.hello.capital.quote_scale;
  return (cost * 10n ** BigInt(exp)) / qty;
}

function sellAll(qty: bigint): OrderInput {
  const id = nextId('s');
  state.pending.set(id, { kind: 'exit', tiers: [] });
  return { side: 'sell', client_id: id, symbol: SYMBOL, qty, max_slippage_bps: MAX_SLIPPAGE_BPS };
}

function decide(st: BarsState, batch: Batch): OrderInput[] {
  // 1. Resolve the orders sent on the previous batch from this batch's fills.
  for (const fill of batch.fills) {
    const p = state.pending.get(fill.client_id);
    if (!p) continue;
    state.pending.delete(fill.client_id);
    if (fill.status === 'filled') {
      state.everTraded = true;
      if (p.kind === 'buy') {
        for (const t of p.tiers) {
          state.ordered[t] = false;
          state.filled[t] = true;
        }
        if (!state.cycleActive) {
          state.cycleActive = true;
          state.cyclesStarted += 1;
        }
      } else if (p.kind === 'tp1') {
        state.tp1Filled = true;
      }
    } else {
      // Rejected: undo the optimistic bookkeeping so the signal can retry.
      if (p.kind === 'buy') {
        for (const t of p.tiers) {
          state.ordered[t] = false;
          state.armed[t] = true;
        }
      } else if (p.kind === 'tp1') {
        state.tp1Sent = false;
      }
    }
  }

  // 2. Equity brake: a 15% drawdown from the peak ends trading for the run.
  if (st.equity > state.peakEquity) state.peakEquity = st.equity;
  if (!state.halted && st.equity * BPS <= state.peakEquity * (BPS - BigInt(BRAKE_BPS))) {
    state.halted = true;
    const held = st.positions.get(SYMBOL);
    if (held && held.qty > 0n) return [sellAll(held.qty)];
    return [];
  }
  if (state.halted) return [];

  // 3. This batch's bar (a minute the recorder missed carries no bar).
  const bar = batch.bars.find((b) => b.symbol === SYMBOL);
  if (!bar) return [];
  const close = BigInt(bar.c);
  const prevHigh = state.highs.length > 0 ? state.highs[state.highs.length - 1] : null;
  state.closes.push(close);
  state.highs.push(BigInt(bar.h));

  if (st.warmingUp) return [];
  const barIndex = st.seq - st.warmupBars;
  if (barIndex >= LAST_BAR) return [];

  const pos = st.positions.get(SYMBOL);
  const qty = pos ? pos.qty : 0n;

  // 4. A cycle ends the moment the account is flat again.
  if (state.cycleActive && qty === 0n) {
    state.cycleActive = false;
    state.frozenAnchor = null;
    state.armed = [false, false, false];
    state.ordered = [false, false, false];
    state.filled = [false, false, false];
    state.tp1Sent = false;
    state.tp1Filled = false;
    state.highestSinceTp1 = null;
  }

  // 5. Manage an open position: exits first, buys only before the first take-profit.
  if (qty > 0n && pos) {
    const avgBuy = averageBuyPrice(st, pos.cost, qty);
    // Hard stop: the close fell 6.5% below the frozen anchor.
    if (state.frozenAnchor !== null && close * BPS <= state.frozenAnchor * (BPS - BigInt(HARD_STOP_BPS))) {
      return [sellAll(qty)];
    }
    if (!state.tp1Filled) {
      if (!state.tp1Sent && close * BPS >= avgBuy * (BPS + BigInt(TP1_BPS))) {
        state.tp1Sent = true;
        const id = nextId('s');
        state.pending.set(id, { kind: 'tp1', tiers: [] });
        return [{ side: 'sell', client_id: id, symbol: SYMBOL, qty: qty / 2n, max_slippage_bps: MAX_SLIPPAGE_BPS }];
      }
    } else {
      // After TP1: trail the rest 0.8% below the highest close since then.
      if (state.highestSinceTp1 === null || close > state.highestSinceTp1) state.highestSinceTp1 = close;
      if (close * BPS >= avgBuy * (BPS + BigInt(TP2_BPS))) return [sellAll(qty)];
      if (close * BPS <= state.highestSinceTp1 * (BPS - BigInt(TRAIL_BPS))) return [sellAll(qty)];
    }
    if (state.tp1Sent) return [];
  }

  // 6. Dip tiers: arm on touch, buy on bounce confirmation.
  if (state.closes.length >= LOOKBACK_BARS) {
    const trailing = trailingHigh(state.closes, LOOKBACK_BARS);
    // A full recovery to the anchor with nothing bought yet unfreezes it.
    if (state.frozenAnchor !== null && !state.cycleActive && !state.ordered.some(Boolean) && close >= state.frozenAnchor) {
      state.frozenAnchor = null;
      state.armed = [false, false, false];
    }
    const anchor = state.frozenAnchor ?? trailing;
    let touched = false;
    for (let i = 0; i < TIER_DIP_BPS.length; i++) {
      if (!state.armed[i] && !state.ordered[i] && !state.filled[i] &&
          close * BPS <= anchor * (BPS - BigInt(TIER_DIP_BPS[i]))) {
        state.armed[i] = true;
        touched = true;
      }
    }
    if (touched && state.frozenAnchor === null) state.frozenAnchor = trailing;
    const confirmed = !REQUIRE_CONFIRMATION || (prevHigh !== null && close > prevHigh);
    const ready = state.armed.map((a, i) => (a && !state.ordered[i] ? i : -1)).filter((i) => i >= 0);
    const mayStartCycle = state.cycleActive || state.cyclesStarted < MAX_CYCLES;
    if (confirmed && ready.length > 0 && mayStartCycle) {
      let notional = 0n;
      for (const i of ready) notional += TIER_NOTIONAL[i];
      if (notional > st.cash) notional = st.cash;
      if (notional >= MIN_NOTIONAL) {
        const id = nextId('b');
        state.pending.set(id, { kind: 'buy', tiers: ready });
        for (const i of ready) {
          state.armed[i] = false;
          state.ordered[i] = true;
        }
        return [{ side: 'buy', client_id: id, symbol: SYMBOL, notional_quote_units: notional, max_slippage_bps: MAX_SLIPPAGE_BPS }];
      }
    }
  }

  // 7. Fallback: no trade by bar 1200, buy full size once.
  if (barIndex >= FALLBACK_BAR && !state.fallbackSent && !state.everTraded && state.cyclesStarted === 0 &&
      state.closes.length >= LOOKBACK_BARS) {
    const buyPending = [...state.pending.values()].some((p) => p.kind === 'buy');
    if (!buyPending && st.cash >= MIN_NOTIONAL) {
      state.fallbackSent = true;
      if (state.frozenAnchor === null) state.frozenAnchor = trailingHigh(state.closes, LOOKBACK_BARS);
      const id = nextId('b');
      state.pending.set(id, { kind: 'buy', tiers: [] });
      return [{ side: 'buy', client_id: id, symbol: SYMBOL, notional_quote_units: st.cash, max_slippage_bps: MAX_SLIPPAGE_BPS }];
    }
  }

  return [];
}

runBars({
  onBatch(st, batch) {
    return decide(st, batch);
  },
}).catch((err) => {
  console.error(err);
  process.exitCode = 1;
});
