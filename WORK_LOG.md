# SSExactMajority Macro-Step Work Log

## 2026-05-08 Session

### A1 — TimerDescent.lean
- ✓ `medianAgent`, `medianTimer`, `medianAgent_rank`
- ✓ `medianTimer_decreases_at_misorder_median_v_max_odd` (the main single-step
  descent for the misorder swap-fires + odd-n + timer ≥ 2 case)
- TODO: extend to no-swap case (when inputs don't form a misorder)
- TODO: even-n companion

### A2 — reach_zero_timer_macro
- BLOCKED on tracking position-of-median across steps.
- After step 1: position μ has rank n-1, position v has rank ceilHalf n - 1.
- For step 2 of timer descent, scheduler picks (v, μ) — the new (median, max).
- A clean PotentialReach instantiation requires the invariant to be
  parameterized on the current median's POSITION, which medianTimer abstracts
  away.
- Workaround idea: define potential `medianTimer` and an explicit recursive
  scheduler that tracks position. Or: prove "from medianTimer = T ≥ 2,
  exists 1-step trajectory to medianTimer = T - 1" as a single lemma, then
  iterate.

### B1 onwards — pending A2

## E1 — `hSwapExists` 组合论证 (BLOCKED)

**Issue**: the four-way disjunction in `hSwapExists` is not always satisfiable structurally.

Specifically, for any misorder pair `(u, v)`:
- If u, v both non-median → case (i) ✓
- If u at median → cases (ii)/(iii)/(iv) cover (depending on parity, v position, timer)
- If v at median (u below median) → **NO disjunct covers this**

The "v at median" misorder pair is structurally common: u at lower rank with input
.B, v at median with input .A. Swap fires, post-swap state has median (= old v's
state) at position u, agents proceed correctly. But the disjunction's labels assume
"u at median".

**Counterexample to "always satisfiable"**: even in the symmetric case, when timer
= 0 at median, neither (ii) nor (iii) apply. Reset cycle handles it, but that's a
macro-step.

**Path forward**: extend `hSwapExists` with a fifth disjunct for the v-at-median
case + a corresponding swap-step lemma `swap_step_decreases_at_misorder_v_median_*`.
Then prove existence of one of (i)-(v) under reasonable hypotheses (e.g.,
nA, nB ≥ 1, timer ≥ 1 at median).

This is doable but requires writing parallel lemmas to RankPreservation.lean's
existing five swap-step lemmas. Deferred.

## E3 — `BurmanMacroDecision` 消除 (DEFERRED)

Requires building macro-step trajectory analysis tools (multi-step timer descent →
reset cycle → epidemic → Burman re-settle). Deferred in favor of treating it as
the bundled external assumption in MasterModuloBurman.lean.

## F (Burman 2021) — out of session scope

A separate paper's worth of formalization. Deferred.

## E1 even-n existence completeness — gap

For even-n misorder pair with u at lower median (rank n/2 - 1) and v at
rank > n/2 (i.e., NOT at upper median): not covered by the 6-way
disjunction.  The misorder requires u.rank < v.rank; if u at n/2 - 1
and v.rank ≥ n/2 + 1, neither (iv) (which needs v at n/2) nor any other
disjunct applies.

This case requires a 7th sub-case lemma "even n, u at lower median,
v not at upper median, v not at max, u.timer ≥ 1" with result similar to
even n no-decision propagation.  Deferred.

## Status snapshot (end of round 4)

- Build: 901 jobs, 0 sorry, 0 axiom.
- Single-step swap-step coverage: 6-way (most permissive), parity-combined.
- Single-step decision-step coverage: median-wrong for both parities.
- Theorem 4 modulo Burman: D1, D2, D3 all proved.
- Median-wrong witnesses: discharged for n ≥ 3 odd and n ≥ 4 even strict majority.
- 5-way swap-step existence: proved for odd n with median.timer ≥ 2.

Remaining structural gaps that fit in this loop:
- Even-n 5-way (or 6-way) swap-step existence under timer hypotheses.
- 7th sub-case: even-n misorder with u at lower median + v above upper.

Out-of-loop:
- E3 BurmanMacroDecision (multi-step trajectory).
- F Burman 2021 (separate paper).

## 2026-05-09 Session — Timer descent infrastructure

### New file: Convergence/TimerDescentNoSwap.lean

Proves three theorems for the no-swap case at InSswap (odd n, timer ≥ 2):
- `step_at_median_max_no_swap_odd` — component-level step description
- `step_at_median_max_no_swap_odd_preserves_InSswap` — InSswap preserved
- `timer_decreases_at_median_max_no_swap_odd` — timer strictly decreases

Key insight: at InSswap, scheduling (median, max) does NOT trigger the
swap (because A-agents have lower ranks → median has input A, swap needs
input B at the lower rank). Only decision + propagation fire. Timer
decrements by 1 each time median meets max.

One sorry remains: the explicit transitionPEM equation (being filled by
subagent).

### BurmanMacroDecision discharge plan

The macro-step when median is correct but some non-median is wrong:

1. **Timer descent** (timer T → 1): iterate `timer_decreases_at_median_max_no_swap_odd`
   via induction. Each step: schedule (median, max), preserves InSswap,
   timer decreases. Requires timer ≥ 2 per step.

2. **Timer = 1 → 0**: two sub-cases:
   a. Max has wrong answer → step at (median, max) → timer = 0, reset
      fires (answers differ). Both enter Resetting. NEW LEMMA NEEDED.
   b. Max has correct answer → timer = 0, no reset. InSswap preserved.
      Then schedule (median, wrong_agent) → timer = 0, answers differ →
      reset fires. NEW LEMMA NEEDED (timer = 0, non-max partner).

3. **After reset**: epidemic propagation — correct answer spreads via the
   epidemic protocol. Median's answer was set by the decision step, so
   it's correct. All Resetting agents eventually get the correct answer.

4. **Re-ranking**: Burman's ranking protocol re-establishes unique ranks.
   This is `h_burman_ranking` — external assumption.

5. **Re-swapping**: from InSrank, the swap phase brings to InSswap.
   This is `hSwapPhase` — already proved via the swap-step infrastructure.

6. **Net effect**: the agent that triggered the reset now has the correct
   answer (it was set during the epidemic). So wrongAnswerCount decreased.

### Next concrete steps

- Fill the transitionPEM sorry (subagent in progress)
- Timer = 1 → 0 step lemma (reset fires when answers differ)
- Timer = 0 non-max partner step lemma (reset fires at any wrong agent)
- Compose into a multi-step trajectory (explicit scheduler construction)
- Wire into `BurmanMacroDecision` (modulo `h_burman_ranking`)
