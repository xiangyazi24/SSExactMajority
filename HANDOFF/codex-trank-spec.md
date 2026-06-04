# Codex task (uisai1): trank=O(1) tightening — O(n log n) parallel → O(n) expected (the headline)

The optimal-bound STRUCTURE is done + build-verified (b927830): PEM_expectedParallelTime_optimal,
[12]-only hyps, 0 sorry/axiom, hRank12 eliminated. Current bound E[parallel] ≤ OW_globalWindow·16/n
= O(Rmax·n) = O(n log n) with Rmax=60log n. The paper's HEADLINE is O(n) EXPECTED. Close the log gap.

## Two sources of the loose log factor
1. h12ranking is stated `≤ Rmax·n²`. [12]'s actual Optimal-Silent-SSR ranking time (Theorem 4.3) is
   O(n) PARALLEL = O(n²) seq, INDEPENDENT of Rmax. Since h12ranking is a CITED [12] hypothesis, restate
   it with the TRUE [12] bound (≤ c·n² for an explicit constant c, NOT Rmax·n²). Propagate the tighter
   bound through OW_globalWindow / OW_rankBound.
2. The consensus/timer windows use 7(Rmax+4) (median timer). The protocol's timer is 7(trank+4); the
   current PEMProtocolCoupled instantiates trank=Rmax (Time.lean:39-55 notes this is NOT the paper's
   constant-trank regime). For O(n) parallel the timer must be 7(trank+4) with trank=O(1).

## SCOPE FIRST (investigate, report precisely)
- Is the timer-bounded machinery (IsTimerBoundedConfig, the swap/decision/drain windows, decision_before
  _timer_zero, timer_drain_to_zero_productive) UNIFORM in the timer bound, i.e. can it take 7(trank+4)
  with trank=O(1) instead of 7(Rmax+4)? Or is trank=Rmax baked in (requiring a structural re-param of
  PEMProtocolCoupled / re-proving the windows)?
- Determine the MINIMAL change: ideally (a) restate h12ranking ≤ c·n² [easy, it is a cited hyp], and
  (b) generalize the timer bound parameter from 7(Rmax+4) to a separate T_timer=O(1), so OW_globalWindow
  becomes O(n²) seq = O(n) parallel.

## ATTEMPT
Restate h12ranking ≤ c·n² and re-derive the final bound; if the timer re-param is uniform, do it; if it
requires re-proving windows for trank=O(1), report the exact list of lemmas needing it (do NOT break the
build-verified b927830 state — work additively or report the structural scope).

## HARD RULES (automode, no effort cap)
- NO sorry/axiom/native_decide. Verify via `lake build` (olean), NOT just lake env lean (env≠build bit me).
  Keep the [12]-only hypothesis discipline. Report precisely (tightened to O(n) / structural scope needed).
  Append to HANDOFF/outbox/codex-trank-report.md.
