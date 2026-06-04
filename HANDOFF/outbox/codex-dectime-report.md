## 2026-06-04 — decision timing isolation

New file:
- `SSExactMajority/UpperBound/Time/DecisionTiming.lean`

Proved:
- `decisionWindow n := 2 * n * (n - 1)`.
- `kanayaDecisionWindow n := 4 * n * n`.
- `DecisionProductiveTarget C := (InSswap C ∧ MedianAnswerCorrect C ∧ MedianTimerAtLeast 1 C) ∨ IsConsensusConfig C ∨ CorrectResetSeed C`.
- `decision_before_timer_zero`: in the short `decisionWindow`, if the live-region exit probability is `≤ 1/4`, then
  `P(DecisionProductiveTarget) ≥ 1/4`.
- `decision_before_timer_zero_kanaya28`: in the `4*n*n` Kanaya-style window, from `MedianTimerAtLeast 28`, if live-region exit probability is `≤ 1/2`, then
  `P(DecisionProductiveTarget) ≥ 1/8`.  The already-MAC case is handled by the time-0 hit; the non-MAC case reuses the existing Phase-3 live-decision subtraction wrapper.

Exact obstruction:
- I did not find an unconditional theorem proving the required live-region exit bound from `InSswap + MedianTimerAtLeast 1`.
- The current library already proves `decision ∨ live-exit` geometrically (`PEM_phase3_live_or_exit_window` / `PEM_Tswap_to_MedianAnswerCorrect_or_exit_prob_window`) and has subtraction wrappers, but those wrappers require an explicit exit upper bound.
- There are exit-count bounds from `InSrank + MedianTimerAtLeast 12*n` / `35` for `¬InSrank ∨ ¬MedianTimerAtLeast 1`, but no theorem currently converts the `InSswap` decision-timing timeout branch into the needed `¬(InSswap ∧ MedianTimerAtLeast 1)` bound without an external hypothesis.

Verification:
- `lake env lean SSExactMajority/UpperBound/Time/DecisionTiming.lean` passed.
- No `sorry`, `axiom`, or `native_decide` added.

## 2026-06-04 — update: stopped invariant closes the timer-35 form

Additional proof in `SSExactMajority/UpperBound/Time/DecisionTiming.lean`:
- Added `step_InSswap_of_InSswap_of_post_InSrank`: from a pre-step `InSswap`
  state, any post-step `InSrank` state is still `InSswap`, using rank/input
  preservation.
- Added a stopped support invariant for `hitTwoFlagDist`: while the bad flag
  `¬ InSrank ∨ ¬ MedianTimerAtLeast 1` is false, the chain remains in
  `InSswap ∧ MedianTimerAtLeast 1`, and the live-exit flag is false.
- Derived `live_exit_ProbHitWithin_le_bad`, converting the live-region exit
  event into the existing bad event.
- Renamed the conditional wrapper to
  `decision_before_timer_zero_of_exit_le_quarter`.
- Proved `decision_before_timer_zero`: assuming `4 ≤ n`, `n ≤ Rmax`,
  `n ≤ Emax`, `n ≤ Dmax`, `InSswap C`, and `MedianTimerAtLeast 35 C`,
  the productive target is hit within `decisionWindow n = 2 * n * (n - 1)`
  with probability at least `1/4`.

Remaining limitation:
- The fully `MedianTimerAtLeast 1` timeout theorem is still not closed. The
  unconditional theorem above uses the existing timer-35 event-count tail bound.
  `decision_before_timer_zero_kanaya28` remains available as a conditional
  wrapper with an explicit `exit ≤ 1/2` hypothesis.

Verification:
- `lake env lean SSExactMajority/UpperBound/Time/DecisionTiming.lean` passed
  with no output.
- No `sorry`, `axiom`, or `native_decide` added.
