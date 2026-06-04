## 2026-06-04 codex generic-trank foundation

Added `SSExactMajority/UpperBound/Time/GenericTrank.lean`.

Proved:

- `generic_timer_preservation`: one-step preservation of `IsTimerBoundedConfig K`
  for `PEMProtocol n trank Rmax Emax Dmax hn`, assuming `7 * (trank + 4) <= K`.
- `generic_decision_window`: the `decision_window` Markov form over
  `PEMProtocol n trank Rmax Emax Dmax hn`.
- Supporting generic one-step / expected-time lemmas:
  `generic_PEM_even_median_wrong_to_MedianAnswerCorrect_prob_lower_bound`,
  `generic_PEM_odd_median_wrong_to_MedianAnswerCorrect_prob_lower_bound`,
  `generic_PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound`,
  `generic_PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le`.

Verification:

- `lake env lean SSExactMajority/UpperBound/Time/GenericTrank.lean`
- `lake build SSExactMajority.UpperBound.Time.GenericTrank`

Both passed. No `sorry`, `axiom`, `admit`, or `native_decide` in the new file.

Timer-cap/trank audit:

- `generic_decision_window` is cleanly timer-cap-uniform: it does not need an
  upper cap `K` at all, only `MedianTimerAtLeast 1`. Its proof uses generic
  `trank` throughout and did not hit any semantic `trank = Rmax` dependency.
- The next short-window lemma,
  `PEM_srank_or_timer_failure_prob_le_quarter_short35`, is still coupled in
  `Time.lean` and uses a private `srankMedianMaxEvent`/hit-count support stack.
  I did not find a semantic need for `trank = Rmax` there; the current blocker
  is that the support lemmas are stated with `PEMProtocolCoupled`.
- `decision_before_timer_zero` inherits that coupled dependency and also uses
  private coupled lemmas from `DecisionTiming.lean`
  (`live_exit_ProbHitWithin_le_bad` and its support invariant).
- The timer-drain/productive windows (`timer_ge_two_descent_step`,
  `PEM_expected_timer_drain_poly`, `timer_drain_to_zero_productive`,
  `MAClive_to_consensus_or_crs`, `swap_live_to_cons_or_crs_or_break`) are not
  ported in this pass. Their current proofs call coupled step helpers such as
  `step_rank_preserved_of_InSswap`, `step_timer_le_of_InSswap`, and
  `crs_of_InSswap_break_with_MedC`. The `n <= Rmax` assumptions are genuine
  reset-count assumptions, but I did not identify a proof step that
  semantically requires `trank = Rmax`; the remaining work is generic copies of
  those coupled helper layers.

## 2026-06-04 codex generic-trank coupled-transfer checkpoint

Added the coupled-transfer bridge inside `GenericTrank.lean`:

- `generic_step_eq_coupled_of_InSrank`: for any `PEMProtocol n trank Rmax`,
  one step agrees with `PEMProtocolCoupled n Rmax` whenever the pre-state is
  `InSrank`.
- `generic_ProbHitWithin_eq_of_step_eq_until`: finite-window hit probability
  equality for goals whose non-goal region gives the step-equality hypothesis.

Ported:

- `generic_PEM_srank_or_timer_failure_prob_le_quarter_short35` over
  `PEMProtocol n trank Rmax Emax Dmax hn0`, retaining the genuine reset-count
  assumptions `n <= Rmax`, `n <= Emax`, `n <= Dmax`.

Verification:

- `lake build SSExactMajority.UpperBound.Time.GenericTrank`

Result: passed. No semantic `trank = Rmax` dependency encountered in this
layer.

## 2026-06-04 codex generic-trank step-helper checkpoint

Added generic wrappers over the coupled step helpers:

- `generic_step_rank_preserved_of_InSswap`
- `generic_step_timer_le_of_InSswap`
- `generic_crs_of_InSswap_break_with_MedC`
- internal `generic_step_InSswap_of_InSswap_of_post_InSrank`

All use the `InSrank` step-equality bridge to transfer the existing coupled
helper result back to `PEMProtocol n trank Rmax Emax Dmax hn0`.

Verification:

- `lake build SSExactMajority.UpperBound.Time.GenericTrank`

Result: passed. No semantic `trank = Rmax` dependency encountered in this
layer.
