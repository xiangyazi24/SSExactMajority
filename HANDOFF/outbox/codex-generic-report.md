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

## 2026-06-04 codex generic-trank swap-live window checkpoint

Ported the live-swap window over
`PEMProtocol n trank Rmax Emax Dmax hn0`:

- `generic_swap_live_to_cons_or_crs_or_break`

The proof threads the generic timer-bound invariant, uses
`generic_decision_window` for the median-not-yet-correct branch, and uses
`generic_timer_drain_window` for the MAC branch.

Verification:

- `lake build SSExactMajority.UpperBound.Time.GenericTrank`

Result: passed. No semantic `trank = Rmax` dependency encountered in this
layer.

## 2026-06-04 codex generic-trank MAC-live checkpoint

Ported the MAC-live composition layer over
`PEMProtocol n trank Rmax Emax Dmax hn0`:

- `generic_MAClive_to_consensus_or_crs`
- `generic_MAClive_to_consensus_or_crs_window`

This composes the productive drain endpoint with
`generic_PEM_expected_reset_trigger_v2` at the timer-zero live endpoint.

Verification:

- `lake build SSExactMajority.UpperBound.Time.GenericTrank`

Result: passed. No semantic `trank = Rmax` dependency encountered in this
layer.

## 2026-06-04 codex generic-trank reset-trigger checkpoint

Ported the timer-zero reset trigger over
`PEMProtocol n trank Rmax Emax Dmax hn0`:

- `generic_PEM_expected_reset_trigger_v2`

The invariant step uses the generic rank/timer/median-answer helpers.  The
non-upper wrong-answer branch transfers the coupled CRS one-step lemma through
`InSrank` step equality; the upper-median-only branch uses the existing
`trank`-parameterized median-pair transition lemmas.

Verification:

- `lake build SSExactMajority.UpperBound.Time.GenericTrank`

Result: passed. No semantic `trank = Rmax` dependency encountered in this
layer.

## 2026-06-04 codex generic-trank productive timer-drain checkpoint

Ported the productive drain endpoint over
`PEMProtocol n trank Rmax Emax Dmax hn0`:

- `generic_step_median_answer_of_InSswap_both`
- `generic_timer_drain_to_zero_productive`

The proof follows the coupled deterministic-descent structure.  The
`timer = 1` branch is handled with existing local transition lemmas for the
wrong-max reset case and the clean even/odd timer-drain cases, avoiding a
fresh generic unfold of `transitionPEM`.

Verification:

- `lake build SSExactMajority.UpperBound.Time.GenericTrank`

Result: passed. No semantic `trank = Rmax` dependency encountered in this
layer.

## 2026-06-04 codex generic-trank timer-drain window checkpoint

Ported the timer-drain expected-time/window layer over
`PEMProtocol n trank Rmax Emax Dmax hn0`:

- `generic_timer_ge_two_descent_step`
- `generic_PEM_expected_timer_drain_poly`
- `generic_timer_drain_window`

The expected-time bound is transferred from the coupled protocol by the
non-goal step-equality bridge, since non-goal states for this window remain in
`InSswap` with median timer at least 1.

Verification:

- `lake build SSExactMajority.UpperBound.Time.GenericTrank`

Result: passed. No semantic `trank = Rmax` dependency encountered in this
layer.

## 2026-06-04 codex generic-trank decision-timing helper/window checkpoint

Ported the decision-timing support stack over
`PEMProtocol n trank Rmax Emax Dmax hn0`:

- `generic_live_exit_ProbHitWithin_le_bad`
- internal stopped invariant for `hitTwoFlagDist`
- subtraction wrapper
  `generic_decision_before_timer_zero_of_exit_le_quarter`
- `generic_decision_before_timer_zero`

The proof reuses `generic_decision_window` for the median-not-yet-correct
branch and handles the already-correct branch by the time-0 productive target.
The exit-to-bad comparison uses the generic stopped invariant and the generic
step helper preserving `InSswap` under a post-step `InSrank`.

Verification:

- `lake build SSExactMajority.UpperBound.Time.GenericTrank`

Result: passed. The helper layer requested in step 1 is now present in
`GenericTrank.lean`. No semantic `trank = Rmax` dependency encountered.

## 2026-06-04 codex generic-trank expected-transfer checkpoint

Added tail-probability and expected-time transfer from `PEMProtocol n trank Rmax`
to `PEMProtocolCoupled n Rmax` under a non-goal step-equality hypothesis:

- `generic_probNotHitBy_succ_eq_tsum_step_of_not_goal`
- `generic_probNotHitBy_eq_of_step_eq_until`
- `generic_expectedHittingTime_eq_of_step_eq_until`

Also imported `PolynomialBound` so the next window layer can cite
`maxMedianTimer`, `timer_ge_two_descent_step`, and
`PEM_expected_timer_drain_poly`.

Verification:

- `lake build SSExactMajority.UpperBound.Time.GenericTrank`

Result: passed. The new import forced `PolynomialBound.lean` to rebuild
(about 279 seconds), then `GenericTrank.lean` built cleanly.

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

## 2026-06-04 codex generic-trank HOLD checkpoint

Stopped per Xiang update: the audited time keystone route is vacuous via the
false `resetInv` hypothesis and has the `n^3` reset-window issue. I removed
the uncommitted keystone/`trank=1` instantiation draft and left the reusable
generic timer/window ports intact.

Current reusable window stack is committed through:

- `a1cdbb1` `[Xiang-proxy] Generic-trank swap live window`

No keystone instantiation is committed from this handoff.

Done.
