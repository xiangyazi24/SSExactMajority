# Codex -> Claude/Zinan: time-bound status sync

Sender: Codex
Receiver: Zinan / Claude Code
Topic: SSExactMajority `UpperBound/Time.lean` expected-time endgame status

## Completed result

I removed the independent arithmetic `sorry` at `Time.lean`'s swap square-sum bound:

- Added `import Mathlib.Analysis.PSeries`.
- Added private helper `real_sum_range_inv_sq_le_two`.
- Proved `ennreal_sum_inv_sq_le_two_mul_sq` using `sum_Ioo_inv_sq_le` plus ENNReal `toReal`.

Verification:

```bash
/Users/huangx/.openclaw/workspace/scripts/remote-build.sh SSExactMajority --file SSExactMajority/UpperBound/Time.lean
```

Result: build OK. Remaining warnings are existing lints plus exactly 3 `sorry` declarations.

Remaining `sorry`s in `SSExactMajority/UpperBound/Time.lean`:

- `PEM_ranking_expected_hitting_time`
- `PEM_consensus_expected_hitting_time`
- `PEM_swap_ProbHitWithin_InSswap`

## Current blocker analysis

For `PEM_consensus_expected_hitting_time`, the tempting first leg
`PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le` does not target pure
`InSswap ∧ MedianAnswerCorrect`. It targets:

```lean
fun D =>
  (InSswap D ∧ MedianAnswerCorrect D) ∨
    ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
```

So composing it with `expectedHittingTime_add_le` requires a uniform expected
bound from the exit branch too. That branch is too broad unless we prove a
reachable-exit refinement or a quantitative reset/propagation theorem.

Existing useful local facts:

- one-step/live decision expectation:
  `PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le`
- reset seed creation:
  `PEM_odd_median_max_timer_one_reset_seed_prob_lower_bound`
  and even analogue
- reset epidemic local descent:
  `PEM_correctResetSeed_nonResetting_positive_descent_prob_lower_bound`
  and richer growth lemmas
- qualitative deterministic reachability:
  `PEM_consensus_reachable`

Missing quantitative bridge:

```lean
CorrectResetSeed C ->
  expectedHittingTime P hn C IsConsensusConfig <= O(Rmax * n * n)
```

or a narrower live decision/exit theorem that avoids quantifying over all
`¬ (InSswap ∧ MedianTimerAtLeast 1)` states.

The deterministic reset sweep lemmas (`phase2_propagate_reset`,
`all_resetting_from_seed_answer_aux`, etc.) produce existence of a list/path,
but do not currently package a list-length/window/probability bound usable by
`expectedHittingTime`.

## Lock status

No handoff lock held.

