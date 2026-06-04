# codex-renewal2 report

## Result

Proved `awakening_to_goal_or_exit_expected_le` in
`SSExactMajority/UpperBound/Time/EntryBound.lean`.

The proof uses `Probability.expectedHittingTime_le_of_variable_descent_until_goal`
with:

- `Goal := FreshRankingStart ∨ HeapPrefix entry ∨ IsConsensusConfig ∨ ¬ IsAwakeningConfig`.
- `Inv := IsAwakeningConfig`.
- `φ D := (awakeningResettingFollowers D).card`.
- constant descent rate `(n * (n - 1))⁻¹`.

## Main ingredients

- `hInvStep` is the disruption-inclusive case split: if the next state remains
  awakening, use `Inv`; otherwise the `¬ IsAwakeningConfig` disjunct is already
  a goal.
- `hZeroGoal` uses
  `freshRankingStart_iff_awakeningResettingFollowers_card_zero_of_awakening`.
- `hp` applies `awakening_step_descent_prob` for the smaller
  `FreshRankingStart ∨ (IsAwakeningConfig ∧ smaller card)` target and lifts it
  with `Probability.ProbHitWithin_mono_goal`.
- `hNonincrease` is discharged by a stronger no-card-rise lemma:
  `awakeningResettingFollowers_card_step_le_of_awakening`.  Its proof shows any
  resetting follower after an awakening step was already a resetting follower
  before the step, using endpoint transition case analysis around
  `transitionPEM`, recruitment, unsettled partners, and phase-4 reset leaders.

## Verification

Command run:

```bash
lake env lean SSExactMajority/UpperBound/Time/EntryBound.lean
```

Result: success, no warnings.

Also checked:

```bash
rg -n "sorry|axiom|native_decide" SSExactMajority/UpperBound/Time/EntryBound.lean
```

Result: no matches.
