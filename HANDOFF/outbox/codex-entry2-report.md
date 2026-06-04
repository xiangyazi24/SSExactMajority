## codex-entry2 report

### STEP A: awakening -> FreshRankingStart E[T]

Status: blocked, not closed.

The already-proved local progress piece is present in
`SSExactMajority/UpperBound/Time/EntryBound.lean`:

- `freshRankingStart_iff_awakeningResettingFollowers_card_zero_of_awakening`
- `awakening_step_descent_witness`
- `awakening_step_descent_prob`

I instantiated
`Probability.expectedHittingTime_le_of_variable_descent_until_goal` with

- `Goal := FreshRankingStart`
- `Inv := IsAwakeningConfig`
- `phi D := (awakeningResettingFollowers D).card`
- `pRate _ := 1 / (n * (n - 1))`

The `hp` premise is exactly discharged by `awakening_step_descent_prob`, and
the zero-level goal premise is exactly
`freshRankingStart_iff_awakeningResettingFollowers_card_zero_of_awakening`.
The obstruction is the required all-pair invariant premise:

```lean
forall C, IsAwakeningConfig C -> not (FreshRankingStart C) ->
  forall i j,
    IsAwakeningConfig (C.step P i j) \/
    FreshRankingStart (C.step P i j)
```

This premise is false for the protocol.  After one successful
`settled root -> dormant follower` awakening-descent step, if another dormant
follower remains, the state is still `IsAwakeningConfig` and not
`FreshRankingStart`, but it now contains an Unsettled follower.  Scheduling the
ordered pair `(unsettled follower, root)` triggers the binary-tree recruit
step, not the phase-3bc sweep:

- `rankDeltaOSSR_recruit_ba`
  (`SSExactMajority/Convergence/BurmanProof.lean:10354`)
- `transitionPEM_recruit_ba_settled_rank_children`
  (`SSExactMajority/Convergence/BurmanProof.lean:10693`)

For the awakening root, `rank = 0`, `children = 0`, and `4 <= n` gives
`2 * 0 + 0 + 1 < n`; the recruit trace sets the root-side output
`children = 1`.  That violates `IsAwakeningConfig`, whose leader clause
requires `children = 0`, and it is not `FreshRankingStart`.

So the requested theorem cannot be obtained from the variable-descent lemma
with `Inv = IsAwakeningConfig` and `Goal = FreshRankingStart`.  The local
good-pair probability is correct, but the phase is not closed under arbitrary
scheduler pairs before the goal.

### STEP B: dormant -> awakening

Status: attempted, blocked at the analogous all-pair closure premise.

The qualitative proof `phase3a_to_awakening` uses a chosen leader/follower pair
and strong induction on the leader delaytimer.  For a stochastic variable
descent, the direct invariant `IsDormantConfig` is not closed under arbitrary
pairs before reaching `IsAwakeningConfig`.

Concrete obstruction: in a dormant configuration with two follower agents
`u != v`, both `leader = F`, both `resetcount = 0`, and both delaytimers
`<= 1`, scheduling `(u, v)` makes both followers Unsettled:

- `transitionPEM_both_dormant_followers_low_dt_unsettle`
  (`SSExactMajority/Convergence/BurmanProof.lean:8325`)

The unique leader is unchanged and still `Resetting`, so the resulting state is
not `IsDormantConfig` (not all agents are Resetting) and not
`IsAwakeningConfig` (the unique leader is not Settled).  Thus the needed
until-goal closure premise for a dormant-to-awakening variable descent fails.

The existing `followerDormantMeasure` lemmas prove good local decreases for
selected follower/dormant interactions, but by themselves they do not provide
the arbitrary-pair invariant needed for `expectedHittingTime_le_of_variable_descent_until_goal`.

### Verification

`lake env lean SSExactMajority/UpperBound/Time/EntryBound.lean` passed after
writing this report.  No changes were made to `EntryBound.lean`.
