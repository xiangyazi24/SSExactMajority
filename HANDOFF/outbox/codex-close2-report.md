# codex-close2 report

Status: not closed. `OW_consensusBound` still has the old `hRank12`
hypothesis; I did not find a sound derivation using only
`h12reset / h12rank / h12reRank`.

What was verified:

- `PEM_expected_reset_trigger_v2` is available and has exactly the productive
  timer-zero shape:
  `InSswap ∧ MedianAnswerCorrect ∧ wrongAnswerCount > 0 ∧ median timer = 0`
  gives
  `E[T to IsConsensusConfig ∨ CorrectResetSeed] ≤ n(n-1)`.
- The `wrongAnswerCount = 0` branch is immediate by
  `isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero`.
- The existing `CRS_to_consensus_faithful` and
  `OW_exit_rerank_to_swap_event` helpers in `OptimalWindows.lean` compile.

Exact obstruction:

`reset_trigger_v2` fixes the post-drain productive branch, but it does not
separate the earlier decision branch.  The only available decision theorem is
still

```lean
decision_window :
  InSswap C -> MedianTimerAtLeast 1 C -> ¬ MedianAnswerCorrect C ->
  ProbHitWithin C
    (fun D => (InSswap D ∧ MedianAnswerCorrect D) ∨
      ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
    (2 * n * (n - 1)) ≥ 1/2
```

This lower bound may put all guaranteed mass on the `¬ live` disjunct.  After
that, `h12reRank` only returns to live swap with probability `1/2`; it does not
produce consensus, CRS, silence, or MAC.  Chaining
`decision_window -> h12reRank -> retry` inside `ProbHitWithin_add_ge_mul` is
circular: the exit branch requires the same live-to-consensus/productive window
that `OW_consensusBound` is trying to prove.

So the current hypotheses are insufficient to prove a uniform constant
productive window from a live non-MAC state.  One additional ingredient would
close the gap:

- a decision theorem with positive mass on the MAC/live branch, e.g. an
  unconditional version of the existing conditional
  `PEM_phase3_live_decision_hit_lower_bound_of_exit_le_quarter_from_expected`;
  or
- an exit-probability upper bound for the decision window; or
- a stronger `h12reRank` that returns from exit to a productive/silence endpoint
  rather than merely to live swap.

I briefly attempted the timer-drain refinement
`InSswap ∧ MAC ∧ timer>=1 -> consensus ∨ CRS ∨ (InSswap ∧ MAC ∧ timer=0)`
by reusing the deterministic `maxMedianTimer` descent.  That route is
mathematically plausible, but the resulting proof is heavy and was not retained
because it does not address the decision-exit obstruction above.

Verification:

```text
lake env lean SSExactMajority/UpperBound/Time/OptimalWindows.lean
```

Result: exit code 0.  Remaining diagnostics are the pre-existing
`OW_rankBound` `sorry` warning and the unused-section-variable warning on
`decision_window`.

Final `OW_consensusBound` hypothesis list in the checked file:

```lean
hRank12 :
  ∀ C,
    IsTimerBoundedConfig (7 * (Rmax + 4)) C ->
    OW_restartBranch C ->
      (2 : ENNReal)^-1 ≤
        ProbHitWithin P C OW_silenceEndpoint (OW_rank12Window n Rmax)
```

`hRank12` is not eliminated.
