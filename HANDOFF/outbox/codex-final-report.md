# codex-final report

Status: partially wired and self-verified; `OW_consensusBound` was not
soundly refactored to the three [12] hypotheses because the exit branch lacks
the probability separation needed by the current renewal lemma.

Changes in `SSExactMajority/UpperBound/Time/OptimalWindows.lean`:

- Added `CRS_to_consensus_faithful`.
  This discharges the CorrectResetSeed half by calling
  `CRS_to_silence_faithful h12reset h12rank`, then applies the proved
  `OW_silenceEndpoint -> IsConsensusConfig` conversion.
- Added `OW_exit_rerank_to_swap_event`.
  This uses the [12] re-rank hypothesis
  `h12reRank : exit -> ProbHitWithin Live T_rerank >= 1/2`,
  threads the timer-bounded invariant, then composes with
  `swap_live_to_cons_or_crs_or_break`, yielding probability `1/8` of reaching
  the swap-cycle event
  `IsConsensusConfig ∨ CorrectResetSeed ∨ ¬(InSswap ∧ MedianTimerAtLeast 1)`.

Exact obstruction:

`OW_exit_rerank_to_swap_event` only proves re-entry to the same cycle event.
The existing swap window lower-bounds

```lean
ProbHitWithin P C
  (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
    ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
  (OW_swapWindow n Rmax)
```

by `1/4`. It does not lower-bound the productive subevent
`IsConsensusConfig ∨ CorrectResetSeed`; all of the guaranteed `1/4` mass may
be on the exit branch. The [12] `h12reRank` hypothesis returns an exit state
to live-swap with probability `1/2`, but it also does not create any lower
bound for the next swap attempt to be productive rather than another exit.

Therefore the current `expectedHittingTime_le_window_mul_inv_of_invariant`
renewal cannot be closed for `IsConsensusConfig`: its window hypothesis needs
a fixed positive lower bound on hitting consensus within one finite window
from every timer-bounded non-consensus state. With only
`h12reset / h12rank / h12reRank`, the non-live case can be returned to live,
but the live case still has no fixed positive lower bound for
`consensus ∨ CRS` rather than `consensus ∨ CRS ∨ exit`.

The missing additional lemma would be one of:

- a productive swap lower bound:
  `p <= ProbHitWithin P C (fun D => IsConsensusConfig D ∨ CorrectResetSeed D) T`
  from live `InSswap ∧ MedianTimerAtLeast 1`; or
- an exit-probability upper bound strong enough to use the existing subtraction
  lemmas such as
  `PEM_phase3_live_decision_hit_lower_bound_of_exit_le_quarter_from_expected`;
  or
- a renewal theorem whose success event may be `consensus` and whose failure
  branch is certified to return to the same live state class with a separate
  retry bound.

Final hypothesis status:

- Productive CRS branch now cites only:
  `h12reset : CRSResetDuration12 ... T_reset`
  and
  `h12rank : ∀ m D, EpidemicPhiGoal m D -> rankProb <= ProbHitWithin ... (OW_rankedEpidemicEndpoint m) T_rank`,
  plus the existing arithmetic product premise required by
  `CRS_to_silence_faithful`.
- Exit branch now cites only:
  `h12reRank : ∀ C, IsTimerBoundedConfig _ C ->
    ¬(InSswap C ∧ MedianTimerAtLeast 1 C) ->
    (1/2 : ENNReal) <= ProbHitWithin ... C
      (fun D => InSswap D ∧ MedianTimerAtLeast 1 D) T_rerank`.
- `OW_consensusBound` still has the old `hRank12` hypothesis because replacing
  it by only the three [12] hypotheses above would require the missing
  productive-exit probability fact.

Verification:

```text
lake env lean SSExactMajority/UpperBound/Time/OptimalWindows.lean
```

Result: exit code 0. Remaining warnings are pre-existing:
`OW_rankBound` uses `sorry`, and `decision_window` has an unused section
variable warning.
