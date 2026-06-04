## 2026-06-04 codex-elim

Status: blocked. `hRank12` was not eliminated from `OW_consensusBound` or
`PEM_expectedParallelTime_optimal`.

Verified facts:

- `DecisionProductiveTarget` in `DecisionTiming.lean` is exactly
  `(InSswap ∧ MedianAnswerCorrect ∧ MedianTimerAtLeast 1) ∨
   IsConsensusConfig ∨ CorrectResetSeed`.
- `decision_before_timer_zero` is proven and gives the requested
  `1/4` productive window from `InSswap ∧ MedianTimerAtLeast 35`.
- `CRS_to_consensus_faithful` / `CRS_to_silence_faithful` are available for
  the CRS branch using `h12resetDuration` and `h12rank`.
- `PEM_expected_reset_trigger_v2` is available for
  `InSswap ∧ MedianAnswerCorrect ∧ timer=0 ∧ wrongAnswerCount>0 →
   IsConsensusConfig ∨ CorrectResetSeed`.

Precise obstruction:

The missing bridge is the non-exit MAC drain window needed before applying
`PEM_expected_reset_trigger_v2`:

```lean
InSswap C →
MedianAnswerCorrect C →
MedianTimerAtLeast 1 C →
IsTimerBoundedConfig (7 * (Rmax + 4)) C →
ProbHitWithin ... C
  (fun D =>
    IsConsensusConfig D ∨ CorrectResetSeed D ∨
      (InSswap D ∧ MedianAnswerCorrect D ∧ ¬ MedianTimerAtLeast 1 D))
  K ≥ const
```

The existing proven `timer_drain_window` only gives

```lean
IsConsensusConfig ∨ CorrectResetSeed ∨
  ¬ (InSswap ∧ MedianTimerAtLeast 1)
```

That exit branch is too weak.  `h12reRank` can return an exit state to a fresh
live swap state, but it does not itself hit consensus.  Composing
`decision_before_timer_zero → timer_drain_window → h12reRank` therefore
requires recursively invoking the same fresh-swap consensus window inside the
one-window success proof, which is circular for
`expectedHittingTime_le_window_mul_inv_of_invariant`.

I briefly attempted the necessary refined drain theorem by cloning the
`PEM_expected_timer_drain_poly` deterministic-descent proof and splitting the
`¬live` endpoint into `CRS` vs. `InSswap ∧ MAC ∧ ¬timer≥1`; this is the right
shape, but it was not completed into a checked lemma.  No `sorry`, `axiom`, or
`native_decide` was added.

Current checked theorem interfaces remain unchanged:

- `OW_consensusBound` still takes the old `hRank12`.
- `PEM_expectedParallelTime_optimal` still takes and threads the old `hRank12`.

Verification:

```bash
lake env lean SSExactMajority/UpperBound/Time/OptimalWindows.lean
```

exited 0.  The only output was the existing unused section-variable warning at
`OptimalWindows.lean:534`.
