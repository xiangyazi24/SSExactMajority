# codex-close report

Status: not closed. `OW_consensusBound` still has the old `hRank12`
hypothesis; I did not make a sound replacement by only
`h12reset / h12rank / h12reRank`.

What is currently proved in `OptimalWindows.lean`:

- `CRS_to_consensus_faithful`: CRS branch to consensus using only
  `CRS_to_silence_faithful h12reset h12rank` plus the proved
  `OW_silenceEndpoint -> IsConsensusConfig` link.
- `OW_exit_rerank_to_swap_event`: exit branch uses `h12reRank` to return to
  live swap and then the proved swap window, reaching
  `IsConsensusConfig ∨ CorrectResetSeed ∨ ¬ live`.

Exact obstruction to the requested close:

The requested "productive isolation" lemma does not follow from the two stated
windows alone.

`decision_window` gives a lower bound for hitting

```lean
(InSswap ∧ MedianAnswerCorrect) ∨ ¬ live
```

and `timer_drain_window` gives, from the live/MAC branch, a lower bound for

```lean
IsConsensusConfig ∨ CorrectResetSeed ∨ ¬ live
```

These compose to the already-proved swap-cycle event

```lean
IsConsensusConfig ∨ CorrectResetSeed ∨ ¬ live
```

but they do not imply any positive lower bound for the subevent

```lean
IsConsensusConfig ∨ CorrectResetSeed
```

All of the guaranteed mass in `decision_window` may be on `¬ live`; similarly,
all guaranteed mass in `timer_drain_window` may be on its exit disjunct. A
finite-prefix lower bound on `A ∨ Exit` and a conditional lower bound from `A`
to `Productive ∨ Exit` is insufficient to lower-bound `Productive`.

I also checked the plausible refinement route: strengthen timer drain to a
refined endpoint
`IsConsensusConfig ∨ CorrectResetSeed ∨ (InSswap ∧ MedianAnswerCorrect ∧ ¬ timer)`
and then use `PEM_expected_reset_trigger_v2` to turn the timer-zero exit into
`IsConsensusConfig ∨ CorrectResetSeed`. That would create a real productive
window, but it is not derivable by merely composing the two existing window
theorems; it requires a new refined timer-drain theorem. I did not leave this
unfinished proof in the file.

Verification:

```text
lake env lean SSExactMajority/UpperBound/Time/OptimalWindows.lean
```

Result: exit code 0. Remaining warnings are the existing `OW_rankBound` `sorry`
and the existing unused-section-variable warning on `decision_window`.
