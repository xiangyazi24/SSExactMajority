# Generic keystone round-2 satisfiability report

## Verdict

No blocker.  The third over-strong cited-window hypothesis is closed, and the
generic/trank=1 keystones remain genuinely `O(n)`.

The Lean source change is only in
`SSExactMajority/UpperBound/Time/GenericKeystone.lean`; this report was also
updated.
`OptimalWindows.lean` and `GenericTrank.lean` were not edited.

## Round-2 fix

`OW_rankedEpidemicEndpoint m` requires the endpoint majority to equal `m`:
`OptimalWindows.lean:80-82`.  Therefore the cited answer-epidemic/ranking
window cannot be quantified over wrong-answer instances.

The `h12rank` hypothesis now has the faithful precondition
`majorityAnswer D = m` everywhere it is exposed:

| Site | Evidence |
|---|---|
| Generic CRS-to-silence product wrapper | `GenericKeystone.lean:117-125` |
| Generic CRS-to-consensus product wrapper | `GenericKeystone.lean:228-236` |
| Generic end-to-end keystone | `GenericKeystone.lean:290-298` |
| `trank = 1` theorem | `GenericKeystone.lean:687-695` |
| Explicit `O(n)` corollary | `GenericKeystone.lean:804-812` |

The reset/epidemic chain supplies this precondition rather than assuming it for
free.  `CRS_to_silence_faithful_product_generic` threads the invariant
`MajInv D := majorityAnswer D = majorityAnswer C`, proves it is step-invariant
from `majorityAnswer_step_eq`, and strengthens both reset completion and the
epidemic window with `ProbHitWithin_eq_and_inv_of_invariant`:
`GenericKeystone.lean:139-206`.  Thus the final call to `h12rank` is made only
at `m = majorityAnswer C` with `majorityAnswer D = m`.

## Satisfiability sweep

| Hypothesis / field | Satisfiable? | Reason / precondition |
|---|---:|---|
| `h12ranking` in the generic keystone | Yes | Target is `(InSrank ∧ MedianTimerAtLeast 35 ∧ timer-bounded) ∨ IsConsensusConfig`, so an already-silent/consensus start hits at time `0`; non-consensus starts are the cited ranking window. Evidence: `GenericKeystone.lean:275-285`, consumed at `532-540`. |
| `h12ranking` in `PEM_expectedParallelTime_On` and `_On_explicit` | Yes | Same consensus done-escape, specialized to `PEM_trank1_timer`. Evidence: `GenericKeystone.lean:674-682`, `791-799`. |
| `h12reRank` in the generic keystone | Yes | It is only asserted under timer bounds and `¬ (InSswap ∧ MedianTimerAtLeast 35)`, and the target is `(InSswap ∧ MedianTimerAtLeast 35) ∨ IsConsensusConfig`; consensus starts are time-`0`, non-live/non-consensus starts use the cited rerank window. Evidence: `GenericKeystone.lean:299-309`, consumed at `590-609`. |
| `h12reRank` in `PEM_expectedParallelTime_On` and `_On_explicit` | Yes | Same done-escape target and non-live precondition, specialized to `trank = 1`. Evidence: `GenericKeystone.lean:696-705`, `813-822`. |
| `h12rank` in all keystones | Yes after this fix | Added `majorityAnswer D = m`, matching the target's own majority requirement. Wrong-answer `EpidemicPhiGoal m D` instances are no longer demanded. Evidence: `GenericKeystone.lean:290-298`, `687-695`, `804-812`; target shape at `OptimalWindows.lean:80-82`. |
| `h12resetCompletion.resetReach` | Yes | Quantifies only over `CorrectResetSeed C` plus the timer bound, not all configs. The target is `ResetCompletionTarget12 (majorityAnswer C)`, i.e. `EpidemicRegion`, with `K_reset <= C_reset*n*n`; no false deterministic invariant or timer-35 target is required. Evidence: `GenericKeystone.lean:31-44`; `CorrectResetSeed` shape at `BurmanConvergenceFinal.lean:13787-13797`; target shape at `OptimalWindows.lean:338-340`. |
| `h12resetCompletion.epidemicStep`, `epidemicNonincrease`, `epidemicPairDescent` | Yes | These are conditional one-step epidemic-mechanics obligations for configurations already in `EpidemicRegion`; they are not universal reachability windows over arbitrary configs. Evidence: `GenericKeystone.lean:45-69`, consumed at `100-106`. |
| `hTimerStep` | Yes-shaped | This is an invariant-preservation assumption, not a cited hitting-window target; in `trank = 1` it is discharged by `generic_timer_preservation`. Evidence: generic hypothesis at `GenericKeystone.lean:271-274`, specialization at `715-723`. |
| `hRmax`, `hEmax`, `hDmax`, `hn4` | Yes-shaped | Numeric domain assumptions only; they do not assert reachability to a target. Evidence: `GenericKeystone.lean:267-270`, `670-673`, `788-790`. |
| `hRankWindow`, `hRerankWindow` in `_On_explicit` | Yes-shaped | Arithmetic bounds on cited window lengths, not hitting-window hypotheses. They preserve the explicit linear conclusion. Evidence: `GenericKeystone.lean:823-824`, used at `841-850`. |

## O(n) status

The explicit corollary still fixes the reset success probability to the absolute
constant `1/2` and folds all fixed quadratic sequential-window constants into
`PEM_On_explicit_linearConstant`:
`GenericKeystone.lean:779-831`.  The final arithmetic cancels the quadratic
sequential window by division by `n` and rewrites the success-probability factor
to `256`: `GenericKeystone.lean:851-883`.

Therefore the final statement remains
`expectedParallelTimeToConsensus <= PEM_On_explicit_linearConstant ... * n`,
with no dependence on a variable `1 / p_reset`.

## Verification

Checks run:

```bash
exec -a lake /data/home/xhuan5/.elan/bin/elan env lean SSExactMajority/UpperBound/Time/GenericKeystone.lean
exec -a lake /data/home/xhuan5/.elan/bin/elan build
```

I also ran the forbidden-placeholder grep over
`SSExactMajority/UpperBound/Time/GenericKeystone.lean`.

Results:

```text
GenericKeystone single-file Lean check: passed with no output.
Full lake build: Build completed successfully (3266 jobs).
Forbidden-token scan: no matches.
```
