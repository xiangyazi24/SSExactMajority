# Generic keystone round-3 WellFormed report

## Verdict

No blocker.  The pathological unbounded-counter class is closed by adding a
structural `WellFormed` domain invariant and requiring it at every cited
[12]-window start.  The `trank = 1` explicit theorem still concludes the same
linear `K * n` bound.

The Lean source change is only in
`SSExactMajority/UpperBound/Time/GenericKeystone.lean`; this report was also
updated.  `OptimalWindows.lean` and `GenericTrank.lean` were not edited.

## Structural Fix

`AgentWellFormed` bounds the unbounded structural fields:
`resetcount <= Rmax`, `errorcount <= Emax`, `delaytimer <= Dmax`, and
`children <= 2`.  I included `children` because it is also a protocol counter
whose pathological values can block faithful ranking/recruitment behavior.

Evidence:

| Item | Evidence |
|---|---|
| Per-agent structural bounds | `GenericKeystone.lean:28-32` |
| Config-level `WellFormed` = protocol timer bound plus structural bounds | `GenericKeystone.lean:36-39` |
| Generic `WellFormed_step` invariant for `PEMProtocol n trank Rmax Emax Dmax` | `GenericKeystone.lean:293-327` |
| Counter/children preservation through OSSR reset/propagate/rankDelta and PEM phase 4 | `GenericKeystone.lean:41-291` |

## Renewal Threading

The generic renewal invariant is now
`Inv C := WellFormed trank Rmax Emax Dmax C /\ IsTimerBoundedConfig T_timer C`:
`GenericKeystone.lean:643-645`.  Its step preservation uses `WellFormed_step`
and the existing `hTimerStep`: `GenericKeystone.lean:684-691`.

The reset-to-epidemic chain also carries `WellFormed` together with the
majority invariant:

| Item | Evidence |
|---|---|
| Local `ChainInv := WellFormed /\ MajInv` | `GenericKeystone.lean:444-468` |
| `resetReach` strengthened to target `ResetCompletionTarget12 /\ ChainInv` | `GenericKeystone.lean:469-482` |
| answer-epidemic window strengthened to `EpidemicPhiGoal /\ ChainInv` | `GenericKeystone.lean:483-503` |
| `h12rank` called only with `EpidemicPhiGoal`, `WellFormed`, and `majorityAnswer D = m` | `GenericKeystone.lean:514-524` |

## Satisfiability Sweep

| Hypothesis / field | Satisfiable? | Reason / precondition |
|---|---:|---|
| `h12ranking` in the generic keystone | Yes | Start requires `WellFormed` and `T_timer` bound. Target includes `(InSrank /\ MedianTimerAtLeast 35 /\ WellFormed /\ T_timer-bound) \/ IsConsensusConfig`, so silent/consensus starts still escape at time 0 and pathological huge-counter starts are outside the cited domain. Evidence: `GenericKeystone.lean:594-604`; consumed at `850-858`. |
| `h12ranking` in `PEM_expectedParallelTime_On` and `_On_explicit` | Yes | Same shape specialized to `trank = 1`; initial theorem now assumes `WellFormed 1 Rmax Emax Dmax C0`. Evidence: `GenericKeystone.lean:992-1001`, `1026-1033`, `1111-1120`, `1147-1153`. |
| `h12reRank` in the generic keystone | Yes | Start requires `WellFormed`, `T_timer` bound, and `not (InSswap /\ MedianTimerAtLeast 35)`. The proof strengthens the hit target with invariant preservation before continuing; already-consensus targets still have a time-0 branch. Evidence: `GenericKeystone.lean:619-629`, consumed and strengthened at `908-918`. |
| `h12reRank` in `PEM_expectedParallelTime_On` and `_On_explicit` | Yes | Same WellFormed start precondition, specialized to `trank = 1`; the wrapper supplies the redundant timer bound from `WellFormed`. Evidence: `GenericKeystone.lean:1016-1025`, `1034-1058`, `1135-1144`. |
| `h12rank` in all keystones | Yes | Start requires `EpidemicPhiGoal m D`, `WellFormed D`, and `majorityAnswer D = m`, matching the endpoint's majority requirement and excluding wrong-answer/pathological starts. Evidence: generic `GenericKeystone.lean:609-618`; `trank = 1` `1006-1015`; explicit `1125-1134`. |
| `h12resetCompletion.resetReach` | Yes | Start requires `WellFormed C` and `CorrectResetSeed C`; it no longer quantifies over timer-only configs with huge `resetcount/errorcount/delaytimer/children`. Target remains the faithful probabilistic reset-completion target `ResetCompletionTarget12 (majorityAnswer C)` within `K_reset = O(n^2)`. Evidence: `GenericKeystone.lean:335-348`; call site `474-481`. |
| `CRSResetCompletion12Generic` local epidemic fields | Yes | `epidemicStep`, `epidemicNonincrease`, and `epidemicPairDescent` are conditional one-step mechanics on configurations already in `EpidemicRegion`; they are not universal hitting-window hypotheses. Evidence: `GenericKeystone.lean:349-373`, consumed at `408-410`. |
| `hTimerStep` | Yes-shaped | This is a timer-bound preservation assumption, not a [12] hitting window. In `trank = 1` it is discharged by `generic_timer_preservation`. Evidence: generic hypothesis `GenericKeystone.lean:590-593`, wrapper proof `1034-1043`. |
| `hRmax`, `hEmax`, `hDmax`, `hn4` | Yes-shaped | Numeric domain assumptions only. They do not assert reachability to a target, and are compatible with the `WellFormed` structural bounds. Evidence: `GenericKeystone.lean:586-589`, `988-991`, `1108-1110`. |
| `hRankWindow`, `hRerankWindow` in `_On_explicit` | Yes-shaped | Arithmetic bounds on fixed cited window lengths, not hitting-window hypotheses. They still feed the same explicit linear arithmetic. Evidence: `GenericKeystone.lean:1145-1146`, used at `1163-1172`. |

## O(n) Status

The O(n) conclusion is not weakened.  `PEM_expectedParallelTime_On_explicit`
still fixes `p_reset = 1/2` and concludes
`expectedParallelTimeToConsensus <= PEM_On_explicit_linearConstant ... * n`;
the only new theorem-domain assumption is `WellFormed 1 Rmax Emax Dmax C0`.

Evidence:

| Item | Evidence |
|---|---|
| Fixed linear constant | `GenericKeystone.lean:1096-1101` |
| Explicit theorem assumes reset success probability `1/2` | `GenericKeystone.lean:1121-1124` |
| Explicit theorem conclusion remains linear in `n` | `GenericKeystone.lean:1147-1153` |
| Quadratic window divided by `n` and success factor rewritten to `256` | `GenericKeystone.lean:1173-1205` |

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
