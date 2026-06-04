# Round-5 Dormancy Reset Fix Report

## Verdict

No blocker.

The dormancy hole is closed by removing the exposed deterministic epidemic-step
fields from the reset contracts.  Both reset contracts now expose only the
cited probabilistic reset-completion window:

- Generic: `CRSResetCompletion12Generic.resetReach` reaches
  `EpidemicPhiGoal (majorityAnswer C)` within `K_reset`.
- Coupled legacy path: `CRSResetCompletion12.resetReach` has the same completed
  epidemic target.

I did not introduce a separate finite dormancy predicate as a renewal invariant.
The natural candidates are not preserved under all scheduler pairs: a
`resetcount = 1` pair can drain to zero, and a zero-counter delayed resetting
agent can keep ticking toward wake.  Treating such a condition as the invariant
for `epidemic_phiCount_to_zero_window_ge_half` would reintroduce the same
pathological-config class.  The faithful placement is the one in the spec's
race clause: the cited reset-completion window covers reaching the completed
answer epidemic before reset-counter drain can wake agents.

## Source Changes

| Item | Evidence |
|---|---|
| Generic reset contract has only `resetReach` after positivity/window fields | `SSExactMajority/UpperBound/Time/GenericKeystone.lean:336-349` |
| Generic reset target is completed epidemic, not bare `EpidemicRegion` | `GenericKeystone.lean:342-349` |
| Generic renewal strengthens reset hit with `WellFormed` and majority preservation | `GenericKeystone.lean:383-421` |
| Generic reset-to-silence now composes reset hit directly with rank | `GenericKeystone.lean:422-444` |
| Generic wrapper weakens probability/window only after proving the stronger chain | `GenericKeystone.lean:438-460` |
| Coupled reset contract also has only `resetReach` after positivity/window fields | `SSExactMajority/UpperBound/Time/OptimalWindows.lean:350-363` |
| Coupled reset-to-silence now composes reset hit directly with rank | `OptimalWindows.lean:396-423` |
| Coupled wrapper weakens probability/window only after proving the stronger chain | `OptimalWindows.lean:417-439` |
| `EpidemicMechanics` documents why bare all-resetting is insufficient | `SSExactMajority/UpperBound/Time/EpidemicMechanics.lean:11-15` |
| Remaining local mechanics theorems require explicit non-wake side conditions | `EpidemicMechanics.lean:339-387`, `441-455` |

The old local reset-step assumptions and the old answer-epidemic wrapper are
gone from `GenericKeystone.lean` and `OptimalWindows.lean`; grep for their names
returns no matches.

## Satisfiability Table

| Hypothesis / field | Satisfiable? | Reason |
|---|---:|---|
| `h12ranking` in generic keystone | Yes | Start requires `WellFormed` and the free `T_timer` bound. Target has a consensus escape, so already-consensus starts hit at time 0; non-consensus starts are in the bounded cited domain. Evidence: `GenericKeystone.lean:519-529`, consumed at `775-783`. |
| `h12ranking` in `PEM_expectedParallelTime_On` / explicit | Yes | Same target shape specialized to `trank = 1`; wrappers pass the `WellFormed` start and the timer bound from `WellFormed`. Evidence: `GenericKeystone.lean:917-926`, `1036-1045`, wrapper at `969-984`. |
| `CRSResetCompletion12Generic.resetReach` | Yes | Start requires `WellFormed` and `CorrectResetSeed`; target is the faithful completed answer epidemic for the true `majorityAnswer C`, with `K_reset <= C_reset*n*n`. No forall over arbitrary drained `EpidemicRegion` remains. Evidence: `GenericKeystone.lean:336-349`, used at `413-421`. |
| Coupled `CRSResetCompletion12.resetReach` | Yes | Same completed epidemic target in the older coupled contract. The previous local fields are removed, so only the cited reset window remains. Evidence: `OptimalWindows.lean:350-363`, used at `396-400`. |
| `h12rank` in generic / On / explicit | Yes | Start requires `EpidemicPhiGoal m D`, `WellFormed D`, and `majorityAnswer D = m`, so wrong-answer endpoints are excluded. Evidence: `GenericKeystone.lean:534-543`, `931-940`, `1050-1059`; call site `422-437`. |
| `h12reRank` in generic / On / explicit | Yes | Start requires `WellFormed`, timer boundedness in the generic theorem, and not already live. Target has a consensus escape; the proof strengthens the hit target with invariant preservation before continuing. Evidence: `GenericKeystone.lean:544-554`, `941-950`, `1060-1069`; call site `833-843`. |
| Local epidemic-step facts | Removed | `epidemicStep`, `epidemicNonincrease`, `epidemicPairDescent`, `stepNoPhase4`, `stepAllResetting`, and `pairRankResetting` are no longer hypothesis fields in either reset contract. The reset race is cited through `resetReach`; deterministic mechanics stay in `EpidemicMechanics` with side conditions. |
| `hTimerStep` | Yes-shaped | It is a preservation assumption, not a hitting-window citation. In `trank = 1`, it is discharged by `generic_timer_preservation`. Evidence: `GenericKeystone.lean:515-518`, wrapper proof `960-968`. |
| Arithmetic window hypotheses in explicit theorem | Yes-shaped | `hRankWindow` and `hRerankWindow` are numeric bounds only. Reset has `resetWindow_quadratic`; the final bound remains linear. Evidence: `GenericKeystone.lean:1070-1078`, arithmetic at `1088-1130`. |

## O(n) Status

The explicit theorem is unchanged in strength.  It still fixes the reset
success probability to `1/2`, keeps `K_reset <= C_reset*n*n`, and concludes

```text
expectedParallelTimeToConsensus <= PEM_On_explicit_linearConstant ... * n
```

Evidence:

| Item | Evidence |
|---|---|
| Fixed linear coefficient | `GenericKeystone.lean:1021-1026` |
| Explicit theorem fixes reset probability at `1/2` | `GenericKeystone.lean:1046-1049` |
| Explicit theorem conclusion is linear in `n` | `GenericKeystone.lean:1072-1078` |
| Quadratic sequential window divided by `n` | `GenericKeystone.lean:1088-1130` |

## Verification

Checks run:

```bash
/data/home/xhuan5/.elan/bin/elan run $(cat lean-toolchain) lake env lean SSExactMajority/UpperBound/Time/OptimalWindows.lean
/data/home/xhuan5/.elan/bin/elan run $(cat lean-toolchain) lake env lean SSExactMajority/UpperBound/Time/GenericKeystone.lean
/data/home/xhuan5/.elan/bin/elan run $(cat lean-toolchain) lake build
```

Results:

```text
OptimalWindows single-file Lean check: passed, with one pre-existing linter warning.
GenericKeystone single-file Lean check: passed with no output.
Full lake build: Build completed successfully (3266 jobs).
Forbidden-placeholder scan: no matches in the changed Lean files or this report.
Local reset-step-field grep: no matches in GenericKeystone.lean or OptimalWindows.lean.
```
