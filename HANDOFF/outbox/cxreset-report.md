# Answer-Epidemic Attack 4 Report

### BLOCKER

I wrote Lean for the attack4 reset-target issue.  The requested probabilistic
race cannot be started from the bare `EpidemicRegion` target: that predicate is
only all-`Resetting` plus answer-shape, and it permits drained reset counters
and drained delay timers.  Such a configuration can wake on the very next
interaction.

## Lean Proven

| Theorem / definition | File | Result |
|---|---|---|
| `NoWakeAgent` | `SSExactMajority/UpperBound/Time/OptimalWindows.lean:375` | Exact one-step no-wake condition: `0 < resetcount ∨ 1 < delaytimer`. |
| `processAgent_noWake_role` | `SSExactMajority/UpperBound/Time/OptimalWindows.lean:380` | If a `Resetting` endpoint satisfies `NoWakeAgent` and has a Resetting partner, then `processAgent` keeps it `Resetting` for that step. |
| `processAgent_noWake_not_preserved_counterexample` | `SSExactMajority/UpperBound/Time/OptimalWindows.lean:409` | The correct one-step no-wake condition decays and is not an invariant. |
| `bare_epidemicRegion_can_wake_counterexample` | `SSExactMajority/UpperBound/Time/OptimalWindows.lean:437` | A bare `EpidemicRegion .outA` configuration on two agents has all agents `Resetting`, but one scheduled interaction makes agent `0` `Settled`; hence `still all Resetting` fails immediately. |

## False Subfact

The false attack4 subfact is:

```text
The [12] reset target can be weakened to bare EpidemicRegion and still serve as
the universal start state for the local joint answer-epidemic race.
```

Counterexample state:

```text
n = 2
agent 0: role=Resetting, leader=L, resetcount=0, delaytimer=0, answer=outA
agent 1: role=Resetting, leader=F, resetcount=0, delaytimer=0, answer=phi
```

This satisfies `EpidemicRegion .outA`.  But for the interaction `(0,1)`,
`processAgent` fires `resetOSSR` on agent `0`, and the post-state role is
`Settled`, not `Resetting`.  Therefore the joint target
`EpidemicPhiGoal ... ∧ still all Resetting` cannot be proved uniformly from
bare `EpidemicRegion`.

## Consequence

The faithful reset citation must target a stronger non-answer condition, e.g.
a fresh all-resetting `DormantStart` carrying reset-counter/delay lower bounds,
not bare `EpidemicRegion` and not `EpidemicPhiGoal`.  The existing
`resetReach` target is still over-cited to `EpidemicPhiGoal`; changing it to
bare `EpidemicRegion` would make the bridge start condition false by the Lean
counterexample above.

## Verification

Single-file check:

```bash
/data/home/xhuan5/.elan/bin/elan run $(cat lean-toolchain) lake env lean SSExactMajority/UpperBound/Time/OptimalWindows.lean
```

Result: passed, with the pre-existing `decision_window` unused-section-variable
linter warning.

Full build:

```bash
/data/home/xhuan5/.elan/bin/elan run $(cat lean-toolchain) lake build
```

Result: passed, with pre-existing linter warnings.

Forbidden-token scan: passed for the touched Lean/report files.
