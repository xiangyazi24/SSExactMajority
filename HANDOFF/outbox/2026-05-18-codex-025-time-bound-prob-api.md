# codex time-bound probability API follow-up

Status: completed.

Files touched:
- `SSExactMajority/Probability/ExpectedTime.lean`
- `SSExactMajority/LowerBound/Time.lean`
- `docs/TIME_BOUND_PLAN.md`
- `docs/TIME_BOUND_PLAN_A.md`

Work:
- Added `probHitBy` as the finite-prefix hit probability.
- Added `reachesGoalAlmostSurely` as `⨆ t, P[T ≤ t] = 1`.
- Added `hitsGoalByWithFailureAtMost` as the tail-bound primitive for whp statements.
- Added `expectedParallelTimeToOutputStable` and `expectedParallelTimeToSilent`.
- Added `RandomStabilizesSSEM` to make the lower-bound scaffold depend on uniform-random almost-sure stabilization, not only the existing deterministic existential `SolvesSSEM`.

Verification:
- Remote target build is being run on uisai1 for the current tree.

