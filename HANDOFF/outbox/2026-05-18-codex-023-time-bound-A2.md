# codex time-bound A2

Status: completed.

Files touched:
- `SSExactMajority/Probability/ExpectedTime.lean`
- `docs/TIME_BOUND_PLAN_A.md`

Work:
- Implemented `expectedHittingTime` using the PMF finite-prefix tail-sum route.
- Added `hitFlagStepDist`, `hitFlagDist`, and `probNotHitBy` so the event is "goal has been hit by time t", not merely the marginal at step `t`.
- Wrote the probability foundation memo in `docs/TIME_BOUND_PLAN_A.md`.

Verification:
- Remote target build passed on uisai1:
  `lake build SSExactMajority.Probability.RandomScheduler SSExactMajority.Probability.ExpectedTime SSExactMajority.LowerBound.Time SSExactMajority.UpperBound.Time`

