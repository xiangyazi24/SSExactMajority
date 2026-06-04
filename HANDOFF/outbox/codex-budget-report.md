# Reset-budget report

Lean file added:

- `SSExactMajority/UpperBound/Time/ResetBudget.lean`

Verified:

- `lake env lean SSExactMajority/UpperBound/Time/ResetBudget.lean`

Definitions:

- `sameRankSettledPairs C`: ordered off-diagonal pairs `(i,j)` with `i ≠ j`,
  both endpoints `Settled`, and equal ranks.
- `resetBudget C := (sameRankSettledPairs C).card`.

Proved:

- `resetBudget_le_quadratic`: `resetBudget C ≤ n * n`.
- `rankDeltaOSSR_collision_roles`: the raw `rankDeltaOSSR` collision branch
  sends a same-rank `Settled`/`Settled` pair to two `Resetting` states.
- `transitionPEM_collision_roles`: the same role conclusion survives the
  concrete PEM wrapper; phase 4 is disabled because the pre-phase output is
  not both `Settled`.
- `resetBudget_strict_decrease_at_collision`: for the concrete coupled PEM
  transition `protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)`, if
  the scheduled off-diagonal pair is same-rank `Settled`/`Settled`, then
  `resetBudget` strictly decreases.

Investigation findings:

- Collision reset resolves exactly a duplicate settled rank. Both scheduled
  endpoints leave `Settled`, all bystanders are unchanged, and no new
  same-rank settled pair can be introduced by this branch. The proof removes
  at least the scheduled ordered pair `(i,j)` from the budget.
- Error reset is in `rankDeltaOSSR` Part 4. Each `Unsettled` endpoint first
  gets `errorcount := errorcount - 1`; if the post-decrement counter is `0`
  (equivalently, the old counter was `0` or `1` under Nat subtraction), that
  endpoint becomes `Resetting`, and the final guard then sets both endpoints
  to `Resetting`.
- A simple global errorcount budget is not yet monotone for the full protocol:
  error monitoring decreases counters locally, but `resetOSSR` can initialize
  a follower as `Unsettled` with `errorcount = Emax`; also recruitment and
  wake-up branches change roles in ways not captured by the collision-only
  budget. The full non-increase theorem therefore needs either a phase
  invariant excluding those counter-increase branches, or a lexicographic/
  phase-indexed budget that accounts for wake-up/recruitment separately.

No `sorry`, `axiom`, or `native_decide` was used in `ResetBudget.lean`.
