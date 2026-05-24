# Codex 026: Time Bound Lower/Upper Plans

## Changes

- Added scheduler probability lemmas in `SSExactMajority/Probability/RandomScheduler.lean`:
  - `mem_offDiagonalPairs`
  - `uniformPair_apply_of_ne`
  - `uniformPair_apply_self`
  - `uniformPair_apply_pair_add_swap_of_ne`
  - `pairSetMass`
  - `pairSetMass_eq_card_mul_inv_of_subset`
  - `pairSetMass_offDiagonalPairs`
  - `GoodPairs`
  - `mem_GoodPairs`
  - `GoodPairs_card_le`
  - `GoodPairs_nonempty_of_descent`
  - `pairSetMass_GoodPairs`
- Added finite-prefix hitting probability helpers in
  `SSExactMajority/Probability/ExpectedTime.lean`:
  - `ProbHitWithin`
  - `probHitBy_add_probNotHitBy`
  - zero-window boundary lemmas
  - `reachesGoalInWindowWithProbAtLeast`
  - `reachesGoalInWindowWithProbAtLeast_zero_of_goal`
  - `expectedSequentialTime`
- Added `docs/TIME_BOUND_PLAN_B.md` for the Theorem 3 lower-bound route.
- Added `docs/TIME_BOUND_PLAN_C.md` for the §5.2 upper-bound route.
- Updated `docs/TIME_BOUND_PLAN.md` and `docs/chatgpt_prompts.md`.
- Updated `SSExactMajority/UpperBound/Time.lean` to state the upper-bound
  scaffold with an explicit constant/externally bounded timer hypothesis,
  plus separate `PEMProtocol` / `ConcretePEM` abbrevs.

## Important finding

Kanaya §5.1's expected lower-bound argument is sound: a fixed unordered pair
fires with probability `2 / (n * (n - 1))`, so the expected sequential wait is
`n * (n - 1) / 2`, hence `Ω(n)` parallel time.

The whp lower-bound step as written is not strong enough for the standard
meaning of whp.  The displayed one-pair geometric tail gives probability
about `n^{-α}` for waiting `Θ(n² log n)` interactions, not probability
`1 - O(1/n)`.  I marked this as a formalization blocker in
`docs/TIME_BOUND_PLAN_B.md`.

The §5.2 upper-bound route has a separate timer issue.  The direct Kanaya
timer-drain estimate costs `x * (n - 1) / 2` sequential interactions for a
timer value `x`.  For the literal Lean target `protocolPEM n n n ...`,
the median timer is `7 * (n + 4) = Θ(n)`, so the direct argument gives
`Θ(n³)` sequential / `Θ(n²)` parallel for that drain part.  The O(n)
parallel theorem should therefore be stated with a constant/externally
bounded timer hypothesis, unless a new `trank = n` timer lemma is proved.

## Verification

- Local single-file:
  `lake env lean SSExactMajority/Probability/RandomScheduler.lean` passed.
- Local `ExpectedTime.lean` direct check is blocked by missing local
  `RandomScheduler.olean`; no local `lake build` was run.
- Remote target build passed on uisai1 via current-tree rsync to
  `~/repos/SSExactMajority-current`:
  `lake build SSExactMajority.Probability.RandomScheduler SSExactMajority.Probability.ExpectedTime SSExactMajority.LowerBound.Time SSExactMajority.UpperBound.Time`

## Sorry count

Correction: converting unproved final theorem stubs into proposition
definitions was not valid progress. The theorem statements have been restored.

Actual remaining theorem-level `sorry`s in the time-bound layer:

- `time_lower_bound_omega_n_expected`
- `PEM_expected_parallel_time_linear_param`

These count as open until the stated theorems have real Lean proofs. No `axiom`,
statement-definition substitute, or weakened theorem is acceptable for closing
them.
