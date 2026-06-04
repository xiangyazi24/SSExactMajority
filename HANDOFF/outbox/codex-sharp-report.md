# codex-sharp report

- Refactored the old existential awakening witness through
  `awakening_step_descent_of_resetting_follower`: for every
  `w ∈ awakeningResettingFollowers C`, the unique awakening root meeting `w`
  preserves `IsAwakeningConfig` and strictly decreases the resetting-follower
  card.
- Proved `awakening_step_descent_prob_sharp` with the pair set
  `(awakeningResettingFollowers C).image (fun w => (root, w))`.
  Its image has card `k`, is contained in `OffDiagonalPairs n`, and every pair
  hits the descent/exit target, so `pairSetMass_eq_card_mul_inv_of_subset` and
  `ProbHitWithin_one_lower_bound_of_pairSet` give `k/(n(n-1))`.
- Proved `awakening_to_goal_or_exit_expected_le_sharp` by applying
  `expectedHittingTime_le_of_variable_descent_until_goal` with
  `pRate k = k/(n(n-1))`. The resulting bound is the explicit coupon-collector
  sum
  `∑ k ∈ Finset.range (awakeningResettingFollowers C).card,
    (((k + 1 : ℕ) : ENNReal) / ((n * (n - 1) : ℕ) : ENNReal))⁻¹`.
- Verification: `lake env lean SSExactMajority/UpperBound/Time/EntryBound.lean`
  passed.
