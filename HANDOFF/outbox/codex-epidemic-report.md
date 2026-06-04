## 2026-06-04 codex epidemic

Created `SSExactMajority/UpperBound/Time/EpidemicBound.lean`.

What is proved:

- `phiAgents`, `nonPhiAgents`, `phiNonPhiPairs`: explicit finite sets for
  phi agents, non-phi agents, and ordered `(phi, non-phi)` scheduler pairs.
- `phiNonPhiPairs_card`: the good-pair count is
  `2 * phiCount C * (n - phiCount C)`.
- `epidemic_phi_pair_mass`: under the uniform off-diagonal scheduler, those
  pairs have mass
  `((2 * phiCount C * (n - phiCount C) : ℕ) : ENNReal) *
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹`.
- `epidemic_phiCount_one_step_prob_ge`: if every `(phi, non-phi)` pair is a
  one-step good pair at level `k`, the one-step hit probability is at least
  `2*k*(n-k)/(n*(n-1))`.
- `epidemic_phiCount_to_zero_expected_le`: the variable-descent expected-time
  theorem:

```lean
Probability.expectedHittingTime P hn C (EpidemicPhiGoal m) ≤
  ∑ r ∈ Finset.range (phiCount C),
    ((((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹)
```

The theorem is conditional on the exact reset-epidemic region facts needed by
`expectedHittingTime_le_of_variable_descent_until_goal`:

- `Inv` implies all answers are in `{m, phi}`.
- Until `EpidemicPhiGoal m`, every step stays in `Inv` or reaches the goal.
- Until the goal, `phiCount` is non-increasing for every scheduler pair.
- Until the goal, every ordered `(phi, non-phi)` pair reaches the goal or
  remains in `Inv` with strictly smaller `phiCount`.

This exposes the precise region obligation.  The raw PEM reset machinery can
leave reset mode when reset counters/delay timers expire, so an unconditional
closed epidemic region is not derivable from just "some correct reset seed";
the closure/timer-survival assumptions have to be supplied by the caller or
the target must include an exit disjunct.

Verification:

```bash
lake env lean SSExactMajority/UpperBound/Time/EpidemicBound.lean
```

Result: passed.  `rg -n "sorry|axiom|native_decide|admit"
SSExactMajority/UpperBound/Time/EpidemicBound.lean` returned no matches.
