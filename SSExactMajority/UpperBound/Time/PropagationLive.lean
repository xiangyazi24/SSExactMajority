import SSExactMajority.UpperBound.Time.PolynomialBound

namespace SSEM

open scoped ENNReal

/-- hPropagationLive with IsBoundedConfig: from InSswap + MAC + timer≥1 +
    bounded config + ¬consensus, E[T to consensus] < ⊤.

    The caller (PEM_expected_parallel_time_from_phase_bounds) has
    IsTimerBoundedConfig available as a protocol invariant. We strengthen
    to IsBoundedConfig for bounded_config_to_consensus. -/
theorem PEM_propagation_live_bounded
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (hTimerLo : MedianTimerAtLeast 1 C)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C)
    (hNotCon : ¬ IsConsensusConfig C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C IsConsensusConfig < ⊤ :=
  bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmax C hBounded



/-- End-to-end: expected parallel time to consensus is finite from any initial config.
    Uses IsBoundedConfig invariant + bounded_config_to_consensus. -/
theorem PEM_expected_parallel_time_finite_init
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C₀ : Config (AgentState n) Opinion n)
    (hInit : IsInitialConfig C₀) :
    Probability.expectedParallelTimeToConsensus
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C₀ < ⊤ := by
  have hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C₀ := by
    intro w; have h := hInit w
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hSeq : Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C₀ IsConsensusConfig < ⊤ :=
    bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmax C₀ hBounded
  exact ENNReal.div_lt_top (ne_of_lt hSeq) (by exact_mod_cast (show (n : ℕ) ≠ 0 by omega))

end SSEM
