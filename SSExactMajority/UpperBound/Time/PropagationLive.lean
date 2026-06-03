import SSExactMajority.UpperBound.Time.PolynomialBound

namespace SSEM

open scoped ENNReal

/-- hPropagationLive with IsBoundedConfig: from InSswap + MAC + timer≥1 +
    bounded config + ¬consensus, E[T to consensus] < ⊤. -/
theorem PEM_propagation_live_bounded
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (_hSswap : InSswap C)
    (_hMedCorrect : MedianAnswerCorrect C)
    (_hTimerLo : MedianTimerAtLeast 1 C)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C)
    (_hNotCon : ¬ IsConsensusConfig C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C IsConsensusConfig < ⊤ :=
  bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmax C hBounded

/-- Consensus is absorbing under PEMProtocolCoupled. -/
theorem PEMProtocolCoupled_consensus_absorbing
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hC : IsConsensusConfig C) (i j : Fin n) :
    IsConsensusConfig
      (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  have hfix : RankDeltaSettledFix (rankDeltaOSSR Rmax Emax Dmax hn0) :=
    rankDeltaOSSR_satisfies_fix
  simpa [PEMProtocolCoupled, PEMProtocol] using step_preserves_consensus hfix hC i j

/-! ### Key lemma: polynomial E[T] from InSswap + MAC to consensus

Under InSswap + MedianAnswerCorrect, the decision-phase interactions
decrease wrongAnswerCount, giving E[T to consensus] ≤ n²(n-1).

The sub-lemmas require:
1. InSswap ∧ MAC preserved or consensus reached at each step
2. wrongAnswerCount non-increasing under InSswap ∧ MAC
3. Descent pair exists with prob ≥ 1/(n(n-1))

Items 2-3 follow from the protocol's decision phase semantics:
with MAC, the median has the correct answer, and interactions with
lower-ranked agents propagate it. Item 1 requires that InSswap is
preserved by all non-consensus steps when MAC holds. -/

-- (Removed: the false `PEM_expected_consensus_from_InSswap_MAC` bound
--  wrongAnswerCount*n(n-1) and its consumer hPropagationLive_proof.
--  That bound is FALSE — correcting non-median answers needs a reset cycle
--  (~O(Rmax*n^2)). The optimal bound goes via OptimalWindows.lean instead.)

/-- End-to-end: expected parallel time to consensus is finite from any initial config. -/
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
