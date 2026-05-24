import SSExactMajority.UpperBound.Time
import SSExactMajority.Convergence.BurmanProof

namespace SSEM
open Probability

/-- From all-Resetting with correct answers, E[T to IsConsensusConfig] is bounded.
Uses ranking_from_all_resetting for the deterministic trace
and expectedHittingTime_le_of_det_trace for the probabilistic bound. -/
theorem allR_to_consensus_bound
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (D : Config (AgentState n) Opinion n)
    (hAllR : ∀ w : Fin n, (D w).1.role = .Resetting)
    (hAllCorrect : ∀ w : Fin n, (D w).1.answer = majorityAnswer D) :
    expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) D IsConsensusConfig ≤
      ((22 * Rmax * n * n : ℕ) : ENNReal) := by
  sorry

end SSEM
