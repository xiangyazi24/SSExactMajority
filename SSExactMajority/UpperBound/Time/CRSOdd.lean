import SSExactMajority.UpperBound.Time.Bridge

namespace SSEM

open scoped ENNReal


set_option maxRecDepth 65536 in
set_option maxHeartbeats 800000000 in
theorem step_InSswap_break_creates_CorrectResetSeed_odd
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    (hOdd : n % 2 ≠ 0)
    {i j : Fin n}
    (hS' : ¬ InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)) :
    CorrectResetSeed (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  -- TODO: unfold transitionPEM + split_ifs + simp_all overflows
  -- maxRecDepth/maxHeartbeats in Lean 4.30 (same issue as CRSEvenTimerPos).
  -- Needs factored helper lemmas instead of brute-force unfolding.
  sorry

end SSEM
