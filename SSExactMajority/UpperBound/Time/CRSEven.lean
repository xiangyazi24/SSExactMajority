import SSExactMajority.UpperBound.Time.Bridge
import SSExactMajority.UpperBound.Time.HeavyProofs

namespace SSEM

open scoped ENNReal

set_option maxRecDepth 65536 in
set_option maxHeartbeats 800000000 in
theorem step_InSswap_break_creates_CorrectResetSeed
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    (hM : MedianAnswerCorrect D)
    (hT : ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n → (D μ).1.timer = 0)
    {i j : Fin n}
    (hS' : ¬ InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)) :
    CorrectResetSeed (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  -- TODO: Same Lean 4.30 issue as CRSOdd/CRSEvenTimerPos:
  -- unfold transitionPEM + split_ifs + simp_all overflows limits.
  -- Needs factored helper lemmas.
  sorry

end SSEM
