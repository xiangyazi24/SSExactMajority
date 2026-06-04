import SSExactMajority.UpperBound.Time.OptimalWindows
import SSExactMajority.UpperBound.Time.AnswerEpidemicBridge

namespace SSEM

open scoped BigOperators ENNReal

/-- Fresh reset-seed target delivered by the faithful reset-completion
citation: the answer epidemic has a valid seed, and every agent has been
freshly reset with delay timer `Dmax`. -/
def FreshResetSeedTarget {n : ℕ} (Dmax : ℕ) (m : Answer)
    (C : Config (AgentState n) Opinion n) : Prop :=
  EpidemicRegion m C ∧
    ∀ a : Fin n, (C a).1.role = .Resetting ∧ (C a).1.delaytimer = Dmax

/-- Faithful [12]-cited reset-completion contract.

The cited reset window delivers a fresh epidemic-region reset seed. It does
not cite the PEM-specific answer-epidemic completion; that completion is
proved separately by `answer_epidemic_bridge_from_fresh_resetting`. -/
structure CRSReset12Faithful {n Rmax Emax Dmax : ℕ} (hn : 0 < n)
    (p_reset : ENNReal) (C_reset K_reset : ℕ) : Prop where
  resetProb_pos : 0 < p_reset
  resetProb_le_one : p_reset ≤ 1
  resetConstant_pos : 0 < C_reset
  resetWindow_quadratic : K_reset ≤ C_reset * n * n
  freshSeedReach :
    ∀ (hn2 : 2 ≤ n) (C : Config (AgentState n) Opinion n),
      IsTimerBoundedConfig (7 * (1 + 4)) C →
      CorrectResetSeed C →
        p_reset ≤
          Probability.ProbHitWithin
            (PEMProtocol n 1 Rmax Emax Dmax hn) hn2 C
            (FreshResetSeedTarget Dmax (majorityAnswer C)) K_reset

/-- Compose the faithful [12] fresh-reset seed reachability with the proven
answer-epidemic bridge at `trank = 1`. -/
theorem faithful_reset_to_phiGoal
    {n Rmax Emax Dmax K_reset K_bridge C_reset : ℕ}
    (hn : 0 < n) (hn2 : 2 ≤ n) (hDmax : n ≤ Dmax)
    {p_reset pE : ENNReal}
    (h12reset :
      CRSReset12Faithful (n := n) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) hn p_reset C_reset K_reset)
    (epidemicFast :
      StandardEpidemicFastHypothesisPEM
        n Rmax Emax Dmax K_bridge hn hn2 pE)
    (hTail : drainNoWakeTail n K_bridge Dmax ≤ pE / 2) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (1 + 4)) C →
      CorrectResetSeed C →
        p_reset * (pE / 2) ≤
          Probability.ProbHitWithin
            (PEMProtocol n 1 Rmax Emax Dmax hn) hn2 C
            (fun D => EpidemicPhiGoal (majorityAnswer C) D ∧
              AllAgentsResetting D)
            (K_reset + K_bridge) := by
  classical
  intro C hTimer hSeed
  let P : Protocol (AgentState n) Opinion Output :=
    PEMProtocol n 1 Rmax Emax Dmax hn
  let Mid : Config (AgentState n) Opinion n → Prop :=
    FreshResetSeedTarget Dmax (majorityAnswer C)
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => EpidemicPhiGoal (majorityAnswer C) D ∧ AllAgentsResetting D
  have hDmax_pos : 0 < Dmax := Nat.lt_of_lt_of_le hn hDmax
  have hFreshSeed :
      p_reset ≤ Probability.ProbHitWithin P hn2 C Mid K_reset := by
    simpa [P, Mid] using h12reset.freshSeedReach hn2 C hTimer hSeed
  have hBridge :
      ∀ D : Config (AgentState n) Opinion n, Mid D →
        pE / 2 ≤ Probability.ProbHitWithin P hn2 D Goal K_bridge := by
    intro D hD
    exact
      answer_epidemic_bridge_from_fresh_resetting
        (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (K := K_bridge) (C₀ := D) (m := majorityAnswer C)
        (pE := pE) hn hn2 hDmax_pos hD.2 hD.1 hTail epidemicFast
  exact
    Probability.ProbHitWithin_add_ge_mul P hn2 C Mid Goal
      K_reset K_bridge p_reset (pE / 2) hFreshSeed hBridge

end SSEM
