import SSExactMajority.Convergence.BurmanConvergenceFinal
import SSExactMajority.Probability.ExpectedTime

namespace SSEM

open scoped ENNReal

variable {n : ℕ}

abbrev PEMProtocolCoupled' (n Rmax Emax Dmax : ℕ) (hn : 0 < n) :
    Protocol (AgentState n) Opinion Output :=
  protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)

noncomputable def maxRC (C : Config (AgentState n) Opinion n) : ℕ :=
  Finset.sup Finset.univ
    (fun w : Fin n => if (C w).1.role = .Resetting then (C w).1.resetcount else 0)

theorem maxRC_le_of_all_le {C : Config (AgentState n) Opinion n} {M : ℕ}
    (h : ∀ w : Fin n, (C w).1.role = .Resetting → (C w).1.resetcount ≤ M) :
    maxRC C ≤ M := by
  unfold maxRC; apply Finset.sup_le; intro w _
  by_cases hr : (C w).1.role = .Resetting <;> simp [hr, h w hr]

/-- Strong recovery invariant: all Resetting, all correct answers, rc bounded.
Phase4 never fires (no Settled pair), so answers are preserved
and maxRC is non-increasing through rc-sync. -/
structure StrongRecoveryInv (Rmax : ℕ) (C : Config (AgentState n) Opinion n) : Prop where
  allResetting : ∀ w : Fin n, (C w).1.role = .Resetting
  allCorrect : ∀ w : Fin n, (C w).1.answer = majorityAnswer C
  rcBounded : ∀ w : Fin n, (C w).1.resetcount ≤ Rmax

/-- Phase 1 goal: StrongRecoveryInv holds with maxRC = 0, or consensus.
When maxRC = 0 and all Resetting, all agents have rc=0 and will
drain delaytimers before exiting. Phase 2 handles the rest. -/
def Phase1Goal (Rmax : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  IsConsensusConfig C ∨ (StrongRecoveryInv Rmax C ∧ maxRC C = 0)

-- Helper: under StrongRecoveryInv, step preserves invariant or reaches Phase1Goal
theorem strongRecoveryInv_step
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    (hInv : StrongRecoveryInv Rmax C) (i j : Fin n) :
    StrongRecoveryInv Rmax (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) ∨
    Phase1Goal Rmax (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) := by
  sorry

theorem maxRC_step_le_strong
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    (hInv : StrongRecoveryInv Rmax C) (i j : Fin n) :
    maxRC (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) ≤ maxRC C := by
  sorry

theorem maxRC_descent_strong
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hInv : StrongRecoveryInv Rmax C)
    (hNotGoal : ¬ Phase1Goal Rmax C) (hpos : 0 < maxRC C) :
    ∃ u v : Fin n, u ≠ v ∧
      ((StrongRecoveryInv Rmax (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) u v) ∧
        maxRC (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) u v) < maxRC C) ∨
        Phase1Goal Rmax (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) u v)) := by
  sorry

/-- Phase 2: from Phase1Goal (maxRC=0 all-Resetting or consensus) to consensus.
This is the re-ranking phase: delaytimer drain → Settled/Unsettled →
binary tree ranking → InSswap → consensus. -/
theorem phase1Goal_to_consensus
    {Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn : 0 < n) (hRmax : n ≤ Rmax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hGoal : Phase1Goal Rmax C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn) (by omega : 2 ≤ n)
      C IsConsensusConfig ≤ ((Rmax * n * n : ℕ) : ENNReal) := by
  sorry

/-- Main theorem: from all-Resetting + correct to consensus in 2·Rmax·n². -/
set_option linter.unusedDecidableInType false in
theorem allR_to_consensus_bound
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hDmax : n ≤ Dmax)
    (D : Config (AgentState n) Opinion n)
    (hAllR : ∀ w : Fin n, (D w).1.role = .Resetting)
    (hAllCorrect : ∀ w : Fin n, (D w).1.answer = majorityAnswer D)
    (hBounded : ∀ w : Fin n, (D w).1.resetcount ≤ Rmax) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) D IsConsensusConfig ≤
      ((2 * Rmax * n * n : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  have hInv0 : StrongRecoveryInv Rmax D := ⟨hAllR, hAllCorrect, hBounded⟩
  -- Phase 1: maxRC descent to Phase1Goal
  have hPhase1 : Probability.expectedHittingTime P hn2 D (Phase1Goal Rmax) ≤
      ((Rmax * n * n : ℕ) : ENNReal) := by
    have hmaxRC_le : maxRC D ≤ Rmax := maxRC_le_of_all_le (fun w _ => hBounded w)
    have hDescent := Probability.expectedHittingTime_le_of_deterministic_descent
      P hn2 D (Phase1Goal Rmax) (StrongRecoveryInv Rmax) maxRC hInv0
      (fun C hInv hphi => Or.inr ⟨hInv, hphi⟩)
      (fun C hInv _ i j => strongRecoveryInv_step C hInv i j)
      (fun C hInv _ i j => maxRC_step_le_strong C hInv i j)
      (fun C hInv hGoal hpos => maxRC_descent_strong hn4 C hInv hGoal hpos)
    calc Probability.expectedHittingTime P hn2 D (Phase1Goal Rmax)
        ≤ ↑(maxRC D) * ((n * (n - 1) : ℕ) : ENNReal) := hDescent
      _ ≤ ((Rmax * n * n : ℕ) : ENNReal) := by
          norm_cast
          calc maxRC D * (n * (n - 1))
              ≤ Rmax * (n * (n - 1)) := Nat.mul_le_mul_right _ hmaxRC_le
            _ ≤ Rmax * (n * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le n 1))
            _ = Rmax * n * n := by ring
  -- Phase 2: Phase1Goal to consensus
  have hPhase2 : ∀ C, Phase1Goal Rmax C →
      Probability.expectedHittingTime P hn2 C IsConsensusConfig ≤
        ((Rmax * n * n : ℕ) : ENNReal) :=
    fun C hC => phase1Goal_to_consensus hn4 hn0 hRmax hDmax C hC
  -- Compose
  calc Probability.expectedHittingTime P hn2 D IsConsensusConfig
      ≤ ((Rmax * n * n : ℕ) : ENNReal) + ((Rmax * n * n : ℕ) : ENNReal) :=
        Probability.expectedHittingTime_add_le P hn2 D (Phase1Goal Rmax) IsConsensusConfig
          _ _ hPhase1 hPhase2 (fun C h => Or.inl h)
    _ = ((2 * Rmax * n * n : ℕ) : ENNReal) := by push_cast; ring

end SSEM
