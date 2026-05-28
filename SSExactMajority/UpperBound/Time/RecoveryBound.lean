import SSExactMajority.Convergence.BurmanConvergenceFinal
import SSExactMajority.Probability.ExpectedTime

namespace SSEM

open scoped ENNReal

variable {n : ℕ}

/-- PEM protocol with coupled trank = Rmax (local copy to avoid sorry-laden Time.lean). -/
abbrev PEMProtocolCoupled' (n Rmax Emax Dmax : ℕ) (hn : 0 < n) :
    Protocol (AgentState n) Opinion Output :=
  protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)

/-! ### Max resetcount across Resetting agents -/

noncomputable def maxRC (C : Config (AgentState n) Opinion n) : ℕ :=
  Finset.sup Finset.univ
    (fun w : Fin n => if (C w).1.role = .Resetting then (C w).1.resetcount else 0)

theorem maxRC_ge_of_resetting {C : Config (AgentState n) Opinion n}
    {w : Fin n} (hw : (C w).1.role = .Resetting) :
    (C w).1.resetcount ≤ maxRC C := by
  unfold maxRC
  have h := Finset.le_sup (f := fun w : Fin n =>
    if (C w).1.role = .Resetting then (C w).1.resetcount else 0) (Finset.mem_univ w)
  simp only [hw, ite_true] at h
  exact h

theorem maxRC_eq_zero_iff {C : Config (AgentState n) Opinion n} :
    maxRC C = 0 ↔ ∀ w : Fin n, (C w).1.role = .Resetting → (C w).1.resetcount = 0 := by
  constructor
  · intro h w hw
    have := maxRC_ge_of_resetting hw; omega
  · intro h
    unfold maxRC
    show Finset.sup Finset.univ _ = 0
    have : (0 : ℕ) = ⊥ := rfl
    rw [this]
    rw [Finset.sup_eq_bot_iff]
    intro w _
    by_cases hr : (C w).1.role = .Resetting
    · simp [hr, h w hr]
    · simp [hr]

theorem maxRC_le_of_all_le {C : Config (AgentState n) Opinion n} {M : ℕ}
    (h : ∀ w : Fin n, (C w).1.role = .Resetting → (C w).1.resetcount ≤ M) :
    maxRC C ≤ M := by
  unfold maxRC
  apply Finset.sup_le
  intro w _
  by_cases hr : (C w).1.role = .Resetting
  · simp [hr]; exact h w hr
  · simp [hr]

/-! ### Recovery-phase invariant -/

def RecoveryInv (Rmax : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  (∀ w : Fin n, (C w).1.answer = majorityAnswer C) ∧
  (∀ w : Fin n, (C w).1.resetcount ≤ Rmax)

theorem recoveryInv_step
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    (hInv : RecoveryInv Rmax C)
    (i j : Fin n) :
    RecoveryInv Rmax (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) := by
  sorry

theorem maxRC_step_le
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    (hInv : RecoveryInv Rmax C)
    (i j : Fin n) :
    maxRC (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) ≤ maxRC C := by
  sorry

theorem maxRC_descent
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hInv : RecoveryInv Rmax C)
    (hNotGoal : ¬ IsConsensusConfig C)
    (hpos : 0 < maxRC C) :
    ∃ u v : Fin n, u ≠ v ∧
      ((RecoveryInv Rmax (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) u v) ∧
        maxRC (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) u v) < maxRC C) ∨
        IsConsensusConfig (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) u v)) := by
  sorry

theorem maxRC_zero_to_consensus
    {Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn : 0 < n) (hRmax : n ≤ Rmax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hInv : RecoveryInv Rmax C)
    (hMaxRC0 : maxRC C = 0) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn)
      (by omega : 2 ≤ n) C IsConsensusConfig ≤
      ((Rmax * n * n : ℕ) : ENNReal) := by
  sorry

/-! ### Main theorem -/

set_option linter.unusedDecidableInType false in
theorem allR_to_consensus_bound
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hDmax : n ≤ Dmax)
    (D : Config (AgentState n) Opinion n)
    (hAllR : ∀ w : Fin n, (D w).1.role = .Resetting)
    (hAllCorrect : ∀ w : Fin n, (D w).1.answer = majorityAnswer D) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) D IsConsensusConfig ≤
      ((2 * Rmax * n * n : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  let Mid := fun C : Config (AgentState n) Opinion n =>
    IsConsensusConfig C ∨ (RecoveryInv Rmax C ∧ maxRC C = 0)
  have hMidGoal : ∀ C, IsConsensusConfig C → Mid C :=
    fun C h => Or.inl h
  -- Phase 1: maxRC descent
  have hPhase1 : Probability.expectedHittingTime P hn2 D Mid ≤
      ((Rmax * n * n : ℕ) : ENNReal) := by
    have hInv0 : RecoveryInv Rmax D := by
      refine ⟨fun w => hAllCorrect w, fun w => ?_⟩
      sorry -- (D w).1.resetcount <= Rmax: protocol invariant
    have hmaxRC_le : maxRC D ≤ Rmax :=
      maxRC_le_of_all_le (fun w _ => hInv0.2 w)
    have hDescent := Probability.expectedHittingTime_le_of_deterministic_descent
      P hn2 D Mid (RecoveryInv Rmax) maxRC hInv0
      (fun C hInv hphi => Or.inr ⟨hInv, hphi⟩)
      (fun C hInv _ i j => Or.inl (recoveryInv_step C hInv i j))
      (fun C hInv _ i j => maxRC_step_le C hInv i j)
      (fun C hInv hGoal hpos => by
        have hNC : ¬ IsConsensusConfig C := fun h => hGoal (Or.inl h)
        obtain ⟨u, v, huv, h⟩ := maxRC_descent hn4 C hInv hNC hpos
        exact ⟨u, v, huv, h.imp (fun ⟨a, b⟩ => ⟨a, b⟩) (fun h => Or.inl h)⟩)
    have h_arith : ↑(maxRC D) * ((n * (n - 1) : ℕ) : ENNReal) ≤
        ((Rmax * n * n : ℕ) : ENNReal) := by
      sorry -- maxRC D ≤ Rmax, n*(n-1) ≤ n*n, so product ≤ Rmax*n*n
    exact le_trans hDescent h_arith
  -- Phase 2
  have hPhase2 : ∀ C, Mid C →
      Probability.expectedHittingTime P hn2 C IsConsensusConfig ≤
        ((Rmax * n * n : ℕ) : ENNReal) := by
    intro C hC
    rcases hC with hCons | ⟨hInv, hMaxRC0⟩
    · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 C IsConsensusConfig hCons]
      exact bot_le
    · exact maxRC_zero_to_consensus hn4 hn0 hRmax hDmax C hInv hMaxRC0
  -- Compose
  calc Probability.expectedHittingTime P hn2 D IsConsensusConfig
      ≤ ((Rmax * n * n : ℕ) : ENNReal) + ((Rmax * n * n : ℕ) : ENNReal) :=
        Probability.expectedHittingTime_add_le P hn2 D Mid IsConsensusConfig
          _ _ hPhase1 hPhase2 hMidGoal
    _ = ((2 * Rmax * n * n : ℕ) : ENNReal) := by push_cast; ring

end SSEM
