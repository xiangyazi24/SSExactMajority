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

/-! ### Resetcount lemmas -/

private theorem resetOSSR_rc {Emax : ℕ} {hn : 0 < n} (s : AgentState n) :
    (resetOSSR Emax hn s).resetcount = s.resetcount := by
  unfold resetOSSR; cases s.leader <;> rfl

set_option maxHeartbeats 8000000 in
private theorem processAgent_rc_eq
    {Emax Dmax : ℕ} {hn : 0 < n}
    (s : AgentState n) (oldRc : ℕ) (pr : Bool) :
    (processAgent Emax Dmax hn s oldRc pr).resetcount = s.resetcount := by
  unfold processAgent
  by_cases h1 : s.role = .Resetting ∧ s.resetcount = 0
  · simp only [h1, ite_true, and_self]
    by_cases h2 : 0 < oldRc
    · simp only [h2, ite_true]
      by_cases h3 : (Dmax = 0 ∨ (!pr) = true)
      · simp only [h3, ite_true]; rw [resetOSSR_rc]
      · simp only [show ¬(Dmax = 0 ∨ (!pr) = true) from h3, ite_false]
    · simp only [show ¬(0 < oldRc) from h2, ite_false]
      by_cases h3 : (s.delaytimer - 1 = 0 ∨ (!pr) = true)
      · simp only [h3, ite_true]; rw [resetOSSR_rc]
      · simp only [show ¬(s.delaytimer - 1 = 0 ∨ (!pr) = true) from h3, ite_false]
  · simp only [show ¬(s.role = .Resetting ∧ s.resetcount = 0) from h1, ite_false]

set_option maxHeartbeats 8000000 in
private theorem propagateReset_rc_le
    {Emax Dmax : ℕ} {hn : 0 < n} (M : ℕ)
    {a b : AgentState n}
    (ha : a.resetcount ≤ M) (hb : b.resetcount ≤ M) :
    (propagateReset Emax Dmax hn a b).1.resetcount ≤ M ∧
    (propagateReset Emax Dmax hn a b).2.resetcount ≤ M := by
  unfold propagateReset
  constructor
  · rw [processAgent_rc_eq]; split_ifs <;> simp_all <;> omega
  · rw [processAgent_rc_eq]; split_ifs <;> simp_all <;> omega

set_option maxHeartbeats 8000000 in
private theorem rankDeltaOSSR_rc_le_Rmax
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (s t : AgentState n)
    (hs_rc : s.resetcount ≤ Rmax) (ht_rc : t.resetcount ≤ Rmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount ≤ Rmax ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount ≤ Rmax := by
  unfold rankDeltaOSSR
  by_cases h1 : s.role = .Resetting ∨ t.role = .Resetting
  · simp only [h1, ite_true]
    have hpr := propagateReset_rc_le (Emax := Emax) (Dmax := Dmax) (hn := hn) Rmax hs_rc ht_rc
    exact ⟨hpr.1, by split_ifs <;> simp_all⟩
  · push_neg at h1; obtain ⟨hs_nr, ht_nr⟩ := h1
    simp only [show ¬(s.role = .Resetting ∨ t.role = .Resetting) from
      fun h => h.elim hs_nr ht_nr, ite_false]
    by_cases h2 : s.role = .Settled ∧ t.role = .Settled ∧ s.rank = t.rank
    · simp only [h2]; exact ⟨le_refl _, le_refl _⟩
    · simp only [h2, ite_false]
      by_cases h_ab : s.role = .Settled ∧ t.role = .Unsettled ∧
         s.children < 2 ∧ 2 * s.rank.val + s.children + 1 < n
      · simp only [dif_pos h_ab]; exact ⟨hs_rc, ht_rc⟩
      · simp only [dif_neg h_ab]
        by_cases h_ba : t.role = .Settled ∧ s.role = .Unsettled ∧
           t.children < 2 ∧ 2 * t.rank.val + t.children + 1 < n
        · simp only [dif_pos h_ba]; exact ⟨hs_rc, ht_rc⟩
        · simp only [dif_neg h_ba]
          constructor <;> (split_ifs <;> simp_all <;> omega)

/-- The full transition preserves rc ≤ Rmax.
    TARGETED SORRY: phase4 branch when both agents become Settled. -/
private theorem transitionPEM_pair_rc_le_Rmax
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (s t : AgentState n) (x₀ x₁ : Opinion)
    (hs_rc : s.resetcount ≤ Rmax) (ht_rc : t.resetcount ≤ Rmax) :
    (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) ((s, x₀), (t, x₁))).1.resetcount ≤ Rmax ∧
    (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) ((s, x₀), (t, x₁))).2.resetcount ≤ Rmax := by
  rw [transitionPEM_eq]
  have h_struct := transitionPEM_prePhase4_structural
    (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := s) (s₁ := t) (x₀ := x₀) (x₁ := x₁)
  set pre := transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn) s t x₀ x₁
  have h_rd := rankDeltaOSSR_rc_le_Rmax (Emax := Emax) (Dmax := Dmax) (hn := hn) s t hs_rc ht_rc
  obtain ⟨_, _, _, _, hrc0_eq, _, _, _, _, _, hrc1_eq, _⟩ := h_struct
  have hpre0 : pre.1.resetcount ≤ Rmax := hrc0_eq ▸ h_rd.1
  have hpre1 : pre.2.resetcount ≤ Rmax := hrc1_eq ▸ h_rd.2
  by_cases h : pre.1.role = .Settled ∧ pre.2.role = .Settled
  · -- phase4 fires: swap/decide preserve rc, propagate sets rc = Rmax or preserves
    sorry
  · rw [transitionPEM_phase4_of_not_both_settled h]
    exact ⟨hpre0, hpre1⟩

set_option maxHeartbeats 400000 in
/-- Step-level rc bound. -/
private theorem step_rc_le_Rmax
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    (hBound : ∀ w : Fin n, (C w).1.resetcount ≤ Rmax)
    (u v w : Fin n) :
    (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) u v w).1.resetcount ≤ Rmax := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn with hP
  by_cases huv : u = v
  · subst huv; simp only [Config.step, ite_true]; exact hBound w
  · simp only [Config.step, if_neg huv]
    by_cases hwu : w = u
    · subst hwu; simp only [ite_true]
      exact (transitionPEM_pair_rc_le_Rmax (C w).1 (C v).1 (C w).2 (C v).2
        (hBound w) (hBound v)).1
    · simp only [if_neg hwu]
      by_cases hwv : w = v
      · subst hwv; simp only [ite_true]
        exact (transitionPEM_pair_rc_le_Rmax (C u).1 (C w).1 (C u).2 (C w).2
          (hBound u) (hBound w)).2
      · simp only [if_neg hwv]; exact hBound w

/-! ### Answer preservation -/

set_option maxHeartbeats 400000 in
/-- Step-level answer preservation.
    TARGETED SORRY: interacting agents' answers may change through
    phase4_decide or transitionPEM_prePhase4 answer clearing. -/
private theorem step_answer_preservation
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    (hAllM : ∀ w : Fin n, (C w).1.answer = majorityAnswer C)
    (u v w : Fin n) :
    (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) u v w).1.answer =
      majorityAnswer C := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn with hP
  by_cases huv : u = v
  · subst huv; simp only [Config.step, ite_true]; exact hAllM w
  · simp only [Config.step, if_neg huv]
    by_cases hwu : w = u
    · subst hwu; simp only [ite_true]; sorry
    · simp only [if_neg hwu]
      by_cases hwv : w = v
      · subst hwv; simp only [ite_true]; sorry
      · simp only [if_neg hwv]; exact hAllM w

theorem recoveryInv_step
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    (hInv : RecoveryInv Rmax C)
    (i j : Fin n) :
    RecoveryInv Rmax (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  have hmaj : majorityAnswer (C.step P i j) = majorityAnswer C :=
    majorityAnswer_step_eq C i j
  exact ⟨fun w => hmaj ▸ step_answer_preservation C hInv.1 i j w,
         fun w => step_rc_le_Rmax hInv.2 i j w⟩

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
    (hAllCorrect : ∀ w : Fin n, (D w).1.answer = majorityAnswer D)
    (hBounded : ∀ w : Fin n, (D w).1.resetcount ≤ Rmax) :
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
  have hPhase1 : Probability.expectedHittingTime P hn2 D Mid ≤
      ((Rmax * n * n : ℕ) : ENNReal) := by
    have hInv0 : RecoveryInv Rmax D := ⟨hAllCorrect, hBounded⟩
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
    calc Probability.expectedHittingTime P hn2 D Mid
        ≤ ↑(maxRC D) * ((n * (n - 1) : ℕ) : ENNReal) := hDescent
      _ ≤ ((Rmax * n * n : ℕ) : ENNReal) := by
          norm_cast
          calc maxRC D * (n * (n - 1))
              ≤ Rmax * (n * (n - 1)) := Nat.mul_le_mul_right _ hmaxRC_le
            _ ≤ Rmax * (n * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le n 1))
            _ = Rmax * n * n := by ring
  have hPhase2 : ∀ C, Mid C →
      Probability.expectedHittingTime P hn2 C IsConsensusConfig ≤
        ((Rmax * n * n : ℕ) : ENNReal) := by
    intro C hC
    rcases hC with hCons | ⟨hInv, hMaxRC0⟩
    · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 C IsConsensusConfig hCons]
      exact bot_le
    · exact maxRC_zero_to_consensus hn4 hn0 hRmax hDmax C hInv hMaxRC0
  calc Probability.expectedHittingTime P hn2 D IsConsensusConfig
      ≤ ((Rmax * n * n : ℕ) : ENNReal) + ((Rmax * n * n : ℕ) : ENNReal) :=
        Probability.expectedHittingTime_add_le P hn2 D Mid IsConsensusConfig
          _ _ hPhase1 hPhase2 hMidGoal
    _ = ((2 * Rmax * n * n : ℕ) : ENNReal) := by push_cast; ring

end SSEM
