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
  by_cases hr : (C w).1.role = .Resetting
  · simp [hr, h w hr]
  · simp [hr]

structure StrongRecoveryInv (Rmax : ℕ) (C : Config (AgentState n) Opinion n) : Prop where
  allResetting : ∀ w : Fin n, (C w).1.role = .Resetting
  allCorrect : ∀ w : Fin n, (C w).1.answer = majorityAnswer C
  rcBounded : ∀ w : Fin n, (C w).1.resetcount ≤ Rmax

def Phase1Goal (Rmax : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  IsConsensusConfig C ∨ (StrongRecoveryInv Rmax C ∧ maxRC C = 0) ∨
  (∃ w : Fin n, (C w).1.role ≠ .Resetting)

/-! ### Auxiliary lemmas -/

private theorem resetOSSR_rc_preserved {Emax : ℕ} {hn : 0 < n} (s : AgentState n) :
    (resetOSSR Emax hn s).resetcount = s.resetcount := by
  unfold resetOSSR; cases s.leader <;> rfl

private theorem processAgent_rc_preserved {Emax Dmax : ℕ} {hn : 0 < n}
    (s : AgentState n) (oldRc : ℕ) (pr : Bool) :
    (processAgent Emax Dmax hn s oldRc pr).resetcount = s.resetcount := by
  unfold processAgent
  by_cases h1 : s.role = .Resetting ∧ s.resetcount = 0
  · rw [if_pos h1]
    by_cases h2 : 0 < oldRc
    · rw [if_pos h2]; simp only []
      by_cases h3 : (Dmax = 0 ∨ (!pr) = true)
      · rw [if_pos h3, resetOSSR_rc_preserved]
      · rw [if_neg h3]
    · rw [if_neg h2]; simp only []
      by_cases h3 : (s.delaytimer - 1 = 0 ∨ (!pr) = true)
      · rw [if_pos h3, resetOSSR_rc_preserved]
      · rw [if_neg h3]
  · rw [if_neg h1]

private theorem propagateReset_rc_of_both_resetting {Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} (hs : s.role = .Resetting) (ht : t.role = .Resetting) :
    (propagateReset Emax Dmax hn s t).1.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) ∧
    (propagateReset Emax Dmax hn s t).2.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) := by
  unfold propagateReset
  dsimp only []
  simp only [hs, ht,
    show ¬(t.role ≠ .Resetting) from not_not.mpr ht,
    show ¬(s.role ≠ .Resetting) from not_not.mpr hs,
    show ¬(s.role = .Resetting ∧ 0 < s.resetcount ∧ t.role ≠ .Resetting) from
      fun ⟨_, _, h⟩ => h ht,
    show ¬(t.role = .Resetting ∧ 0 < t.resetcount ∧ s.role ≠ .Resetting) from
      fun ⟨_, _, h⟩ => h hs,
    show ¬(Role.Resetting ≠ .Resetting) from not_not.mpr rfl,
    show (Role.Resetting == Role.Resetting) = true from rfl,
    and_true, and_false, ite_false, and_self, ite_true, true_and, not_true]
  set M := Nat.max (s.resetcount - 1) (t.resetcount - 1)
  constructor
  · exact processAgent_rc_preserved _ _ _
  · exact processAgent_rc_preserved _ _ _

private theorem rankDeltaOSSR_rc_of_both_resetting
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} (hs : s.role = .Resetting) (ht : t.role = .Resetting) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) := by
  unfold rankDeltaOSSR
  simp only [hs, true_or, ite_true]
  have hpr := propagateReset_rc_of_both_resetting (Emax := Emax) (Dmax := Dmax) (hn := hn) hs ht
  constructor
  · exact hpr.1
  · split_ifs <;> exact hpr.2

private theorem rc_max_sub_le_max (a b : ℕ) :
    Nat.max (a - 1) (b - 1) ≤ Nat.max a b := by
  simp only [Nat.max]
  exact max_le_max (Nat.sub_le a 1) (Nat.sub_le b 1)

private theorem step_bystander_eq' {P : Protocol (AgentState n) Opinion Output}
    {C : Config (AgentState n) Opinion n}
    {i j w : Fin n} (hij : i ≠ j) (hwi : w ≠ i) (hwj : w ≠ j) :
    (C.step P i j w) = C w := by
  simp [Config.step, hij, hwi, hwj]

/-- Under StrongRecoveryInv, if the step output at position i is Resetting,
then rankDeltaOSSR did NOT produce both Settled.
Proof: if rd both Settled, prePhase4 both Settled (structural), Phase 4 fires.
transitionPEM_phase4_settled_pair: output is (not-Resetting, not-Resetting) OR
(both Resetting with rc=Rmax). Case 1 contradicts hi_res'. Case 2 requires
phase4_propagate reset, which needs answer mismatch after decide. But for n ≥ 2
(guaranteed by i ≠ j), resetOSSR gives rank 0, and phase4_decide is identity
on rank-0 pairs (no median condition fires). So answers stay uniform.
And phase4_propagate on rank-0 pair either doesn't match ceilHalf condition
(n ≥ 3) or has freshly-initialized timer > 0 (n = 2). Either way, no reset. -/
private theorem rd_not_both_settled_of_step_resetting
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {i j : Fin n} (hij : i ≠ j)
    (hInv : StrongRecoveryInv Rmax C)
    (hi_res' : (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j i).1.role = .Resetting) :
    ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).1.role = .Settled ∧
       (rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).2.role = .Settled) := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  set rd := rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)
  have h_struct := transitionPEM_prePhase4_structural
    (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (C i).1) (s₁ := (C j).1) (x₀ := (C i).2) (x₁ := (C j).2)
  intro ⟨hrd_s0, hrd_s1⟩
  set pre := transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C i).1 (C j).1 (C i).2 (C j).2
  have h_pre_s0 : pre.1.role = .Settled := by rw [h_struct.1]; exact hrd_s0
  have h_pre_s1 : pre.2.role = .Settled := by rw [h_struct.2.2.2.2.2.2.1]; exact hrd_s1
  have h_phase4 := transitionPEM_phase4_settled_pair (n := n) (Rmax := Rmax)
    (a₀ := pre.1) (a₁ := pre.2) (x₀ := (C i).2) (x₁ := (C j).2) h_pre_s0 h_pre_s1
  have h_step_i : (C.step P i j i).1 = (P.δ (C i, C j)).1 :=
    Config.step_fst_state P C hij
  have h_delta_eq : P.δ (C i, C j) = transitionPEM_phase4 n Rmax pre (C i).2 (C j).2 := rfl
  rw [h_step_i, h_delta_eq] at hi_res'
  rcases h_phase4 with ⟨hno_res_0, _⟩ | ⟨⟨_, _, _⟩, _⟩
  · exact hno_res_0 hi_res'
  · sorry -- Case 2 impossible: Phase 4 propagate-reset can't fire on rank-0 pair

-- Same as above but for position j (symmetric)
private theorem rd_not_both_settled_of_step_resetting_snd
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {i j : Fin n} (hij : i ≠ j)
    (hInv : StrongRecoveryInv Rmax C)
    (hj_res' : (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j j).1.role = .Resetting) :
    ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).1.role = .Settled ∧
       (rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).2.role = .Settled) := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  set rd := rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)
  have h_struct := transitionPEM_prePhase4_structural
    (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (C i).1) (s₁ := (C j).1) (x₀ := (C i).2) (x₁ := (C j).2)
  intro ⟨hrd_s0, hrd_s1⟩
  set pre := transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C i).1 (C j).1 (C i).2 (C j).2
  have h_pre_s0 : pre.1.role = .Settled := by rw [h_struct.1]; exact hrd_s0
  have h_pre_s1 : pre.2.role = .Settled := by rw [h_struct.2.2.2.2.2.2.1]; exact hrd_s1
  have h_phase4 := transitionPEM_phase4_settled_pair (n := n) (Rmax := Rmax)
    (a₀ := pre.1) (a₁ := pre.2) (x₀ := (C i).2) (x₁ := (C j).2) h_pre_s0 h_pre_s1
  have h_step_j : (C.step P i j j).1 = (P.δ (C i, C j)).2 :=
    Config.step_snd_state P C hij (Ne.symm hij)
  have h_delta_eq : P.δ (C i, C j) = transitionPEM_phase4 n Rmax pre (C i).2 (C j).2 := rfl
  rw [h_step_j, h_delta_eq] at hj_res'
  rcases h_phase4 with ⟨_, hno_res_1⟩ | ⟨_, ⟨_, _, _⟩⟩
  · exact hno_res_1 hj_res'
  · sorry -- Same Phase 4 trace argument as above

/-! ### Main theorems -/

set_option maxHeartbeats 1600000 in
theorem strongRecoveryInv_step
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    (hInv : StrongRecoveryInv Rmax C) (i j : Fin n) :
    StrongRecoveryInv Rmax (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) ∨
    Phase1Goal Rmax (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn with hP
  set C' := C.step P i j with hC'
  by_cases hij : i = j
  · left
    have : C' = C := by simp [C', Config.step, hij]
    rw [this]; exact hInv
  · by_cases h_all_res : ∀ w : Fin n, (C' w).1.role = .Resetting
    · left
      have hi_res := hInv.allResetting i
      have hj_res := hInv.allResetting j
      have h_not_both_settled_rd :=
        rd_not_both_settled_of_step_resetting hij hInv (h_all_res i)
      have h_struct := transitionPEM_prePhase4_structural
        (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        (s₀ := (C i).1) (s₁ := (C j).1) (x₀ := (C i).2) (x₁ := (C j).2)
      have h_not_both_settled_pre :
          ¬ ((transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
                (C i).1 (C j).1 (C i).2 (C j).2).1.role = .Settled ∧
              (transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
                (C i).1 (C j).1 (C i).2 (C j).2).2.role = .Settled) := by
        rw [h_struct.1, h_struct.2.2.2.2.2.2.1]; exact h_not_both_settled_rd
      have hm := majorityAnswer_ne_phi C
      have h_no_entry_fst :
          ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).1.role = .Resetting ∧
             (C i).1.role ≠ .Resetting) :=
        fun ⟨_, h⟩ => h hi_res
      have h_no_entry_snd :
          ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).2.role = .Resetting ∧
             (C j).1.role ≠ .Resetting) :=
        fun ⟨_, h⟩ => h hj_res
      have h_ans_all : ∀ w : Fin n, (C' w).1.answer = majorityAnswer C :=
        step_preserves_uniform_answer_of_no_reset_entry
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hm hij (hInv.allCorrect) h_no_entry_fst h_no_entry_snd h_not_both_settled_rd
      have h_rd_rc := rankDeltaOSSR_rc_of_both_resetting hi_res hj_res
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      constructor
      · exact h_all_res
      · rw [show majorityAnswer C' = majorityAnswer C from majorityAnswer_step_eq C i j]
        exact h_ans_all
      · intro w
        by_cases hwi : w = i
        · subst hwi; sorry







        · by_cases hwj : w = j
          · subst hwj; sorry








          · rw [show (C' w) = C w from step_bystander_eq' hij hwi hwj]
            exact hInv.rcBounded w
    · right; right; right
      push_neg at h_all_res; exact h_all_res

set_option maxHeartbeats 1600000 in
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

/-- Phase 2: from Phase1Goal to consensus. -/
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
  have hPhase1 : Probability.expectedHittingTime P hn2 D (Phase1Goal Rmax) ≤
      ((Rmax * n * n : ℕ) : ENNReal) := by
    have hmaxRC_le : maxRC D ≤ Rmax := maxRC_le_of_all_le (fun w _ => hBounded w)
    have hDescent := Probability.expectedHittingTime_le_of_deterministic_descent
      P hn2 D (Phase1Goal Rmax) (StrongRecoveryInv Rmax) maxRC hInv0
      (fun C hInv hphi => Or.inr (Or.inl ⟨hInv, hphi⟩))
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
  have hPhase2 : ∀ C, Phase1Goal Rmax C →
      Probability.expectedHittingTime P hn2 C IsConsensusConfig ≤
        ((Rmax * n * n : ℕ) : ENNReal) :=
    fun C hC => phase1Goal_to_consensus hn4 hn0 hRmax hDmax C hC
  calc Probability.expectedHittingTime P hn2 D IsConsensusConfig
      ≤ ((Rmax * n * n : ℕ) : ENNReal) + ((Rmax * n * n : ℕ) : ENNReal) :=
        Probability.expectedHittingTime_add_le P hn2 D (Phase1Goal Rmax) IsConsensusConfig
          _ _ hPhase1 hPhase2 (fun C h => Or.inl h)
    _ = ((2 * Rmax * n * n : ℕ) : ENNReal) := by push_cast; ring

end SSEM
