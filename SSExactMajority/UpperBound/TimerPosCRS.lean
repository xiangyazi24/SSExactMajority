import SSExactMajority.UpperBound.Time

namespace SSEM

private theorem inSswap_step_of_scheduled_roles
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (hi : (D.step
      (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)) i j i).1.role =
        .Settled)
    (hj : (D.step
      (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)) i j j).1.role =
        .Settled) :
    InSswap
      (D.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)) i j) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
  have hrank : ∀ w : Fin n, (D.step P i j w).1.rank = (D w).1.rank := by
    intro w
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      (step_rank_preserved_of_InSswap
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hS
        (i := i) (j := j) w)
  refine
    { toInSrank :=
        { allSettled := ?_
          ranks_inj := ?_ }
      input_rank := ?_ }
  · intro w
    by_cases hwi : w = i
    · subst w
      simpa [P] using hi
    · by_cases hwj : w = j
      · subst w
        simpa [P] using hj
      · have hw : D.step P i j w = D w := by
          unfold Config.step
          by_cases hij : i = j
          · simp [P, hij]
          · simp [P, hij, hwi, hwj]
        rw [hw]
        exact hS.allSettled w
  · intro u v hEq
    apply hS.ranks_inj
    rw [← hrank u, ← hrank v]
    exact hEq
  · intro w
    rw [step_input_preserved P D i j w, hrank w]
    rw [show nAOf (D.step P i j) = nAOf D from by
      simpa [P] using
        (nAOf_step_eq
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j)]
    exact hS.input_rank w

set_option maxHeartbeats 64000000 in
theorem crs_of_InSswap_break_with_MedC
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) (hM : MedianAnswerCorrect D)
    {i j : Fin n}
    (hS' : ¬ InSswap (D.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)) i j)) :
    CorrectResetSeed (D.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)) i j) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
  set C' : Config (AgentState n) Opinion n := D.step P i j
  by_cases hij : i = j
  · subst j
    exfalso
    apply hS'
    simpa [P, Config.step] using hS
  have hnot_settled :
      ¬ ((C' i).1.role = .Settled ∧ (C' j).1.role = .Settled) := by
    intro hroles
    apply hS'
    simpa [C', P] using
      (inSswap_step_of_scheduled_roles
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hS
        (i := i) (j := j) hroles.1 hroles.2)
  have hsi : (D i).1.role = .Settled := hS.allSettled i
  have hsj : (D j).1.role = .Settled := hS.allSettled j
  have hrij : (D i).1.rank ≠ (D j).1.rank :=
    fun h => hij (hS.ranks_inj h)
  have hRD : rankDeltaOSSR Rmax Emax Dmax hn0 ((D i).1, (D j).1) =
      ((D i).1, (D j).1) :=
    rankDeltaOSSR_satisfies_fix
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
      (D i).1 (D j).1 hsi hsj hrij
  have h_no_swap :
      ¬ ((D i).1.rank < (D j).1.rank ∧
        (D i).2 = Opinion.B ∧ (D j).2 = Opinion.A) :=
    hS.swap_condition_false i j
  have hmaj : majorityAnswer C' = majorityAnswer D := by
    simpa [C', P] using
      (majorityAnswer_step_eq
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j)
  have hfst := Config.step_fst_state P D hij
  have hsnd := Config.step_snd_state P D hij hij.symm
  have hpair :
      (C' i).1.role = .Resetting ∧
      (C' i).1.resetcount = Rmax ∧
      (C' i).1.leader = .L ∧
      (C' i).1.answer = majorityAnswer C' ∧
      (C' j).1.role = .Resetting ∧
      (C' j).1.resetcount = Rmax ∧
      (C' j).1.leader = .L ∧
      (C' j).1.answer = majorityAnswer C' := by
    have hpair_pre :
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j)).1.role = .Resetting ∧
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j)).1.resetcount = Rmax ∧
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j)).1.leader = .L ∧
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j)).1.answer = majorityAnswer D ∧
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j)).2.role = .Resetting ∧
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j)).2.resetcount = Rmax ∧
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j)).2.leader = .L ∧
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j)).2.answer = majorityAnswer D := by
      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
        phase4_swap phase4_decide phase4_propagate
      simp only [hRD, hsi, hsj, ne_eq,
        role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
        false_and, and_false, if_false, and_self, if_true, h_no_swap]
      by_cases hpar : n % 2 = 0
      · simp only [hpar, if_true]
        split_ifs with h <;>
          (first
            | exfalso
              apply hnot_settled
              constructor <;>
                dsimp [C', P] <;>
                (first
                  | rw [congrArg AgentState.role hfst]
                    simp_all
                  | rw [congrArg AgentState.role hsnd]
                    simp_all)
            | simp_all [MedianAnswerCorrect, ceilHalf_eq_half_of_even hpar])
      · simp only [hpar, if_false]
        split_ifs with h <;>
          (first
            | exfalso
              apply hnot_settled
              constructor <;>
                dsimp [C', P] <;>
                (first
                  | rw [congrArg AgentState.role hfst]
                    simp_all
                  | rw [congrArg AgentState.role hsnd]
                    simp_all)
            | simp_all [MedianAnswerCorrect,
                opinionToAnswer_median_eq_majorityAnswer_odd hS])
    rcases hpair_pre with
      ⟨hi_role, hi_rc, hi_leader, hi_ans, hj_role, hj_rc, hj_leader, hj_ans⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [C', P]
      rw [congrArg AgentState.role hfst]
      exact hi_role
    · dsimp [C', P]
      rw [congrArg AgentState.resetcount hfst]
      exact hi_rc
    · dsimp [C', P]
      rw [congrArg AgentState.leader hfst]
      exact hi_leader
    · rw [hmaj]
      dsimp [C', P]
      rw [congrArg AgentState.answer hfst]
      exact hi_ans
    · dsimp [C', P]
      rw [congrArg AgentState.role hsnd]
      exact hj_role
    · dsimp [C', P]
      rw [congrArg AgentState.resetcount hsnd]
      exact hj_rc
    · dsimp [C', P]
      rw [congrArg AgentState.leader hsnd]
      exact hj_leader
    · rw [hmaj]
      dsimp [C', P]
      rw [congrArg AgentState.answer hsnd]
      exact hj_ans
  have hN_bound : nonResettingCount C' < Rmax := by
    have hcard_le : nonResettingCount C' ≤ n - 1 := by
      set S := Finset.univ.filter
        (fun w : Fin n => (C' w).1.role ≠ .Resetting) with hSset
      have hsub : S ⊆ Finset.univ.erase i := by
        intro x hx
        have hx_ne : x ≠ i := by
          intro hxi
          subst x
          have hx_not : (C' i).1.role ≠ .Resetting := by
            rw [hSset] at hx
            exact (Finset.mem_filter.mp hx).2
          exact hx_not hpair.1
        exact Finset.mem_erase.mpr ⟨hx_ne, Finset.mem_univ x⟩
      have hle := Finset.card_le_card hsub
      have herase : (Finset.univ.erase i).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
        simp
      unfold nonResettingCount
      rw [← hSset]
      omega
    have hRmax_pos : 0 < Rmax := Nat.lt_of_lt_of_le hn0 hRmax
    omega
  have hRmax_pos : 0 < Rmax := Nat.lt_of_lt_of_le hn0 hRmax
  refine ⟨⟨i, hpair.1, ?_, hpair.2.2.1, hpair.2.2.2.1⟩, ?_⟩
  · rw [hpair.2.1]
    exact hN_bound
  · intro w hw
    by_cases hwi : w = i
    · subst w
      refine ⟨?_, hpair.2.2.2.1⟩
      rw [hpair.2.1]
      exact hRmax_pos
    · by_cases hwj : w = j
      · subst w
        refine ⟨?_, hpair.2.2.2.2.2.2⟩
        rw [hpair.2.2.2.2.1]
        exact hRmax_pos
      · have hOld : C' w = D w := by
          dsimp [C', P]
          simp [Config.step, hij, hwi, hwj]
        have hSettled : (C' w).1.role = .Settled := by
          rw [hOld]
          exact hS.allSettled w
        rw [hSettled] at hw
        cases hw

end SSEM
