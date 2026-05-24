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
    exact (hrank u).symm.trans (hEq.trans (hrank v))
  · intro w
    rw [step_input_preserved P D i j w, hrank w]
    rw [show nAOf (D.step P i j) = nAOf D from by
      simpa [P] using
        (nAOf_step_eq
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j)]
    exact hS.input_rank w

private theorem majorityAnswer_eq_outT_of_even_lower_upper_disagree
    {n : ℕ} {C : Config (AgentState n) Opinion n}
    (hS : InSswap C) {μ ν : Fin n}
    (hμR : (C μ).1.rank.val + 1 = n / 2)
    (hνR : (C ν).1.rank.val + 1 = n / 2 + 1)
    (hpar : n % 2 = 0) (hdis : (C μ).2 ≠ (C ν).2) :
    majorityAnswer C = .outT := by
  have h_sum := nAOf_add_nBOf C
  have hnA : nAOf C = n / 2 := by
    rcases hxμ : (C μ).2 with _ | _
    · have h1 : (C μ).1.rank.val < nAOf C := (hS.input_rank μ).mp hxμ
      have hxν : (C ν).2 = Opinion.B := by
        cases hxν' : (C ν).2 with
        | A => exfalso; exact hdis (by rw [hxμ, hxν'])
        | B => rfl
      have h2 : ¬ ((C ν).1.rank.val < nAOf C) := by
        intro hlt
        have := (hS.input_rank ν).mpr hlt
        rw [hxν] at this
        cases this
      omega
    · have h1 : ¬ ((C μ).1.rank.val < nAOf C) := by
        intro hlt
        have := (hS.input_rank μ).mpr hlt
        rw [hxμ] at this
        cases this
      have hxν : (C ν).2 = Opinion.A := by
        cases hxν' : (C ν).2 with
        | A => rfl
        | B => exfalso; exact hdis (by rw [hxμ, hxν'])
      have h2 : (C ν).1.rank.val < nAOf C := (hS.input_rank ν).mp hxν
      omega
  have hnB : nBOf C = n / 2 := by omega
  exact majorityAnswer_eq_outT_of_tie (C := C) (by omega)

private theorem nA_ne_nB_of_even_lower_upper_agree
    {n : ℕ} {C : Config (AgentState n) Opinion n}
    (hS : InSswap C) {μ ν : Fin n}
    (hμR : (C μ).1.rank.val + 1 = n / 2)
    (hνR : (C ν).1.rank.val + 1 = n / 2 + 1)
    (hpar : n % 2 = 0) (hagree : (C μ).2 = (C ν).2) :
    nAOf C ≠ nBOf C := by
  intro htie
  have h_sum := nAOf_add_nBOf C
  have hnA : nAOf C = n / 2 := by omega
  rcases hxμ : (C μ).2 with _ | _
  · have hxν : (C ν).2 = Opinion.A := by
      rw [← hagree]
      exact hxμ
    have hν_lt : (C ν).1.rank.val < nAOf C := (hS.input_rank ν).mp hxν
    omega
  · have hμ_lt : (C μ).1.rank.val < nAOf C := by omega
    have hxμA : (C μ).2 = Opinion.A := (hS.input_rank μ).mpr hμ_lt
    rw [hxμ] at hxμA
    cases hxμA

private theorem phase4_decide_fst_median_answer_correct
    {n : ℕ} {D : Config (AgentState n) Opinion n}
    (hn4 : 4 ≤ n) (hS : InSswap D) (hM : MedianAnswerCorrect D)
    {i j : Fin n}
    (hi_med : (D i).1.rank.val + 1 = ceilHalf n) :
    (phase4_decide n (D i).1 (D j).1 (D i).2 (D j).2).1.answer =
      majorityAnswer D := by
  classical
  by_cases hpar : n % 2 = 0
  · have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
    have hi_lower : (D i).1.rank.val + 1 = n / 2 := by
      rw [← hceil]
      exact hi_med
    unfold phase4_decide
    simp only [hpar, if_true]
    by_cases hp₁ :
        (D i).1.rank.val + 1 = n / 2 ∧
          (D j).1.rank.val + 1 = n / 2 + 1
    · simp only [hp₁, if_true]
      by_cases hagree : (D i).2 = (D j).2
      · simp only [hagree, if_true]
        exact opinionToAnswer_upper_median_eq_majorityAnswer_even
          hS hp₁.2 hpar
          (nA_ne_nB_of_even_lower_upper_agree hS hp₁.1 hp₁.2 hpar hagree)
      · simp only [hagree, if_false]
        exact (majorityAnswer_eq_outT_of_even_lower_upper_disagree
          hS hp₁.1 hp₁.2 hpar hagree).symm
    · simp only [hp₁, if_false]
      have hp₂_false :
          ¬ ((D j).1.rank.val + 1 = n / 2 ∧
            (D i).1.rank.val + 1 = n / 2 + 1) := by
        intro hp₂
        omega
      simp only [hp₂_false, if_false]
      exact hM i hi_med
  · have hOdd := opinionToAnswer_median_eq_majorityAnswer_odd hS hi_med hpar
    unfold phase4_decide
    simp only [hpar, if_false, hi_med, if_true]
    exact hOdd

private theorem phase4_decide_snd_median_answer_correct
    {n : ℕ} {D : Config (AgentState n) Opinion n}
    (hn4 : 4 ≤ n) (hS : InSswap D) (hM : MedianAnswerCorrect D)
    {i j : Fin n}
    (hj_med : (D j).1.rank.val + 1 = ceilHalf n) :
    (phase4_decide n (D i).1 (D j).1 (D i).2 (D j).2).2.answer =
      majorityAnswer D := by
  classical
  by_cases hpar : n % 2 = 0
  · have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
    have hj_lower : (D j).1.rank.val + 1 = n / 2 := by
      rw [← hceil]
      exact hj_med
    unfold phase4_decide
    simp only [hpar, if_true]
    have hp₁_false :
        ¬ ((D i).1.rank.val + 1 = n / 2 ∧
          (D j).1.rank.val + 1 = n / 2 + 1) := by
      intro hp₁
      omega
    simp only [hp₁_false, if_false]
    by_cases hp₂ :
        (D j).1.rank.val + 1 = n / 2 ∧
          (D i).1.rank.val + 1 = n / 2 + 1
    · simp only [hp₂, if_true]
      by_cases hagree : (D j).2 = (D i).2
      · simp only [hagree, if_true]
        exact opinionToAnswer_upper_median_eq_majorityAnswer_even
          hS hp₂.2 hpar
          (nA_ne_nB_of_even_lower_upper_agree hS hp₂.1 hp₂.2 hpar hagree)
      · simp only [hagree, if_false]
        exact (majorityAnswer_eq_outT_of_even_lower_upper_disagree
          hS hp₂.1 hp₂.2 hpar hagree).symm
    · simp only [hp₂, if_false]
      exact hM j hj_med
  · have hOdd := opinionToAnswer_median_eq_majorityAnswer_odd hS hj_med hpar
    unfold phase4_decide
    simp only [hpar, if_false, hj_med, if_true]
    exact hOdd

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
    change InSswap (D.step P i i)
    simpa [Config.step] using hS
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
  have hsnd := Config.step_snd_state P D hij (Ne.symm hij)
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
      let dec :=
        phase4_decide n (D i).1 (D j).1 (D i).2 (D j).2
      have hnot_pair_settled :
          ¬ ((transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.role = .Settled ∧
             (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).2.role = .Settled) := by
        intro hsettled
        apply hnot_settled
        constructor
        · dsimp [C', P]
          rw [congrArg AgentState.role hfst]
          exact hsettled.1
        · dsimp [C', P]
          rw [congrArg AgentState.role hsnd]
          exact hsettled.2
      have htrans :
          transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
              (D i, D j) =
            phase4_propagate n Rmax dec.1 dec.2 := by
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap
        simp only [hRD, hsi, hsj, ne_eq,
          role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
          false_and, and_false, if_false, and_self, if_true, h_no_swap, dec]
      have hdec_role_i : dec.1.role = .Settled := by
        dsimp [dec]
        unfold phase4_decide
        split_ifs <;> simp [hsi]
      have hdec_role_j : dec.2.role = .Settled := by
        dsimp [dec]
        unfold phase4_decide
        split_ifs <;> simp [hsj]
      have hdec_rank_i : dec.1.rank = (D i).1.rank := by
        dsimp [dec]
        unfold phase4_decide
        split_ifs <;> rfl
      have hdec_rank_j : dec.2.rank = (D j).1.rank := by
        dsimp [dec]
        unfold phase4_decide
        split_ifs <;> rfl
      have hdec_ans_i :
          dec.1.rank.val + 1 = ceilHalf n →
            dec.1.answer = majorityAnswer D := by
        intro hmed
        have hi_med : (D i).1.rank.val + 1 = ceilHalf n := by
          simpa [hdec_rank_i] using hmed
        simpa [dec] using
          (phase4_decide_fst_median_answer_correct
            (D := D) hn4 hS hM (i := i) (j := j) hi_med)
      have hdec_ans_j :
          dec.2.rank.val + 1 = ceilHalf n →
            dec.2.answer = majorityAnswer D := by
        intro hmed
        have hj_med : (D j).1.rank.val + 1 = ceilHalf n := by
          simpa [hdec_rank_j] using hmed
        simpa [dec] using
          (phase4_decide_snd_median_answer_correct
            (D := D) hn4 hS hM (i := i) (j := j) hj_med)
      have hnot_prop_settled :
          ¬ ((phase4_propagate n Rmax dec.1 dec.2).1.role = .Settled ∧
             (phase4_propagate n Rmax dec.1 dec.2).2.role = .Settled) := by
        intro hsettled
        exact hnot_pair_settled (by simpa [htrans] using hsettled)
      rw [htrans]
      unfold phase4_propagate
      by_cases hi_med : dec.1.rank.val + 1 = ceilHalf n
      · by_cases hj_max : dec.2.rank.val + 1 = n
        · by_cases hreset :
            ({dec.1 with timer := dec.1.timer - 1} : AgentState n).timer = 0 ∧
              ({dec.1 with timer := dec.1.timer - 1} : AgentState n).answer ≠
                dec.2.answer
          · have hAns := hdec_ans_i (by simpa [hdec_rank_i] using hi_med)
            have hNe : majorityAnswer D ≠ dec.2.answer := by
              intro hEq
              exact hreset.2 (by rw [hAns, hEq])
            simp [hi_med, hj_max, hreset, hAns, hNe]
          · exfalso
            apply hnot_prop_settled
            simp [phase4_propagate, hi_med, hj_max, hreset, hdec_role_i,
              hdec_role_j]
        · by_cases hreset :
            dec.1.timer = 0 ∧ dec.1.answer ≠ dec.2.answer
          · have hAns := hdec_ans_i hi_med
            have hNe : majorityAnswer D ≠ dec.2.answer := by
              intro hEq
              exact hreset.2 (by rw [hAns, hEq])
            simp [hi_med, hj_max, hreset, hAns, hNe]
          · exfalso
            apply hnot_prop_settled
            simp [phase4_propagate, hi_med, hj_max, hreset, hdec_role_i,
              hdec_role_j]
      · by_cases hj_med : dec.2.rank.val + 1 = ceilHalf n
        · by_cases hi_max : dec.1.rank.val + 1 = n
          · by_cases hreset :
              ({dec.2 with timer := dec.2.timer - 1} : AgentState n).timer = 0 ∧
                ({dec.2 with timer := dec.2.timer - 1} : AgentState n).answer ≠
                  dec.1.answer
            · have hAns := hdec_ans_j (by simpa [hdec_rank_j] using hj_med)
              have hNe : majorityAnswer D ≠ dec.1.answer := by
                intro hEq
                exact hreset.2 (by rw [hAns, hEq])
              have hn_ne_ceil : ¬ n = ceilHalf n := by
                intro hEq
                exact hi_med (hi_max.trans hEq)
              simp [hi_med, hj_med, hi_max, hreset, hAns, hNe, hn_ne_ceil]
            · exfalso
              apply hnot_prop_settled
              have hn_ne_ceil : ¬ n = ceilHalf n := by
                intro hEq
                exact hi_med (hi_max.trans hEq)
              simp [phase4_propagate, hi_med, hj_med, hi_max, hreset,
                hdec_role_i, hdec_role_j, hn_ne_ceil]
          · by_cases hreset :
              dec.2.timer = 0 ∧ dec.2.answer ≠ dec.1.answer
            · have hAns := hdec_ans_j hj_med
              have hNe : majorityAnswer D ≠ dec.1.answer := by
                intro hEq
                exact hreset.2 (by rw [hAns, hEq])
              simp [hi_med, hj_med, hi_max, hreset, hAns, hNe]
            · exfalso
              apply hnot_prop_settled
              simp [phase4_propagate, hi_med, hj_med, hi_max, hreset,
                hdec_role_i, hdec_role_j]
        · exfalso
          apply hnot_prop_settled
          simp [phase4_propagate, hi_med, hj_med, hdec_role_i, hdec_role_j]
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
        refine ⟨?_, hpair.2.2.2.2.2.2.2⟩
        rw [hpair.2.2.2.2.2.1]
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
