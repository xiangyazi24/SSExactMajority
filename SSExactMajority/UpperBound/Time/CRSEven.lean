import SSExactMajority.UpperBound.Time.Bridge

namespace SSEM

open scoped ENNReal

set_option maxHeartbeats 32000000 in
set_option maxHeartbeats 32000000 in
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
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hP_unfold : P = PEMProtocolCoupled n Rmax Emax Dmax hn0 := rfl
  -- Case: i = j makes step a no-op, so InSswap is preserved (contradicts hS').
  by_cases hij : i = j
  · exfalso; apply hS'; subst hij
    have heq : D.step P i i = D := by
      funext w; unfold Config.step; simp only [if_true]
    rw [heq]; exact hS
  -- Strategy: show the step either preserves InSswap or creates CorrectResetSeed.
  -- Since hS' says ¬InSswap, the second alternative must hold.
  suffices h : InSswap (D.step P i j) ∨ CorrectResetSeed (D.step P i j) from
    h.resolve_left hS'
  -- Post-step roles are Settled or Resetting (from Transition.lean).
  have hsi := hS.toInSrank.allSettled i
  have hsj := hS.toInSrank.allSettled j
  have h_fst := Config.step_fst_state P D hij
  have h_snd := Config.step_snd_state P D hij (Ne.symm hij)
  -- Role of i post-step
  have h_role_i : (D.step P i j i).1.role = .Settled ∨
      (D.step P i j i).1.role = .Resetting := by
    have hrij' : (D i).1.rank ≠ (D j).1.rank := fun h => hij (hS.toInSrank.ranks_inj h)
    have hRD' := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij'
    rw [congrArg AgentState.role h_fst]
    have h_bridge : (P.δ (D i, D j)).1.role =
        (transitionPEM_phase4 n Rmax ((D i).1, (D j).1) (D i).2 (D j).2).1.role := by
      simp only [P, hP_unfold, PEMProtocolCoupled, PEMProtocol, protocolPEM,
        transitionPEM, transitionPEM_prePhase4, hRD', hsi, hsj, and_self, ite_true,
        ne_eq, role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
        false_and, and_false, if_false, if_true, ite_self]
    rw [h_bridge]
    exact (transitionPEM_phase4_role_settled_or_resetting hsi hsj).1
  -- Role of j post-step
  have h_role_j : (D.step P i j j).1.role = .Settled ∨
      (D.step P i j j).1.role = .Resetting := by
    have hrij' : (D i).1.rank ≠ (D j).1.rank := fun h => hij (hS.toInSrank.ranks_inj h)
    have hRD' := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij'
    rw [congrArg AgentState.role h_snd]
    have h_bridge : (P.δ (D i, D j)).2.role =
        (transitionPEM_phase4 n Rmax ((D i).1, (D j).1) (D i).2 (D j).2).2.role := by
      simp only [P, hP_unfold, PEMProtocolCoupled, PEMProtocol, protocolPEM,
        transitionPEM, transitionPEM_prePhase4, hRD', hsi, hsj, and_self, ite_true,
        ne_eq, role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
        false_and, and_false, if_false, if_true, ite_self]
    rw [h_bridge]
    exact (transitionPEM_phase4_role_settled_or_resetting hsi hsj).2
  -- If both stay Settled → InSswap preserved
  by_cases hi_settled : (D.step P i j i).1.role = .Settled
  · by_cases hj_settled : (D.step P i j j).1.role = .Settled
    · -- Both Settled → InSswap preserved
      left
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · -- allSettled
        intro w
        by_cases hwi : w = i
        · rw [hwi]; exact hi_settled
        · by_cases hwj : w = j
          · rw [hwj]; exact hj_settled
          · rw [show (D.step P i j w) = D w from by
                unfold Config.step; simp [hij, hwi, hwj]]
            exact hS.toInSrank.allSettled w
      · -- ranks_inj
        intro w1 w2 heq
        simp only [hP_unfold, step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) hn0 hS] at heq
        exact hS.toInSrank.ranks_inj heq
      · -- input_rank
        intro w
        have h_inp : (D.step P i j w).2 = (D w).2 := by
          unfold Config.step
          by_cases hwi : w = i
          · rw [hwi]; simp [hij]
          · by_cases hwj : w = j
            · rw [hwj]; simp [hij, Ne.symm hij]
            · simp [hij, hwi, hwj]
        have h_rank : (D.step P i j w).1.rank = (D w).1.rank :=
          step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
            (Dmax := Dmax) hn0 hS w
        have h_nA : nAOf (D.step P i j) = nAOf D := by
          unfold nAOf Config.agentsWithInput Config.inputOf
          congr 1; ext w
          simp only [Finset.mem_filter, h_inp]
        rw [h_inp, h_rank, h_nA]
        exact hS.input_rank w
    · -- j Resetting but i Settled: impossible (propagate sets both or neither).
      -- Derive False by unfolding transitionPEM and showing role symmetry.
      exfalso
      have hj_res : (D.step P i j j).1.role = .Resetting :=
        h_role_j.resolve_left hj_settled
      have h2_res : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
          (D i, D j)).2.role = .Resetting := by
        rw [← congrArg AgentState.role h_snd]; exact hj_res
      have h1_set : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
          (D i, D j)).1.role = .Settled := by
        rw [← congrArg AgentState.role h_fst]; exact hi_settled
      have hrij : (D i).1.rank ≠ (D j).1.rank :=
        fun h => hij (hS.toInSrank.ranks_inj h)
      have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij
      have h_no_swap := hS.swap_condition_false i j
      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
        phase4_swap phase4_decide phase4_propagate at h2_res h1_set
      simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
        not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
        and_self, if_true, h_no_swap] at h2_res h1_set
      -- After simp, the if-then-else structure of phase4_propagate is exposed.
      -- In all branches, .1.role and .2.role are equal (both Settled or both Resetting).
      -- So h1_set (= Settled) and h2_res (= Resetting) contradict.
      by_cases hpar : n % 2 = 0
      · simp only [hpar, if_true] at h2_res h1_set
        split_ifs at h2_res h1_set <;> simp_all
      · simp only [hpar, if_false] at h2_res h1_set
        split_ifs at h2_res h1_set <;> simp_all
  · -- i became Resetting → by same symmetry, j also Resetting.
    -- Need: both Resetting → CorrectResetSeed.
    have hi_res : (D.step P i j i).1.role = .Resetting :=
      h_role_i.resolve_left hi_settled
    have hj_res : (D.step P i j j).1.role = .Resetting := by
      rcases h_role_j with h | h
      · -- j Settled: derive False from symmetric argument
        exfalso
        have h1_res : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j)).1.role = .Resetting := by
          rw [← congrArg AgentState.role h_fst]; exact hi_res
        have h2_set : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j)).2.role = .Settled := by
          rw [← congrArg AgentState.role h_snd]; exact h
        have hrij : (D i).1.rank ≠ (D j).1.rank :=
          fun h => hij (hS.toInSrank.ranks_inj h)
        have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij
        have h_no_swap := hS.swap_condition_false i j
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate at h1_res h2_set
        simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
          and_self, if_true, h_no_swap] at h1_res h2_set
        by_cases hpar : n % 2 = 0
        · simp only [hpar, if_true] at h1_res h2_set
          split_ifs at h1_res h2_set <;> simp_all
        · simp only [hpar, if_false] at h1_res h2_set
          split_ifs at h1_res h2_set <;> simp_all
      · exact h
    right
    -- Setup the transitionPEM-level facts (re-derive in this scope)
    have h1_res' : (transitionPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1.role = .Resetting := by
      rw [← congrArg AgentState.role h_fst]; exact hi_res
    have h2_res' : (transitionPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2.role = .Resetting := by
      rw [← congrArg AgentState.role h_snd]; exact hj_res
    have hrij : (D i).1.rank ≠ (D j).1.rank :=
      fun h => hij (hS.toInSrank.ranks_inj h)
    have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij
    have h_no_swap := hS.swap_condition_false i j
    -- Case-split on which of i, j is at median rank
    by_cases hi_med : (D i).1.rank.val + 1 = ceilHalf n
    · -- Case A: i at median → use existing helper after deriving wrong/no_upper for j
      have hj_no_med : (D j).1.rank.val + 1 ≠ ceilHalf n := by
        intro h
        apply hij
        apply hS.toInSrank.ranks_inj
        exact Fin.ext (Nat.add_right_cancel (hi_med.trans h.symm))
      have hi_correct : (D i).1.answer = majorityAnswer D := hM i hi_med
      have hi_timer : (D i).1.timer = 0 := hT i hi_med
      -- If (D j).answer = majority, reset would not fire (b₀.answer = b₁.answer)
      have hj_wrong : (D j).1.answer ≠ majorityAnswer D := by
        intro hj_eq
        have h_eq : (D i).1.answer = (D j).1.answer := by rw [hi_correct, hj_eq]
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate at h1_res'
        simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hi_med, hj_no_med] at h1_res'
        by_cases hpar : n % 2 = 0
        · simp only [hpar, if_true] at h1_res'
          split_ifs at h1_res' <;> simp_all
        · have hi_opinion : opinionToAnswer (D i).2 = (D i).1.answer := by
            rw [opinionToAnswer_median_eq_majorityAnswer_odd hS hi_med hpar,
              hi_correct]
          simp only [hpar, if_false] at h1_res'
          split_ifs at h1_res' <;> simp_all
      -- For EVEN, if j at upper median, phase4_decide sets equal answers (no reset).
      -- For ODD, n/2+1 = ceilHalf n which would put j at median (contradicting hj_no_med).
      have hj_no_upper : (D j).1.rank.val + 1 ≠ n / 2 + 1 := by
        intro h_upper
        by_cases hpar : n % 2 = 0
        · exfalso
          have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
          have hi_lower : (D i).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hi_med
          unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
            phase4_swap phase4_decide phase4_propagate at h1_res'
          simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
            not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
            and_self, if_true, h_no_swap, hi_lower, h_upper, hpar] at h1_res'
          split_ifs at h1_res' <;> simp_all
        · have hceil : ceilHalf n = n / 2 + 1 := by unfold ceilHalf; omega
          exact hj_no_med (h_upper.trans hceil.symm)
      exact step_timer_zero_median_wrong_nonupper_creates_CorrectResetSeed
        hn4 hn0 hRmax hS hij hi_med hi_timer hi_correct hj_wrong hj_no_upper
    · -- Case B: i NOT at median → j must be at median
      have hj_med : (D j).1.rank.val + 1 = ceilHalf n := by
        by_contra hj_no_med
        exfalso
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate at h1_res'
        simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hi_med, hj_no_med] at h1_res'
        split_ifs at h1_res' <;> simp_all
      have hi_no_med := hi_med  -- alias for clarity
      have hj_correct : (D j).1.answer = majorityAnswer D := hM j hj_med
      have hj_timer : (D j).1.timer = 0 := hT j hj_med
      -- If (D i).answer = majority, reset would not fire.
      have hi_wrong : (D i).1.answer ≠ majorityAnswer D := by
        intro hi_eq
        have h_eq : (D i).1.answer = (D j).1.answer := by rw [hi_eq, hj_correct]
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate at h1_res'
        simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hj_med, hi_no_med] at h1_res'
        by_cases hpar : n % 2 = 0
        · simp only [hpar, if_true] at h1_res'
          split_ifs at h1_res' <;> simp_all
        · have hj_opinion : opinionToAnswer (D j).2 = (D j).1.answer := by
            rw [opinionToAnswer_median_eq_majorityAnswer_odd hS hj_med hpar,
              hj_correct]
          simp only [hpar, if_false] at h1_res'
          split_ifs at h1_res' <;> simp_all
      have hi_no_upper : (D i).1.rank.val + 1 ≠ n / 2 + 1 := by
        intro h_upper
        by_cases hpar : n % 2 = 0
        · exfalso
          have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
          have hj_lower : (D j).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hj_med
          unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
            phase4_swap phase4_decide phase4_propagate at h1_res'
          simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
            not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
            and_self, if_true, h_no_swap, hj_lower, h_upper, hpar] at h1_res'
          split_ifs at h1_res' <;> simp_all
        · have hceil : ceilHalf n = n / 2 + 1 := by unfold ceilHalf; omega
          exact hi_no_med (h_upper.trans hceil.symm)
      -- Compute transitionPEM(D i, D j) explicitly when j is at median.
      have h_post_diff : (D j).1.answer ≠ (D i).1.answer := by
        rw [hj_correct]; intro h_eq; exact hi_wrong h_eq.symm
      have htr : transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
          (D i, D j) =
        ({ (D i).1 with
              answer := (D j).1.answer
              role := Role.Resetting
              leader := Leader.L
              resetcount := Rmax }
         { (D j).1 with
              role := Role.Resetting
              leader := Leader.L
              resetcount := Rmax
              answer := (D j).1.answer }) := by
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate
        by_cases hpar : n % 2 = 0
        · -- EVEN
          have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
          have hj_lower : (D j).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hj_med
          have hi_not_lower : (D i).1.rank.val + 1 ≠ n / 2 := by
            rw [← hceil]; exact hi_no_med
          simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
            not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
            and_self, if_true, h_no_swap, hpar, hj_lower, hi_not_lower,
            hi_no_upper, hj_med, hi_no_med, hj_timer, h_post_diff]
          split_ifs <;> simp_all
        · -- ODD
          have hj_opinion : opinionToAnswer (D j).2 = (D j).1.answer := by
            rw [opinionToAnswer_median_eq_majorityAnswer_odd hS hj_med hpar,
              hj_correct]
          have h_post_diff' : opinionToAnswer (D j).2 ≠ (D i).1.answer := by
            rw [hj_opinion]; exact h_post_diff
          simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
            not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
            and_self, if_true, h_no_swap, hpar, hj_med, hi_no_med,
            hj_timer, h_post_diff', hj_opinion]
          split_ifs <;> simp_all
      -- Use htr to derive post-step states for i, j.
      have h_post_i : (D.step P i j i).1 =
          { (D i).1 with
              answer := (D j).1.answer
              role := Role.Resetting
              leader := Leader.L
              resetcount := Rmax } := by
        rw [h_fst]
        show (transitionPEM n Rmax Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1 = _
        rw [htr]
      have h_post_j : (D.step P i j j).1 =
          { (D j).1 with
              role := Role.Resetting
              leader := Leader.L
              resetcount := Rmax
              answer := (D j).1.answer } := by
        rw [h_snd]
        show (transitionPEM n Rmax Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2 = _
        rw [htr]
      have h_post_others : ∀ w, w ≠ i → w ≠ j → (D.step P i j w) = D w := by
        intro w hw hwj; unfold Config.step
        simp [hij, hw, hwj]
      have h_maj : majorityAnswer (D.step P i j) = majorityAnswer D := by
        simpa [P, PEMProtocolCoupled, PEMProtocol] using
          majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j
      have h_nrc : nonResettingCount (D.step P i j) ≤ n - 2 := by
        classical
        unfold nonResettingCount
        set S := Finset.univ.filter (fun w : Fin n =>
          (D.step P i j w).1.role ≠ .Resetting)
        have hi_not : i ∉ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
          rw [h_post_i]
        have hj_not : j ∉ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
          rw [h_post_j]
        have hS_sub : S ⊆ (Finset.univ \ {i, j}) := by
          intro w hw
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, not_or]
          refine ⟨?_, ?_⟩
          · intro h; rw [h] at hw; exact hi_not hw
          · intro h; rw [h] at hw; exact hj_not hw
        have hcard : (Finset.univ \ ({i, j} : Finset (Fin n))).card = n - 2 := by
          have h1 : (Finset.univ : Finset (Fin n)).card = n := Fintype.card_fin n
          have h2 : ({i, j} : Finset (Fin n)).card = 2 := Finset.card_pair hij
          have h3 : (Finset.univ \ ({i, j} : Finset (Fin n))).card =
            (Finset.univ : Finset (Fin n)).card - ({i, j} : Finset (Fin n)).card :=
            Finset.card_sdiff_of_subset (Finset.subset_univ _)
          rw [h3, h1, h2]
        calc S.card ≤ (Finset.univ \ ({i, j} : Finset (Fin n))).card :=
                Finset.card_le_card hS_sub
          _ = n - 2 := hcard
      refine ⟨⟨j, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [h_post_j]
      · rw [h_post_j]
        have h : n - 2 < Rmax := by omega
        exact lt_of_le_of_lt h_nrc h
      · rw [h_post_j]
      · rw [h_post_j, h_maj, hj_correct]
      · intro w hw_res
        by_cases hwi : w = i
        · subst hwi
          rw [h_post_i]
          refine ⟨?_, ?_⟩
          · simp; omega
          · rw [h_maj, hj_correct]
        · by_cases hwj : w = j
          · subst hwj
            rw [h_post_j]
            refine ⟨?_, ?_⟩
            · simp; omega
            · rw [h_maj, hj_correct]
          · exfalso
            have hw_unchanged := h_post_others w hwi hwj
            rw [show (D.step P i j w).1 = (D w).1 from
              congrArg Prod.fst hw_unchanged] at hw_res
            have hw_settled := hS.allSettled w
            rw [hw_settled] at hw_res
            exact Role.noConfusion hw_res


end SSEM
