import SSExactMajority.UpperBound.Time.Bridge

namespace SSEM

open scoped ENNReal

set_option maxHeartbeats 64000000 in
theorem step_timer_le_one_median_max_creates_CorrectResetSeed
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (hμ_timer : (D μ).1.timer ≤ 1)
    (hv_max : (D v).1.rank.val + 1 = n)
    (hμ_correct : (D μ).1.answer = majorityAnswer D)
    (hv_wrong : (D v).1.answer ≠ majorityAnswer D) :
    let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
    CorrectResetSeed (D.step P μ v) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hv_no_med : (D v).1.rank.val + 1 ≠ ceilHalf n := by
    intro h; apply hμv; apply hS.toInSrank.ranks_inj
    exact Fin.ext (Nat.add_right_cancel (hμ_med.trans h.symm))
  have hsi := hS.toInSrank.allSettled μ
  have hsv := hS.toInSrank.allSettled v
  have hrij : (D μ).1.rank ≠ (D v).1.rank := fun h => hμv (hS.toInSrank.ranks_inj h)
  have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn0) (D μ).1 (D v).1 hsi hsv hrij
  have h_no_swap := hS.swap_condition_false μ v
  have h_post_diff : (D μ).1.answer ≠ (D v).1.answer := by
    rw [hμ_correct]; exact fun h => hv_wrong h.symm
  have h_fst := Config.step_fst_state P D hμv
  have h_snd := Config.step_snd_state P D hμv (Ne.symm hμv)
  -- Derive post-step states via trace lemmas (dispatch by parity × timer)
  -- In all cases, both μ and v become Resetting with Rmax resetcount
  have hv_not_upper : (D v).1.rank.val + 1 ≠ n / 2 + 1 := by omega
  by_cases hpar : n % 2 = 0
  · -- EVEN
    have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
    have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hμ_med
    have hv_not_lower : (D v).1.rank.val + 1 ≠ n / 2 := by omega
    by_cases hTimer0 : (D μ).1.timer = 0
    · -- timer = 0: use timer_zero trace
      have htr := propagation_reset_fires_even_lower_timer_zero_no_swap_trace
        (trank := Rmax) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hμv hpar hμ_lower hv_not_lower
        hv_not_upper hTimer0 h_no_swap h_post_diff
      have h_post_μ : (D.step P μ v μ).1 =
          { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax } := by
        rw [h_fst]; show (transitionPEM _ _ _ _ _).1 = _; rw [htr]
      have h_post_v : (D.step P μ v v).1 =
          { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := (D μ).1.answer } := by
        rw [h_snd]; show (transitionPEM _ _ _ _ _).2 = _; rw [htr]
      have h_post_others : ∀ w, w ≠ μ → w ≠ v → (D.step P μ v w) = D w := by
        intro w hw hwv; unfold Config.step; simp [hμv, hw, hwv]
      have h_maj : majorityAnswer (D.step P μ v) = majorityAnswer D := by
        simpa [P, PEMProtocolCoupled, PEMProtocol] using
          majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ v
      have h_nrc : nonResettingCount (D.step P μ v) ≤ n - 2 := by
        classical
        unfold nonResettingCount
        set S := Finset.univ.filter (fun w : Fin n => (D.step P μ v w).1.role ≠ .Resetting)
        have hμ_not : μ ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [h_post_μ]
        have hv_not : v ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [h_post_v]
        have hS_sub : S ⊆ (Finset.univ \ {μ, v}) := by
          intro w hw; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hμ_not (h ▸ hw), fun h => hv_not (h ▸ hw)⟩
        calc S.card ≤ (Finset.univ \ ({μ, v} : Finset (Fin n))).card := Finset.card_le_card hS_sub
          _ = n - 2 := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, Finset.card_pair hμv]
      refine ⟨⟨μ, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [h_post_μ]
      · rw [h_post_μ]; exact lt_of_le_of_lt h_nrc (by omega)
      · rw [h_post_μ]
      · rw [h_post_μ]; simp [h_maj, hμ_correct]
      · intro w hw_res
        by_cases hwμ : w = μ
        · subst hwμ; rw [h_post_μ]; exact ⟨by simp; omega, by simp [h_maj, hμ_correct]⟩
        · by_cases hwv : w = v
          · subst hwv; rw [h_post_v]; exact ⟨by simp; omega, by simp [h_maj, hμ_correct]⟩
          · exfalso; rw [show (D.step P μ v w).1 = (D w).1 from congrArg Prod.fst (h_post_others w hwμ hwv)] at hw_res
            rw [hS.allSettled w] at hw_res; exact Role.noConfusion hw_res
    · -- timer = 1: use timer_one trace
      have hTimer1 : (D μ).1.timer = 1 := by omega
      have htr := propagation_reset_fires_even_lower_timer_one_max_no_swap_trace
        (trank := Rmax) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hn4 hμv hpar hμ_lower hv_max
        hTimer1 h_no_swap h_post_diff
      have h_post_μ : (D.step P μ v μ).1 =
          { (D μ).1 with timer := 0, role := .Resetting, leader := .L, resetcount := Rmax } := by
        rw [h_fst]; show (transitionPEM _ _ _ _ _).1 = _; rw [htr]
      have h_post_v : (D.step P μ v v).1 =
          { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := (D μ).1.answer } := by
        rw [h_snd]; show (transitionPEM _ _ _ _ _).2 = _; rw [htr]
      have h_post_others : ∀ w, w ≠ μ → w ≠ v → (D.step P μ v w) = D w := by
        intro w hw hwv; unfold Config.step; simp [hμv, hw, hwv]
      have h_maj : majorityAnswer (D.step P μ v) = majorityAnswer D := by
        simpa [P, PEMProtocolCoupled, PEMProtocol] using
          majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ v
      have h_nrc : nonResettingCount (D.step P μ v) ≤ n - 2 := by
        classical
        unfold nonResettingCount
        set S := Finset.univ.filter (fun w : Fin n => (D.step P μ v w).1.role ≠ .Resetting)
        have hμ_not : μ ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [h_post_μ]
        have hv_not : v ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [h_post_v]
        have hS_sub : S ⊆ (Finset.univ \ {μ, v}) := by
          intro w hw; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hμ_not (h ▸ hw), fun h => hv_not (h ▸ hw)⟩
        calc S.card ≤ (Finset.univ \ ({μ, v} : Finset (Fin n))).card := Finset.card_le_card hS_sub
          _ = n - 2 := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, Finset.card_pair hμv]
      refine ⟨⟨μ, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [h_post_μ]
      · rw [h_post_μ]; exact lt_of_le_of_lt h_nrc (by omega)
      · rw [h_post_μ]
      · rw [h_post_μ]; simp [h_maj, hμ_correct]
      · intro w hw_res
        by_cases hwμ : w = μ
        · subst hwμ; rw [h_post_μ]; exact ⟨by simp; omega, by simp [h_maj, hμ_correct]⟩
        · by_cases hwv : w = v
          · subst hwv; rw [h_post_v]; exact ⟨by simp; omega, by simp [h_maj, hμ_correct]⟩
          · exfalso; rw [show (D.step P μ v w).1 = (D w).1 from congrArg Prod.fst (h_post_others w hwμ hwv)] at hw_res
            rw [hS.allSettled w] at hw_res; exact Role.noConfusion hw_res
  · -- ODD
    have hμ_ans_eq : opinionToAnswer (D μ).2 = (D μ).1.answer := by
      rw [opinionToAnswer_median_eq_majorityAnswer_odd hS hμ_med hpar, hμ_correct]
    have h_post_diff_odd : opinionToAnswer (D μ).2 ≠ (D v).1.answer := by
      rw [hμ_ans_eq]; exact h_post_diff
    by_cases hTimer0 : (D μ).1.timer = 0
    · have htr := propagation_reset_fires_no_swap_trace
        (trank := Rmax) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hμv hμ_med hv_no_med
        hTimer0 h_no_swap hpar h_post_diff_odd
      have h_post_μ : (D.step P μ v μ).1 =
          { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2 } := by
        rw [h_fst]; show (transitionPEM _ _ _ _ _).1 = _; rw [htr]
      have h_post_v : (D.step P μ v v).1 =
          { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2 } := by
        rw [h_snd]; show (transitionPEM _ _ _ _ _).2 = _; rw [htr]
      have h_post_others : ∀ w, w ≠ μ → w ≠ v → (D.step P μ v w) = D w := by
        intro w hw hwv; unfold Config.step; simp [hμv, hw, hwv]
      have h_maj : majorityAnswer (D.step P μ v) = majorityAnswer D := by
        simpa [P, PEMProtocolCoupled, PEMProtocol] using
          majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ v
      have h_nrc : nonResettingCount (D.step P μ v) ≤ n - 2 := by
        classical
        unfold nonResettingCount
        set S := Finset.univ.filter (fun w : Fin n => (D.step P μ v w).1.role ≠ .Resetting)
        have hμ_not : μ ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [h_post_μ]
        have hv_not : v ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [h_post_v]
        have hS_sub : S ⊆ (Finset.univ \ {μ, v}) := by
          intro w hw; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hμ_not (h ▸ hw), fun h => hv_not (h ▸ hw)⟩
        calc S.card ≤ (Finset.univ \ ({μ, v} : Finset (Fin n))).card := Finset.card_le_card hS_sub
          _ = n - 2 := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, Finset.card_pair hμv]
      refine ⟨⟨μ, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [h_post_μ]
      · rw [h_post_μ]; exact lt_of_le_of_lt h_nrc (by omega)
      · rw [h_post_μ]
      · rw [h_post_μ]; simp [h_maj, hμ_ans_eq, hμ_correct]
      · intro w hw_res
        by_cases hwμ : w = μ
        · subst hwμ; rw [h_post_μ]; exact ⟨by simp; omega, by simp [h_maj, hμ_ans_eq, hμ_correct]⟩
        · by_cases hwv : w = v
          · subst hwv; rw [h_post_v]; exact ⟨by simp; omega, by simp [h_maj, hμ_ans_eq, hμ_correct]⟩
          · exfalso; rw [show (D.step P μ v w).1 = (D w).1 from congrArg Prod.fst (h_post_others w hwμ hwv)] at hw_res
            rw [hS.allSettled w] at hw_res; exact Role.noConfusion hw_res
    · have hTimer1 : (D μ).1.timer = 1 := by omega
      have htr := propagation_reset_fires_no_swap_max_timer_one_trace
        (trank := Rmax) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hn4 hμv hμ_med hv_max
        hTimer1 h_no_swap hpar h_post_diff_odd
      have h_post_μ : (D.step P μ v μ).1 =
          { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2, timer := 0 } := by
        rw [h_fst]; show (transitionPEM _ _ _ _ _).1 = _; rw [htr]
      have h_post_v : (D.step P μ v v).1 =
          { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2 } := by
        rw [h_snd]; show (transitionPEM _ _ _ _ _).2 = _; rw [htr]
      have h_post_others : ∀ w, w ≠ μ → w ≠ v → (D.step P μ v w) = D w := by
        intro w hw hwv; unfold Config.step; simp [hμv, hw, hwv]
      have h_maj : majorityAnswer (D.step P μ v) = majorityAnswer D := by
        simpa [P, PEMProtocolCoupled, PEMProtocol] using
          majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ v
      have h_nrc : nonResettingCount (D.step P μ v) ≤ n - 2 := by
        classical
        unfold nonResettingCount
        set S := Finset.univ.filter (fun w : Fin n => (D.step P μ v w).1.role ≠ .Resetting)
        have hμ_not : μ ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [h_post_μ]
        have hv_not : v ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [h_post_v]
        have hS_sub : S ⊆ (Finset.univ \ {μ, v}) := by
          intro w hw; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hμ_not (h ▸ hw), fun h => hv_not (h ▸ hw)⟩
        calc S.card ≤ (Finset.univ \ ({μ, v} : Finset (Fin n))).card := Finset.card_le_card hS_sub
          _ = n - 2 := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, Finset.card_pair hμv]
      refine ⟨⟨μ, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [h_post_μ]
      · rw [h_post_μ]; exact lt_of_le_of_lt h_nrc (by omega)
      · rw [h_post_μ]
      · rw [h_post_μ]; simp [h_maj, hμ_ans_eq, hμ_correct]
      · intro w hw_res
        by_cases hwμ : w = μ
        · subst hwμ; rw [h_post_μ]; exact ⟨by simp; omega, by simp [h_maj, hμ_ans_eq, hμ_correct]⟩
        · by_cases hwv : w = v
          · subst hwv; rw [h_post_v]; exact ⟨by simp; omega, by simp [h_maj, hμ_ans_eq, hμ_correct]⟩
          · exfalso; rw [show (D.step P μ v w).1 = (D w).1 from congrArg Prod.fst (h_post_others w hwμ hwv)] at hw_res
            rw [hS.allSettled w] at hw_res; exact Role.noConfusion hw_res

set_option maxHeartbeats 64000000 in
theorem step_InSswap_break_creates_CorrectResetSeed_even_timer_pos
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    (hM : MedianAnswerCorrect D)
    (hPar : n % 2 = 0)
    (hT : MedianTimerAtLeast 1 D)
    {i j : Fin n}
    (hS' : ¬ InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)) :
    CorrectResetSeed (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  by_cases hij : i = j
  · exfalso; apply hS'; subst hij
    have heq : D.step P i i = D := by funext w; unfold Config.step; simp
    rw [heq]; exact hS
  suffices h : InSswap (D.step P i j) ∨ CorrectResetSeed (D.step P i j) from
    h.resolve_left hS'
  have hsi := hS.toInSrank.allSettled i
  have hsj := hS.toInSrank.allSettled j
  have h_fst := Config.step_fst_state P D hij
  have h_snd := Config.step_snd_state P D hij (Ne.symm hij)
  have h_role_i : (D.step P i j i).1.role = .Settled ∨
      (D.step P i j i).1.role = .Resetting := by
    have hrij' : (D i).1.rank ≠ (D j).1.rank := fun h => hij (hS.toInSrank.ranks_inj h)
    have hRD' := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij'
    have h_no_swap' := hS.swap_condition_false i j
    rw [congrArg AgentState.role h_fst]
    show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1.role = .Settled ∨ _
    unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
      phase4_swap phase4_decide phase4_propagate
    simp only [hRD', hsi, hsj, ne_eq, role_settled_ne_resetting,
      not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
      and_self, if_true, h_no_swap']
    split_ifs <;> simp_all
  have h_role_j : (D.step P i j j).1.role = .Settled ∨
      (D.step P i j j).1.role = .Resetting := by
    have hrij' : (D i).1.rank ≠ (D j).1.rank := fun h => hij (hS.toInSrank.ranks_inj h)
    have hRD' := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij'
    have h_no_swap' := hS.swap_condition_false i j
    rw [congrArg AgentState.role h_snd]
    show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2.role = .Settled ∨ _
    unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
      phase4_swap phase4_decide phase4_propagate
    simp only [hRD', hsi, hsj, ne_eq, role_settled_ne_resetting,
      not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
      and_self, if_true, h_no_swap']
    split_ifs <;> simp_all
  by_cases hi_settled : (D.step P i j i).1.role = .Settled
  · by_cases hj_settled : (D.step P i j j).1.role = .Settled
    · left
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro w
        by_cases hwi : w = i; · rw [hwi]; exact hi_settled
        by_cases hwj : w = j; · rw [hwj]; exact hj_settled
        rw [show (D.step P i j w) = D w from by unfold Config.step; simp [hij, hwi, hwj]]
        exact hS.toInSrank.allSettled w
      · intro w1 w2 heq
        simp only [step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hS] at heq
        exact hS.toInSrank.ranks_inj heq
      · intro w
        rw [show (D.step P i j w).2 = (D w).2 from by
            unfold Config.step
            by_cases hwi : w = i; · rw [hwi]; simp [hij]
            by_cases hwj : w = j; · rw [hwj]; simp [hij, Ne.symm hij]
            simp [hij, hwi, hwj],
          step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hS,
          show nAOf (D.step P i j) = nAOf D from by
            unfold nAOf Config.agentsWithInput Config.inputOf; congr 1; ext w'
            simp only [Finset.mem_filter]; constructor
            · intro ⟨hm, h⟩; exact ⟨hm, by
                rw [show (D.step P i j w').2 = (D w').2 from by
                  unfold Config.step
                  by_cases hwi : w' = i; · rw [hwi]; simp [hij]
                  by_cases hwj : w' = j; · rw [hwj]; simp [hij, Ne.symm hij]
                  simp [hij, hwi, hwj]] at h; exact h⟩
            · intro ⟨hm, h⟩; exact ⟨hm, by
                rw [show (D.step P i j w').2 = (D w').2 from by
                  unfold Config.step
                  by_cases hwi : w' = i; · rw [hwi]; simp [hij]
                  by_cases hwj : w' = j; · rw [hwj]; simp [hij, Ne.symm hij]
                  simp [hij, hwi, hwj]]; exact h⟩]
        exact hS.input_rank w
    · exfalso
      have hj_res := h_role_j.resolve_left hj_settled
      have h2_res : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
          (D i, D j)).2.role = .Resetting := by rw [← congrArg AgentState.role h_snd]; exact hj_res
      have h1_set : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
          (D i, D j)).1.role = .Settled := by rw [← congrArg AgentState.role h_fst]; exact hi_settled
      have hrij : (D i).1.rank ≠ (D j).1.rank := fun h => hij (hS.toInSrank.ranks_inj h)
      have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij
      have h_no_swap := hS.swap_condition_false i j
      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
        phase4_swap phase4_decide phase4_propagate at h2_res h1_set
      simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
        not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
        and_self, if_true, h_no_swap, hPar, if_true] at h2_res h1_set
      split_ifs at h2_res h1_set <;> simp_all
  · have hi_res := h_role_i.resolve_left hi_settled
    have hj_res : (D.step P i j j).1.role = .Resetting := by
      rcases h_role_j with h | h
      · exfalso
        have h1_res : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j)).1.role = .Resetting := by rw [← congrArg AgentState.role h_fst]; exact hi_res
        have h2_set : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j)).2.role = .Settled := by rw [← congrArg AgentState.role h_snd]; exact h
        have hrij : (D i).1.rank ≠ (D j).1.rank := fun h => hij (hS.toInSrank.ranks_inj h)
        have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij
        have h_no_swap := hS.swap_condition_false i j
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate at h1_res h2_set
        simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hPar, if_true] at h1_res h2_set
        split_ifs at h1_res h2_set <;> simp_all
      · exact h
    right
    have h1_res' : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (D i, D j)).1.role = .Resetting := by rw [← congrArg AgentState.role h_fst]; exact hi_res
    have hrij : (D i).1.rank ≠ (D j).1.rank := fun h => hij (hS.toInSrank.ranks_inj h)
    have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij
    have h_no_swap := hS.swap_condition_false i j
    have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
    by_cases hi_med : (D i).1.rank.val + 1 = ceilHalf n
    · have hj_no_med : (D j).1.rank.val + 1 ≠ ceilHalf n := by
        intro h; apply hij; apply hS.toInSrank.ranks_inj
        exact Fin.ext (Nat.add_right_cancel (hi_med.trans h.symm))
      have hi_correct : (D i).1.answer = majorityAnswer D := hM i hi_med
      have hi_timer_pos : 1 ≤ (D i).1.timer := hT i hi_med
      have hj_wrong : (D j).1.answer ≠ majorityAnswer D := by
        intro hj_eq
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate at h1_res'
        have hi_lower : (D i).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hi_med
        simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hi_med, hj_no_med, hPar, if_true, hi_lower] at h1_res'
        split_ifs at h1_res' <;> simp_all
      have hj_max : (D j).1.rank.val + 1 = n := by
        by_contra hj_not_max
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate at h1_res'
        have hi_lower : (D i).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hi_med
        simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hi_med, hj_no_med, hPar, if_true,
          hi_lower, hj_not_max] at h1_res'
        split_ifs at h1_res' <;> simp_all <;> omega
      have hi_timer_le : (D i).1.timer ≤ 1 := by
        by_contra h; push_neg at h
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate at h1_res'
        have hi_lower : (D i).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hi_med
        simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hi_med, hj_no_med, hPar, if_true,
          hi_lower, hj_max] at h1_res'
        split_ifs at h1_res' <;> simp_all <;> omega
      exact step_timer_le_one_median_max_creates_CorrectResetSeed
        hn4 hn0 hRmax hS hij hi_med hi_timer_le hj_max hi_correct hj_wrong
    · have hj_med : (D j).1.rank.val + 1 = ceilHalf n := by
        by_contra hj_no_med
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate at h1_res'
        simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hi_med, hj_no_med, hPar, if_true] at h1_res'
        split_ifs at h1_res' <;> simp_all
      have hi_no_med := hi_med
      have hj_correct : (D j).1.answer = majorityAnswer D := hM j hj_med
      have hj_timer_pos : 1 ≤ (D j).1.timer := hT j hj_med
      have hi_wrong : (D i).1.answer ≠ majorityAnswer D := by
        intro hi_eq
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate at h1_res'
        have hj_lower : (D j).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hj_med
        simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hj_lower, hi_no_med, hPar, if_true] at h1_res'
        split_ifs at h1_res' <;> simp_all
      have hi_max : (D i).1.rank.val + 1 = n := by
        by_contra hi_not_max
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate at h1_res'
        have hj_lower : (D j).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hj_med
        simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hj_lower, hi_no_med, hPar, if_true,
          hi_not_max] at h1_res'
        split_ifs at h1_res' <;> simp_all <;> omega
      have hj_timer_le : (D j).1.timer ≤ 1 := by
        by_contra h; push_neg at h
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate at h1_res'
        have hj_lower : (D j).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hj_med
        simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hj_lower, hi_no_med, hPar, if_true,
          hi_max] at h1_res'
        split_ifs at h1_res' <;> simp_all <;> omega
      exact step_timer_le_one_median_max_creates_CorrectResetSeed
        hn4 hn0 hRmax hS (Ne.symm hij) hj_med hj_timer_le hi_max hj_correct hi_wrong

end SSEM
