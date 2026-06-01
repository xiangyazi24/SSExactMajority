import SSExactMajority.UpperBound.Time.Bridge

namespace SSEM

open scoped ENNReal

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000000 in
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
      · rw [h_post_μ]; exact lt_of_le_of_lt h_nrc (lt_of_lt_of_le (by omega) hRmax)
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
      · rw [h_post_μ]; exact lt_of_le_of_lt h_nrc (lt_of_lt_of_le (by omega) hRmax)
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
      · rw [h_post_μ]; exact lt_of_le_of_lt h_nrc (lt_of_lt_of_le (by omega) hRmax)
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
      · rw [h_post_μ]; exact lt_of_le_of_lt h_nrc (lt_of_lt_of_le (by omega) hRmax)
      · rw [h_post_μ]
      · rw [h_post_μ]; simp [h_maj, hμ_ans_eq, hμ_correct]
      · intro w hw_res
        by_cases hwμ : w = μ
        · subst hwμ; rw [h_post_μ]; exact ⟨by simp; omega, by simp [h_maj, hμ_ans_eq, hμ_correct]⟩
        · by_cases hwv : w = v
          · subst hwv; rw [h_post_v]; exact ⟨by simp; omega, by simp [h_maj, hμ_ans_eq, hμ_correct]⟩
          · exfalso; rw [show (D.step P μ v w).1 = (D w).1 from congrArg Prod.fst (h_post_others w hwμ hwv)] at hw_res
            rw [hS.allSettled w] at hw_res; exact Role.noConfusion hw_res

set_option maxRecDepth 65536 in
set_option maxHeartbeats 800000000 in
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
  -- TODO: This theorem needs a responder-median variant of
  -- step_timer_le_one_median_max_creates_CorrectResetSeed.
  -- The brute-force unfold+simp approach overflows maxRecDepth/maxHeartbeats
  -- in Lean 4.30. The first theorem (initiator-median) compiles fine.
  -- See: step argument order asymmetry (D.step P i j vs D.step P j i).
  sorry

end SSEM
