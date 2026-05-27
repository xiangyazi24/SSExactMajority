import SSExactMajority.UpperBound.Time.Bridge

namespace SSEM

open scoped ENNReal


set_option maxRecDepth 4096 in
set_option maxHeartbeats 64000000 in
theorem step_InSswap_break_creates_CorrectResetSeed_odd
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    (hOdd : n % 2 ≠ 0)
    {i j : Fin n}
    (hS' : ¬ InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)) :
    CorrectResetSeed (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  by_cases hij : i = j
  · exfalso; apply hS'; subst hij
    have heq : D.step P i i = D := by
      funext w; unfold Config.step; simp only [if_true]
    rw [heq]; exact hS
  suffices h : InSswap (D.step P i j) ∨ CorrectResetSeed (D.step P i j) from
    h.resolve_left hS'
  have hsi := hS.toInSrank.allSettled i
  have hsj := hS.toInSrank.allSettled j
  have h_fst := Config.step_fst_state P D hij
  have h_snd := Config.step_snd_state P D hij (Ne.symm hij)
  have h_role_i : (D.step P i j i).1.role = .Settled ∨
      (D.step P i j i).1.role = .Resetting := by
    have hrij : (D i).1.rank ≠ (D j).1.rank := fun h => hij (hS.toInSrank.ranks_inj h)
    have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij
    have h_no_swap := hS.swap_condition_false i j
    rw [congrArg AgentState.role h_fst]
    show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1.role = .Settled ∨ _
    unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
      phase4_swap phase4_decide phase4_propagate
    simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
      not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
      and_self, if_true, h_no_swap]
    split_ifs <;> simp_all
  have h_role_j : (D.step P i j j).1.role = .Settled ∨
      (D.step P i j j).1.role = .Resetting := by
    have hrij : (D i).1.rank ≠ (D j).1.rank := fun h => hij (hS.toInSrank.ranks_inj h)
    have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij
    have h_no_swap := hS.swap_condition_false i j
    rw [congrArg AgentState.role h_snd]
    show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2.role = .Settled ∨ _
    unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
      phase4_swap phase4_decide phase4_propagate
    simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
      not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
      and_self, if_true, h_no_swap]
    split_ifs <;> simp_all
  by_cases hi_settled : (D.step P i j i).1.role = .Settled
  · by_cases hj_settled : (D.step P i j j).1.role = .Settled
    · left
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro w
        by_cases hwi : w = i
        · rw [hwi]; exact hi_settled
        · by_cases hwj : w = j
          · rw [hwj]; exact hj_settled
          · rw [show (D.step P i j w) = D w from by
                unfold Config.step; simp [hij, hwi, hwj]]
            exact hS.toInSrank.allSettled w
      · intro w1 w2 heq
        simp only [step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) hn0 hS] at heq
        exact hS.toInSrank.ranks_inj heq
      · intro w
        rw [show (D.step P i j w).2 = (D w).2 from by
          unfold Config.step
          by_cases hwi : w = i; · rw [hwi]; simp [hij]
          by_cases hwj : w = j; · rw [hwj]; simp [hij, Ne.symm hij]
          simp [hij, hwi, hwj]]
        rw [show (D.step P i j w).1.rank = (D w).1.rank from
          step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
            (Dmax := Dmax) hn0 hS w]
        rw [show nAOf (D.step P i j) = nAOf D from by
          unfold nAOf Config.agentsWithInput Config.inputOf; congr 1; ext w'
          simp only [Finset.mem_filter]; constructor
          · intro ⟨hm, h⟩; exact ⟨hm, by
              rw [show (D.step P i j w').2 = (D w').2 from by
                unfold Config.step
                by_cases hwi' : w' = i; · rw [hwi']; simp [hij]
                by_cases hwj' : w' = j; · rw [hwj']; simp [hij, Ne.symm hij]
                simp [hij, hwi', hwj']] at h; exact h⟩
          · intro ⟨hm, h⟩; exact ⟨hm, by
              rw [show (D.step P i j w').2 = (D w').2 from by
                unfold Config.step
                by_cases hwi' : w' = i; · rw [hwi']; simp [hij]
                by_cases hwj' : w' = j; · rw [hwj']; simp [hij, Ne.symm hij]
                simp [hij, hwi', hwj']]; exact h⟩]
        exact hS.input_rank w
    · -- j Resetting, i Settled: derive j Resetting from h_role_j
      have hj_res := h_role_j.resolve_left hj_settled
      -- Both must be Resetting (phase4_propagate sets both simultaneously)
      have hi_res : (D.step P i j i).1.role = .Resetting := by
        exfalso
        have h1_set := hi_settled
        have h2_res := hj_res
        have h1_res' : (transitionPEM n Rmax Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2.role = .Resetting := by
          rw [show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j)).2.role = (D.step P i j j).1.role from
            (congrArg AgentState.role h_snd).symm]; exact h2_res
        have h1_set' : (transitionPEM n Rmax Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1.role = .Settled := by
          rw [show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j)).1.role = (D.step P i j i).1.role from
            (congrArg AgentState.role h_fst).symm]; exact h1_set
        have hrij : (D i).1.rank ≠ (D j).1.rank :=
          fun h => hij (hS.toInSrank.ranks_inj h)
        have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij
        have h_no_swap := hS.swap_condition_false i j
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate at h1_res' h1_set'
        simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
          and_self, if_true, h_no_swap] at h1_res' h1_set'
        by_cases hpar : n % 2 = 0
        · simp only [hpar, if_true] at h1_res' h1_set'
          split_ifs at h1_res' h1_set' <;> simp_all
        · simp only [hpar, if_false] at h1_res' h1_set'
          split_ifs at h1_res' h1_set' <;> simp_all
      exact absurd hi_settled (by rw [hi_res]; exact Role.noConfusion)
  · -- i Resetting
    have hi_res := h_role_i.resolve_left hi_settled
    by_cases hj_settled : (D.step P i j j).1.role = .Settled
    · -- i Resetting, j Settled: symmetrical to above, derive both Resetting
      have hj_res : (D.step P i j j).1.role = .Resetting := by
        exfalso
        have h2_set := hj_settled
        have h1_res := hi_res
        have h1_res' : (transitionPEM n Rmax Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1.role = .Resetting := by
          exact h_fst.symm ▸ h1_res
        have h2_set' : (transitionPEM n Rmax Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2.role = .Settled := by
          exact h_snd.symm ▸ h2_set
        have hrij : (D i).1.rank ≠ (D j).1.rank :=
          fun h => hij (hS.toInSrank.ranks_inj h)
        have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij
        have h_no_swap := hS.swap_condition_false i j
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate at h1_res' h2_set'
        simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
          and_self, if_true, h_no_swap] at h1_res' h2_set'
        by_cases hpar : n % 2 = 0
        · simp only [hpar, if_true] at h1_res' h2_set'
          split_ifs at h1_res' h2_set' <;> simp_all
        · simp only [hpar, if_false] at h1_res' h2_set'
          split_ifs at h1_res' h2_set' <;> simp_all
      exact absurd hj_settled (by rw [hj_res]; exact Role.noConfusion)
    · -- Both Resetting → right (CRS)
      have hj_res := h_role_j.resolve_left hj_settled
      right
      -- For odd n, phase4_decide sets the median's answer to
      -- opinionToAnswer(input) = majorityAnswer regardless of pre-step answer.
      -- Propagation then copies this correct answer to both agents.
      -- The CRS construction follows: both Resetting with rc=Rmax, leader=L,
      -- answer=majorityAnswer, and rc > nonResettingCount (since only 2 agents
      -- changed and Rmax ≥ n > n-2).
      -- Re-derive transitionPEM-level facts in this scope
      have h1_res' : (transitionPEM n Rmax Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1.role = .Resetting := by
        exact h_fst.symm ▸ hi_res
      have h2_res' : (transitionPEM n Rmax Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2.role = .Resetting := by
        exact h_snd.symm ▸ hj_res
      have hrij : (D i).1.rank ≠ (D j).1.rank :=
        fun h => hij (hS.toInSrank.ranks_inj h)
      have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij
      have h_no_swap := hS.swap_condition_false i j
      -- Case-split on which of i, j is at median rank.
      -- For odd n, exactly one of them must be the median for propagation to fire.
      by_cases hi_med : (D i).1.rank.val + 1 = ceilHalf n
      · -- Case A: i at median
        have hj_no_med : (D j).1.rank.val + 1 ≠ ceilHalf n := by
          intro h; exact hij (hS.toInSrank.ranks_inj (Fin.ext (by omega)))
        -- For odd n, phase4_decide sets i's answer to opinionToAnswer(input(i))
        -- = majorityAnswer.  If j also had correct answer, propagation wouldn't
        -- fire (no disagreement), contradicting both-Resetting.
        have hj_wrong : (D j).1.answer ≠ majorityAnswer D := by
          intro hj_eq
          have hi_opinion : opinionToAnswer (D i).2 = majorityAnswer D :=
            opinionToAnswer_median_eq_majorityAnswer_odd hS hi_med hOdd
          unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
            phase4_swap phase4_decide phase4_propagate at h1_res'
          simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
            not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
            and_self, if_true, h_no_swap, hi_med, hj_no_med, hOdd] at h1_res'
          split_ifs at h1_res' <;> simp_all
        -- j is not at upper-median (for odd n: n/2+1 = ceilHalf n → j = median,
        -- contradicting hj_no_med)
        have hj_no_upper : (D j).1.rank.val + 1 ≠ n / 2 + 1 := by
          intro h_upper
          have hceil : ceilHalf n = n / 2 + 1 := by unfold ceilHalf; omega
          exact hj_no_med (h_upper.trans hceil.symm)
        -- CRS construction via protocol unfolding.
        -- Sub-case on j at max rank to pick the right trace lemma.
        have hi_opinion : opinionToAnswer (D i).2 = majorityAnswer D :=
          opinionToAnswer_median_eq_majorityAnswer_odd hS hi_med hOdd
        have h_post_diff : opinionToAnswer (D i).2 ≠ (D j).1.answer := by
          rw [hi_opinion]; exact fun h => hj_wrong h.symm
        have h_maj : majorityAnswer (D.step P i j) = majorityAnswer D := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using
            majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
              (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j
        -- Compute post-step state at i and j via case-split on pre-timer.
        have h_post_states :
            (D.step P i j i).1.role = .Resetting ∧
            (D.step P i j i).1.leader = .L ∧
            (D.step P i j i).1.resetcount = Rmax ∧
            (D.step P i j i).1.answer = majorityAnswer D ∧
            (D.step P i j j).1.role = .Resetting ∧
            (D.step P i j j).1.leader = .L ∧
            (D.step P i j j).1.resetcount = Rmax ∧
            (D.step P i j j).1.answer = majorityAnswer D := by
          by_cases hj_max : (D j).1.rank.val + 1 = n
          · have hi_timer_one : (D i).1.timer = 1 := by
              by_contra h
              unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
                phase4_swap phase4_decide phase4_propagate at h1_res'
              simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
                not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
                and_self, if_true, h_no_swap, hi_med, hj_no_med, hOdd, hj_max] at h1_res'
              split_ifs at h1_res' <;> simp_all
            have h_trace := propagation_reset_fires_no_swap_max_timer_one_trace
              (trank := Rmax) (Rmax := Rmax)
              (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
              rankDeltaOSSR_satisfies_fix hS.toInSrank hn4 hij hi_med hj_max
              hi_timer_one h_no_swap hOdd h_post_diff
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.role = _
              rw [h_trace]
            · simp only [h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.leader = _
              rw [h_trace]
            · simp only [h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.resetcount = _
              rw [h_trace]
            · simp only [h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.answer = _
              rw [h_trace]; exact hi_opinion
            · simp only [h_snd]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).2.role = _
              rw [h_trace]
            · simp only [h_snd]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).2.leader = _
              rw [h_trace]
            · simp only [h_snd]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).2.resetcount = _
              rw [h_trace]
            · simp only [h_snd]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).2.answer = _
              rw [h_trace]; exact hi_opinion
          · have hj_no_max : (D j).1.rank.val + 1 ≠ n := hj_max
            have hi_timer_zero : (D i).1.timer = 0 := by
              by_contra h
              unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
                phase4_swap phase4_decide phase4_propagate at h1_res'
              simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
                not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
                and_self, if_true, h_no_swap, hi_med, hj_no_med, hOdd, hj_no_max] at h1_res'
              split_ifs at h1_res' <;> simp_all
            have h_trace := propagation_reset_fires_no_swap_trace
              (trank := Rmax) (Rmax := Rmax)
              (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
              rankDeltaOSSR_satisfies_fix hS.toInSrank hij hi_med hj_no_med
              hi_timer_zero h_no_swap hOdd h_post_diff
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.role = _
              rw [h_trace]
            · simp only [h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.leader = _
              rw [h_trace]
            · simp only [h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.resetcount = _
              rw [h_trace]
            · simp only [h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.answer = _
              rw [h_trace]; exact hi_opinion
            · simp only [h_snd]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).2.role = _
              rw [h_trace]
            · simp only [h_snd]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).2.leader = _
              rw [h_trace]
            · simp only [h_snd]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).2.resetcount = _
              rw [h_trace]
            · simp only [h_snd]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).2.answer = _
              rw [h_trace]; exact hi_opinion
        obtain ⟨hi_role, hi_lead, hi_rc, hi_ans, hj_role, hj_lead, hj_rc, hj_ans⟩ :=
          h_post_states
        -- Build CRS using i as seed
        have h_post_others : ∀ w, w ≠ i → w ≠ j → (D.step P i j w) = D w := by
          intro w hw hwj; unfold Config.step; simp [hij, hw, hwj]
        have h_nrc : nonResettingCount (D.step P i j) ≤ n - 2 := by
          classical
          unfold nonResettingCount
          set S := Finset.univ.filter (fun w : Fin n =>
            (D.step P i j w).1.role ≠ .Resetting)
          have hi_not : i ∉ S := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
            exact hi_role
          have hj_not : j ∉ S := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
            exact hj_role
          have hS_sub : S ⊆ (Finset.univ \ {i, j}) := by
            intro w hw
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
              Finset.mem_insert, Finset.mem_singleton, not_or]
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
        refine ⟨⟨i, hi_role, ?_, hi_lead, ?_⟩, ?_⟩
        · rw [hi_rc]; have : n - 2 < Rmax := by omega
          exact lt_of_le_of_lt h_nrc this
        · rw [hi_ans, h_maj]
        · intro w hw_res
          by_cases hwi : w = i
          · subst hwi
            refine ⟨?_, ?_⟩
            · rw [hi_rc]; omega
            · rw [hi_ans, h_maj]
          · by_cases hwj : w = j
            · subst hwj
              refine ⟨?_, ?_⟩
              · rw [hj_rc]; omega
              · rw [hj_ans, h_maj]
            · exfalso
              have hw_unchanged := h_post_others w hwi hwj
              rw [show (D.step P i j w).1 = (D w).1 from
                congrArg Prod.fst hw_unchanged] at hw_res
              have hw_settled := hS.allSettled w
              rw [hw_settled] at hw_res
              exact Role.noConfusion hw_res
      · -- Case B: j at median (symmetric to Case A)
        have hj_med : (D j).1.rank.val + 1 = ceilHalf n := by
          by_contra hj_no_med
          unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
            phase4_swap phase4_decide phase4_propagate at h1_res'
          simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
            not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
            and_self, if_true, h_no_swap, hi_med, hj_no_med] at h1_res'
          simp only [hOdd, if_false] at h1_res'
          split_ifs at h1_res' <;> simp_all
        have hi_no_med := hi_med
        have hj_opinion : opinionToAnswer (D j).2 = majorityAnswer D :=
          opinionToAnswer_median_eq_majorityAnswer_odd hS hj_med hOdd
        have hi_wrong : (D i).1.answer ≠ majorityAnswer D := by
          intro hi_eq
          unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
            phase4_swap phase4_decide phase4_propagate at h1_res'
          simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
            not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
            and_self, if_true, h_no_swap, hj_med, hi_no_med, hOdd] at h1_res'
          split_ifs at h1_res' <;> simp_all
        have hi_no_upper : (D i).1.rank.val + 1 ≠ n / 2 + 1 := by
          intro h_upper
          have hceil : ceilHalf n = n / 2 + 1 := by unfold ceilHalf; omega
          exact hi_no_med (h_upper.trans hceil.symm)
        have h_post_diff : opinionToAnswer (D j).2 ≠ (D i).1.answer := by
          rw [hj_opinion]; exact fun h => hi_wrong h.symm
        have h_maj : majorityAnswer (D.step P i j) = majorityAnswer D := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using
            majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
              (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j
        -- Compute htr via case-split on whether i is at max.
        have htr : transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j) =
            ({ (D i).1 with
                answer := opinionToAnswer (D j).2
                role := .Resetting
                leader := .L
                resetcount := Rmax },
             { (D j).1 with
                role := .Resetting
                leader := .L
                resetcount := Rmax
                answer := opinionToAnswer (D j).2 }) := by
          by_cases hi_max : (D i).1.rank.val + 1 = n
          · -- i at max → pre j.timer = 1
            have hj_timer_one : (D j).1.timer = 1 := by
              by_contra h
              unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
                phase4_swap phase4_decide phase4_propagate at h1_res'
              simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
                not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
                and_self, if_true, h_no_swap, hj_med, hi_no_med, hOdd, hi_max] at h1_res'
              split_ifs at h1_res' <;> simp_all
            unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
              phase4_swap phase4_decide phase4_propagate
            simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
              not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
              and_self, if_true, h_no_swap, hOdd, hj_med, hi_no_med,
              hj_timer_one, hi_max, h_post_diff, hj_opinion]
            split_ifs <;> simp_all
          · -- i not at max → pre j.timer = 0
            have hi_no_max : (D i).1.rank.val + 1 ≠ n := hi_max
            have hj_timer_zero : (D j).1.timer = 0 := by
              by_contra h
              unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
                phase4_swap phase4_decide phase4_propagate at h1_res'
              simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
                not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
                and_self, if_true, h_no_swap, hj_med, hi_no_med, hOdd, hi_no_max] at h1_res'
              split_ifs at h1_res' <;> simp_all
            unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
              phase4_swap phase4_decide phase4_propagate
            simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
              not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
              and_self, if_true, h_no_swap, hOdd, hj_med, hi_no_med,
              hj_timer_zero, hi_no_max, h_post_diff, hj_opinion]
            split_ifs <;> simp_all
        have h_post_i : (D.step P i j i).1 =
            { (D i).1 with
                answer := opinionToAnswer (D j).2
                role := .Resetting
                leader := .L
                resetcount := Rmax } := by
          rw [h_fst]
          show (transitionPEM n Rmax Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1 = _
          rw [htr]
        have h_post_j : (D.step P i j j).1 =
            { (D j).1 with
                role := .Resetting
                leader := .L
                resetcount := Rmax
                answer := opinionToAnswer (D j).2 } := by
          rw [h_snd]
          show (transitionPEM n Rmax Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2 = _
          rw [htr]
        have h_post_others : ∀ w, w ≠ i → w ≠ j → (D.step P i j w) = D w := by
          intro w hw hwj; unfold Config.step; simp [hij, hw, hwj]
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
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
              Finset.mem_insert, Finset.mem_singleton, not_or]
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
        -- Build CRS with j as seed
        refine ⟨⟨j, ?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [h_post_j]
        · rw [h_post_j]; have : n - 2 < Rmax := by omega
          exact lt_of_le_of_lt h_nrc this
        · rw [h_post_j]
        · rw [h_post_j, h_maj, hj_opinion]
        · intro w hw_res
          by_cases hwi : w = i
          · subst hwi; rw [h_post_i]
            refine ⟨?_, ?_⟩
            · simp; omega
            · rw [h_maj, hj_opinion]
          · by_cases hwj : w = j
            · subst hwj; rw [h_post_j]
              refine ⟨?_, ?_⟩
              · simp; omega
              · rw [h_maj, hj_opinion]
            · exfalso
              have hw_unchanged := h_post_others w hwi hwj
              rw [show (D.step P i j w).1 = (D w).1 from
                congrArg Prod.fst hw_unchanged] at hw_res
              have hw_settled := hS.allSettled w
              rw [hw_settled] at hw_res
              exact Role.noConfusion hw_res


end SSEM
