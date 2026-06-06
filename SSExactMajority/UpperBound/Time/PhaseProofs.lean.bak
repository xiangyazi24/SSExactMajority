import SSExactMajority.UpperBound.Time.Bridge

namespace SSEM

open scoped ENNReal

/-! ### Phase bound proofs (Lemma 6 + Lemma 9+11)

The end-to-end composition is conditional on two phase E[T] bounds:
- hRankBound (Lemma 6): E[T to InSrank ∧ timer≥35 ∧ timer-bounded] ≤ Rmax·n²
- hConsensusBound (Lemma 9+11): E[T to consensus from InSswap+timer] ≤ 10·Rmax·n²

Strategy for hConsensusBound (ChatGPT "exit = progress" design):
Define DecisionProgress := MedianAnswerCorrect ∨ CorrectResetSeed.
The exit from LiveSwap is absorbed as progress (not failure).
Chain: InSswap → DecisionProgress → CorrectSeed → Epidemic → Consensus.

For odd n: exit is deterministically good progress (phase4_decide sets
median answer at the same step as the potential reset).
For even n: requires the (lower-median, upper-median) decision interaction
to happen before timer exhaustion (probabilistic, high probability). -/

/-- Strengthened DecisionProgress: carries enough invariants so the downstream
median-correct-to-consensus stage can directly apply.  The three disjuncts:
* `IsConsensusConfig` (terminal goal),
* `CorrectResetSeed` (reset epidemic ready),
* Full Sdec phase package: InSswap + MedCorrect + live timer + timer-bounded. -/
def DecisionProgress (Rmax : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  IsConsensusConfig C ∨ CorrectResetSeed C ∨
  (InSswap C ∧ MedianAnswerCorrect C ∧ MedianTimerAtLeast 1 C ∧
    IsTimerBoundedConfig (7 * (Rmax + 4)) C)

/-! Strategy sketch for hConsensusBound using the bridge lemma:

Step 1: E[T from InSswap to DecisionProgress] ≤ n(n-1)
  Use expectedHittingTime_mono_goal on PEM_expected_Tswap_..._or_exit_le
  (needs exit_target_subset_DecisionProgress — protocol-specific)

Step 2: E[T from DecisionProgress to IsConsensusConfig]
  Case MedianAnswerCorrect:
    Use epidemic_timer_branch_to_consensus (deterministic) +
    expectedHittingTime_le_of_deterministic_descent (bridge lemma)
    → E[T] ≤ wrongAnswerCount · n(n-1) ≤ n · n(n-1) = n²(n-1)
  Case CorrectResetSeed:
    Use reset epidemic propagation (nonResettingCount descent)
    → E[T] ≤ nonResettingCount · n(n-1) ≤ n · n(n-1) = n²(n-1)

Step 3: Strong Markov composition
  E[T to consensus] ≤ n(n-1) + n²(n-1) ≤ 2n³ ≤ 10·Rmax·n²
  (since Rmax ≥ n → 10·Rmax·n² ≥ 10n³ ≥ 2n³) -/

/-! General step properties from InSswap under PEMProtocolCoupled.
From InSswap (all Settled, distinct ranks, sorted inputs), any step:
1. Preserves rank at every position (no swap, rankDelta = identity)
2. Timer at every position is ≤ pre-step timer (timer only decrements)
These are the universal step properties needed by the variable descent. -/

theorem step_rank_preserved_of_InSswap
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (w : Fin n) :
    (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j w).1.rank =
      (D w).1.rank := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  by_cases hij : i = j
  · subst hij; simp [Config.step]
  · have hsi := hS.toInSrank.allSettled i
    have hsj := hS.toInSrank.allSettled j
    have hne := fun h : (D i).1.rank = (D j).1.rank => hij (hS.toInSrank.ranks_inj h)
    have h_no_swap := hS.swap_condition_false i j
    have h_rank := transitionPEM_rank_of_no_swap (trank := Rmax) (Rmax := Rmax)
      (rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hsi hsj h_no_swap hne
    by_cases hwi : w = i
    · rw [hwi]
      have h_fst := Config.step_fst_state P D hij
      exact congrArg AgentState.rank h_fst ▸ h_rank.1
    · by_cases hwj : w = j
      · rw [hwj]
        have h_snd := Config.step_snd_state P D hij (Ne.symm hij)
        exact congrArg AgentState.rank h_snd ▸ h_rank.2
      · -- bystander
        unfold Config.step; simp [hij, hwi, hwj]

set_option maxHeartbeats 8000000 in
theorem step_timer_le_of_InSswap
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (w : Fin n) :
    (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j w).1.timer ≤
      (D w).1.timer := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  by_cases hij : i = j
  · subst hij; simp [Config.step]
  · by_cases hwi : w = i
    · rw [hwi]
      have h_fst := Config.step_fst_state P D hij
      rw [show (D.step P i j i).1.timer = ((P.δ (D i, D j)).1).timer from
        congrArg AgentState.timer h_fst]
      -- Unfold P.δ = transitionPEM and show timer ≤
      show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (D i, D j)).1.timer ≤ (D i).1.timer
      have hsi := hS.toInSrank.allSettled i
      have hsj := hS.toInSrank.allSettled j
      have hne := fun h : (D i).1.rank = (D j).1.rank => hij (hS.toInSrank.ranks_inj h)
      have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hne
      have h_no_swap := hS.swap_condition_false i j
      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
        phase4_swap phase4_decide phase4_propagate
      simp only [hRD, hsi, hsj, ne_eq,
        role_settled_ne_resetting,
        not_true_eq_false, not_false_eq_true,
        false_and, and_false, if_false,
        and_self, if_true, h_no_swap]
      by_cases hpar : n % 2 = 0
      · simp only [hpar, if_true]
        split_ifs <;> dsimp only [] <;> omega
      · simp only [hpar, if_false]
        split_ifs <;> dsimp only [] <;> omega
    · by_cases hwj : w = j
      · rw [hwj]
        have h_snd := Config.step_snd_state P D hij (Ne.symm hij)
        rw [show (D.step P i j j).1.timer = ((P.δ (D i, D j)).2).timer from
          congrArg AgentState.timer h_snd]
        show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
          (D i, D j)).2.timer ≤ (D j).1.timer
        have hsi := hS.toInSrank.allSettled i
        have hsj := hS.toInSrank.allSettled j
        have hne := fun h : (D i).1.rank = (D j).1.rank => hij (hS.toInSrank.ranks_inj h)
        have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hne
        have h_no_swap := hS.swap_condition_false i j
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate
        simp only [hRD, hsi, hsj, ne_eq,
          role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true,
          false_and, and_false, if_false,
          and_self, if_true, h_no_swap]
        by_cases hpar : n % 2 = 0
        · simp only [hpar, if_true]
          split_ifs <;> dsimp only [] <;> omega
        · simp only [hpar, if_false]
          split_ifs <;> dsimp only [] <;> omega
      · -- bystander
        unfold Config.step; simp [hij, hwi, hwj]

/-! From InSswap, if the step output is also InSswap (no reset fired),
then the answer at position w is either unchanged (bystander) or
opinionToAnswer(input) (median agent via phase4_decide). For median
agents, opinionToAnswer(input) = majorityAnswer (from InSswap sorted). -/
set_option maxHeartbeats 16000000 in
theorem step_median_answer_of_InSswap_both
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (hS' : InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j))
    (hM : MedianAnswerCorrect D) :
    MedianAnswerCorrect (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hmaj : majorityAnswer (D.step P i j) = majorityAnswer D := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j
  intro ν hν; rw [hmaj]
  have hν_pre : (D ν).1.rank.val + 1 = ceilHalf n := by
    rw [← step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) hn0 hS ν]; exact hν
  -- XHUANG_PROOF_V2_SENTINEL: do not overwrite
  by_cases hij : i = j
  · subst hij; simp [Config.step]; exact hM ν hν_pre
  have hsi := hS.toInSrank.allSettled i
  have hsj := hS.toInSrank.allSettled j
  have hrij : (D i).1.rank ≠ (D j).1.rank :=
    fun h => hij (hS.toInSrank.ranks_inj h)
  have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij
  have h_no_swap := hS.swap_condition_false i j
  have h_tie_outT : ∀ (μ ν' : Fin n),
      (D μ).1.rank.val + 1 = n / 2 → (D ν').1.rank.val + 1 = n / 2 + 1 →
      n % 2 = 0 → (D μ).2 ≠ (D ν').2 → majorityAnswer D = .outT := by
    intro μ ν' hμR hν'R hpar hdis
    have h_sum := nAOf_add_nBOf D
    have hnA : nAOf D = n / 2 := by
      rcases hxμ : (D μ).2 with _ | _
      · have h1 : (D μ).1.rank.val < nAOf D := (hS.input_rank μ).mp hxμ
        have hxν' : (D ν').2 = Opinion.B := by
          cases hν2 : (D ν').2 with
          | A => exfalso; apply hdis; rw [hxμ, hν2]
          | B => rfl
        have h2 : ¬ ((D ν').1.rank.val < nAOf D) := by
          intro h; have := (hS.input_rank ν').mpr h
          rw [hxν'] at this; cases this
        omega
      · have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
          intro h; have := (hS.input_rank μ).mpr h
          rw [hxμ] at this; cases this
        have hxν' : (D ν').2 = Opinion.A := by
          cases hν2 : (D ν').2 with
          | A => rfl
          | B => exfalso; apply hdis; rw [hxμ, hν2]
        have h2 : (D ν').1.rank.val < nAOf D := (hS.input_rank ν').mp hxν'
        omega
    have hnB : nBOf D = n / 2 := by omega
    unfold majorityAnswer; simp [hnA, hnB]
  have h_agree_majA : ∀ (μ ν' : Fin n),
      (D μ).1.rank.val + 1 = n / 2 → (D ν').1.rank.val + 1 = n / 2 + 1 →
      n % 2 = 0 → (D μ).2 = (D ν').2 → (D μ).2 = Opinion.A →
      nAOf D > nBOf D := by
    intro μ ν' hμR hν'R hpar hag hA
    have h_sum := nAOf_add_nBOf D
    have hν'A : (D ν').2 = Opinion.A := by rw [← hag]; exact hA
    have hν'_lt : (D ν').1.rank.val < nAOf D := (hS.input_rank ν').mp hν'A
    omega
  have h_agree_majB : ∀ (μ ν' : Fin n),
      (D μ).1.rank.val + 1 = n / 2 → (D ν').1.rank.val + 1 = n / 2 + 1 →
      n % 2 = 0 → (D μ).2 = (D ν').2 → (D μ).2 = Opinion.B →
      nBOf D > nAOf D := by
    intro μ ν' hμR hν'R hpar hag hB
    have h_sum := nAOf_add_nBOf D
    have hμB : (D μ).2 = Opinion.B := hB
    have hμ_not_A : ¬ ((D μ).1.rank.val < nAOf D) := by
      intro h; have := (hS.input_rank μ).mpr h
      rw [hμB] at this; cases this
    omega
  by_cases hνi : ν = i
  · subst hνi
    have h_fst := Config.step_fst_state P D hij
    rw [show (D.step P ν j ν).1.answer = ((P.δ (D ν, D j)).1).answer from
      congrArg AgentState.answer h_fst]
    show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
      (D ν, D j)).1.answer = majorityAnswer D
    have hrank_νj : (D ν).1.rank.val ≠ (D j).1.rank.val := by
      intro h; apply hij
      exact hS.toInSrank.ranks_inj (Fin.ext h)
    by_cases hpar : n % 2 = 0
    · have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
      have hνR : (D ν).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hν_pre
      have hνR_ceil : (D ν).1.rank.val + 1 = ceilHalf n := hν_pre
      have hN_ne1 : ¬ (n / 2 + 1 = n / 2) := by omega
      have hN_ne2 : ¬ (n / 2 = n / 2 + 1) := by omega
      by_cases hjR : (D j).1.rank.val + 1 = n / 2 + 1
      · by_cases hxeq : (D ν).2 = (D j).2
        · have htr := transitionPEM_at_median_pair_even_agreed_inputs
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            (rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
              (Dmax := Dmax) (hn := hn0)) hsi hsj hpar hνR hjR hxeq hn4
          rw [show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D ν, D j)).1.answer = opinionToAnswer (D ν).2 from
            congrArg AgentState.answer (congrArg Prod.fst htr)]
          exact opinionToAnswer_lower_median_eq_majorityAnswer_even
            hS hνR hpar (by
              rcases hx : (D ν).2 with _ | _
              · have := h_agree_majA ν j hνR hjR hpar hxeq hx; omega
              · have := h_agree_majB ν j hνR hjR hpar hxeq hx; omega)
        · have h_no_swap_disagree : ¬ ((D ν).2 = Opinion.B ∧ (D j).2 = Opinion.A) := by
            intro ⟨hxνB, hxjA⟩
            have h_nA_lo : ¬ ((D ν).1.rank.val < nAOf D) := by
              intro h; have := (hS.input_rank ν).mpr h
              rw [hxνB] at this; cases this
            have h_nA_hi : (D j).1.rank.val < nAOf D := (hS.input_rank j).mp hxjA
            omega
          have htr := transitionPEM_at_median_pair_even_disagreed_inputs
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            (rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
              (Dmax := Dmax) (hn := hn0)) hsi hsj hpar hνR hjR hxeq
            h_no_swap_disagree hn4
          rw [show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D ν, D j)).1.answer = .outT from
            congrArg AgentState.answer (congrArg Prod.fst htr)]
          exact (h_tie_outT ν j hνR hjR hpar hxeq).symm
      · have hM_ν := hM ν hν_pre
        have hjR_no_lower : ¬ ((D j).1.rank.val + 1 = n / 2) := by
          intro h; apply hrank_νj; omega
        have hjR_no_med_ceil : ¬ ((D j).1.rank.val + 1 = ceilHalf n) := by
          rw [hceil]; exact hjR_no_lower
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate
        simp only [hRD, hsi, hsj, ne_eq,
          role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true,
          false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hpar, hνR, hjR, hN_ne1, hN_ne2,
          hνR_ceil, hjR_no_lower, hjR_no_med_ceil]
        split_ifs <;> exact hM_ν
    · have hjR_no_med : ¬ ((D j).1.rank.val + 1 = ceilHalf n) := by
        intro h; apply hrank_νj
        have : (D ν).1.rank.val + 1 = (D j).1.rank.val + 1 := by rw [hν_pre, h]
        omega
      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
        phase4_swap phase4_decide phase4_propagate
      simp only [hRD, hsi, hsj, ne_eq,
        role_settled_ne_resetting,
        not_true_eq_false, not_false_eq_true,
        false_and, and_false, if_false,
        and_self, if_true, h_no_swap, hpar, hν_pre, hjR_no_med]
      have hOdd := opinionToAnswer_median_eq_majorityAnswer_odd hS hν_pre hpar
      split_ifs <;> exact hOdd
  by_cases hνj : ν = j
  · subst hνj
    have h_snd := Config.step_snd_state P D hij (Ne.symm hij)
    rw [show (D.step P i ν ν).1.answer = ((P.δ (D i, D ν)).2).answer from
      congrArg AgentState.answer h_snd]
    show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
      (D i, D ν)).2.answer = majorityAnswer D
    have hrank_iν : (D i).1.rank.val ≠ (D ν).1.rank.val := by
      intro h; apply hij
      exact hS.toInSrank.ranks_inj (Fin.ext h)
    by_cases hpar : n % 2 = 0
    · have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
      have hνR : (D ν).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hν_pre
      have hνR_ceil : (D ν).1.rank.val + 1 = ceilHalf n := hν_pre
      have hN_ne1 : ¬ (n / 2 + 1 = n / 2) := by omega
      have hN_ne2 : ¬ (n / 2 = n / 2 + 1) := by omega
      by_cases hiR : (D i).1.rank.val + 1 = n / 2 + 1
      · have hiR_no_med : ¬ ((D i).1.rank.val + 1 = ceilHalf n) := by
          rw [hceil]; omega
        have hiR_no_max : ¬ ((D i).1.rank.val + 1 = n) := by omega
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate
        simp only [hRD, hsi, hsj, ne_eq,
          role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true,
          false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hpar, hνR, hiR, hN_ne1, hN_ne2,
          hνR_ceil, hiR_no_med, hiR_no_max]
        by_cases hxeq : (D i).2 = (D ν).2
        · simp only [hxeq, if_true]
          have hAns := opinionToAnswer_lower_median_eq_majorityAnswer_even
            hS hνR hpar (by
              rcases hx : (D ν).2 with _ | _
              · have := h_agree_majA ν i hνR hiR hpar hxeq.symm hx; omega
              · have := h_agree_majB ν i hνR hiR hpar hxeq.symm hx; omega)
          split_ifs <;> exact hAns
        · have hxsym : (D ν).2 ≠ (D i).2 := Ne.symm hxeq
          simp only [hxsym, if_false]
          have hOutT := (h_tie_outT ν i hνR hiR hpar (Ne.symm hxeq)).symm
          split_ifs <;> exact hOutT
      · have hM_ν := hM ν hν_pre
        have hiR_ne_med : ¬ ((D i).1.rank.val + 1 = n / 2) := by
          intro h; apply hrank_iν
          have : (D i).1.rank.val + 1 = (D ν).1.rank.val + 1 := by rw [h, hνR]
          omega
        have hiR_ne_med_ceil : ¬ ((D i).1.rank.val + 1 = ceilHalf n) := by
          rw [hceil]; exact hiR_ne_med
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate
        simp only [hRD, hsi, hsj, ne_eq,
          role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true,
          false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hpar, hνR, hiR, hN_ne1, hN_ne2,
          hνR_ceil, hiR_ne_med, hiR_ne_med_ceil]
        split_ifs <;> exact hM_ν
    · have hiR_no_med : ¬ ((D i).1.rank.val + 1 = ceilHalf n) := by
        intro h; apply hrank_iν
        have : (D i).1.rank.val + 1 = (D ν).1.rank.val + 1 := by rw [h, hν_pre]
        omega
      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
        phase4_swap phase4_decide phase4_propagate
      simp only [hRD, hsi, hsj, ne_eq,
        role_settled_ne_resetting,
        not_true_eq_false, not_false_eq_true,
        false_and, and_self, if_false,
        and_false, if_true, h_no_swap, hpar, hν_pre, hiR_no_med]
      have hOdd := opinionToAnswer_median_eq_majorityAnswer_odd hS hν_pre hpar
      split_ifs <;> exact hOdd
  · have hbyst : D.step P i j ν = D ν := by
      unfold Config.step; simp [hij, hνi, hνj]
    rw [show (D.step P i j ν).1.answer = (D ν).1.answer from
      congrArg (fun x => x.1.answer) hbyst]
    exact hM ν hν_pre

/-! Phase C.2: Median-correct sub-phase (timer drain → seed → epidemic).
From InSswap + MedianAnswerCorrect + timer≥1 + wrongAnswer > 0:
E[T to consensus] ≤ O(Rmax·n²). Uses epidemic reachability. -/

/-! Phase C.2 sub-decomposition (median correct → consensus):

Sub-phase C.2a: Timer drain. From InSswap + MedianCorrect + timer≥1:
  potential = medianTimer, descent at (median,max) pair.
  E[T to timer=0 ∨ consensus] ≤ timer · n(n-1) ≤ 7(Rmax+4) · n(n-1)

Sub-phase C.2b: Reset seed creation. When timer=0 + answers disagree:
  One (median,max) interaction triggers reset → CorrectResetSeed.
  E[T to CorrectResetSeed ∨ consensus] ≤ n(n-1)

Sub-phase C.2c: Epidemic propagation. From CorrectResetSeed:
  potential = nonResettingCount, descent via propagate-reset.
  E[T to all-resetting ∨ consensus] ≤ n · n(n-1)

Sub-phase C.2d: Re-ranking + consensus. From all-resetting with correct answer:
  potential = resetFuel → ranking → InSswap → consensus.
  E[T] ≤ O(Rmax · n²)

Total: O(Rmax · n²). -/

/-! Stage 1: Timer drain. Inv = InSswap ∧ MedianCorrect ∧ timer≥1,
φ = medianTimer. Each (median,max) step decreases timer. -/

/-! φ for timer drain: max timer across all median-rank agents.
In InSswap there is exactly one, but we define it for all configs. -/
noncomputable def maxMedianTimer (C : Config (AgentState n) Opinion n) : ℕ :=
  Finset.sup Finset.univ
    (fun μ : Fin n => if (C μ).1.rank.val + 1 = ceilHalf n then (C μ).1.timer else 0)

set_option maxHeartbeats 16000000 in
theorem PEM_expected_timer_drain
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (hTimerLo : MedianTimerAtLeast 1 C)
    (hTimerHi : IsTimerBoundedConfig (7 * (Rmax + 4)) C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
        (InSswap D ∧ MedianAnswerCorrect D ∧ ¬ MedianTimerAtLeast 1 D)) ≤
      ((7 * (Rmax + 4) * n * (n - 1) : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  set Goal := fun D : Config (AgentState n) Opinion n =>
    IsConsensusConfig D ∨ CorrectResetSeed D ∨
      (InSswap D ∧ MedianAnswerCorrect D ∧ ¬ MedianTimerAtLeast 1 D)
  set Inv := fun D : Config (AgentState n) Opinion n =>
    InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
  have hBridge := Probability.expectedHittingTime_le_of_deterministic_descent
    P (by omega : 2 ≤ n) C Goal Inv maxMedianTimer
    ⟨hSswap, hMedCorrect, hTimerLo⟩
    (by -- hZeroGoal: Inv D ∧ maxMedianTimer D = 0 → Goal D
        -- Inv includes MedianTimerAtLeast 1 → timer ≥ 1 at median.
        -- But maxMedianTimer = 0 → timer = 0 at median. Contradiction → vacuously true.
        intro D ⟨hSwap_D, _, hT_D⟩ h0
        exfalso
        have hInj := hSwap_D.ranks_inj
        have hSurj : Function.Surjective (fun v => (D v).1.rank) :=
          Finite.surjective_of_injective hInj
        have hCeil : (ceilHalf n : ℕ) - 1 < n := by unfold ceilHalf; omega
        obtain ⟨μ, hμ⟩ := hSurj ⟨ceilHalf n - 1, hCeil⟩
        have hμ_med : (D μ).1.rank.val + 1 = ceilHalf n := by
          have hval : (D μ).1.rank.val = ceilHalf n - 1 := congr_arg Fin.val hμ
          have hceil_pos : 0 < ceilHalf n := by unfold ceilHalf; omega
          omega
        have h1 := hT_D μ hμ_med
        have h2 : (D μ).1.timer ≤ maxMedianTimer D := by
          unfold maxMedianTimer
          exact Finset.le_sup_of_le (Finset.mem_univ μ) (by simp [hμ_med])
        omega)
    (by -- hInvStep: Inv D → ¬Goal D → ∀ i j, Inv(step) ∨ Goal(step)
        -- Key: ¬Inv → (¬InSswap ∨ ¬timer≥1) → Goal (third disjunct)
        -- MedianCorrect is preserved under InSswap (phase4_decide is idempotent,
        -- phase4_propagate copies FROM median)
        intro D ⟨hS, hM, hT⟩ hG i j
        by_cases hS' : InSswap (D.step P i j)
        · by_cases hT' : MedianTimerAtLeast 1 (D.step P i j)
          · by_cases hM' : MedianAnswerCorrect (D.step P i j)
            · exact Or.inl ⟨hS', hM', hT'⟩
            · exact absurd (step_median_answer_of_InSswap_both hn0 hn4 hS hS' hM) hM'
          · -- InSswap preserved, timer dropped below 1 → third disjunct
            have hM' := step_median_answer_of_InSswap_both hn0 hn4 hS hS' hM
            exact Or.inr (Or.inr (Or.inr ⟨hS', hM', hT'⟩))
        · -- InSswap broke → CorrectResetSeed
          exact Or.inr (Or.inr (Or.inl
            (sorry /- forward ref: step_InSswap_break_creates_CorrectResetSeed -/))))
    (by -- hNonincrease: maxMedianTimer doesn't increase
        intro D ⟨hS, hM, hT⟩ hG i j
        unfold maxMedianTimer
        apply Finset.sup_le
        intro μ _
        split_ifs with hμ_med
        · -- μ is a median agent post-step: timer ≤ maxMedianTimer D
          by_cases hij : i = j
          · -- self-interaction: no-op
            subst hij; simp only [Config.step, ite_true] at hμ_med ⊢
            exact Finset.le_sup_of_le (Finset.mem_univ μ) (by simp [hμ_med])
          · by_cases hμi : μ = i
            · -- μ = i: rank preserved, timer ≤
              rw [hμi]
              have hrank : (D.step P i j i).1.rank = (D i).1.rank :=
                step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
                  (Dmax := Dmax) hn0 hS i
              have hμ_pre : (D i).1.rank.val + 1 = ceilHalf n := by rw [← hrank]; rwa [hμi] at hμ_med
              calc (D.step P i j i).1.timer
                  ≤ (D i).1.timer :=
                    step_timer_le_of_InSswap (Rmax := Rmax) (Emax := Emax)
                      (Dmax := Dmax) hn0 hS i
                _ ≤ maxMedianTimer D :=
                    Finset.le_sup_of_le (Finset.mem_univ i) (by simp [maxMedianTimer, hμ_pre])
            · by_cases hμj : μ = j
              · rw [hμj]
                have hrank : (D.step P i j j).1.rank = (D j).1.rank :=
                  step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
                    (Dmax := Dmax) hn0 hS j
                have hμ_pre : (D j).1.rank.val + 1 = ceilHalf n := by rw [← hrank]; rwa [hμj] at hμ_med
                calc (D.step P i j j).1.timer
                    ≤ (D j).1.timer :=
                      step_timer_le_of_InSswap (Rmax := Rmax) (Emax := Emax)
                        (Dmax := Dmax) hn0 hS j
                  _ ≤ maxMedianTimer D :=
                      Finset.le_sup_of_le (Finset.mem_univ j) (by simp [maxMedianTimer, hμ_pre])
              · -- bystander: unchanged
                have hbyst : D.step P i j μ = D μ := by
                  unfold Config.step; simp [hij, hμi, hμj]
                rw [show (D.step P i j μ).1.timer = (D μ).1.timer from
                  congrArg (fun x => x.1.timer) hbyst]
                rw [show (D.step P i j μ).1.rank = (D μ).1.rank from
                  congrArg (fun x => x.1.rank) hbyst] at hμ_med
                exact Finset.le_sup_of_le (Finset.mem_univ μ) (by simp [hμ_med])
        · exact Nat.zero_le _)
    (by -- hDescent: ∃ (median,max) pair that decrements timer
        intro D ⟨hS, hM, hT⟩ hG hφ
        have hn_pos : 0 < n := by omega
        obtain ⟨μ, hμ_med⟩ := hS.toInSrank.exists_median hn_pos
        -- Get max-rank agent via surjectivity
        have hsurj : Function.Surjective (fun v => (D v).1.rank) :=
          Finite.injective_iff_surjective.mp hS.toInSrank.ranks_inj
        have hn_bound : n - 1 < n := by omega
        obtain ⟨v, hv_eq⟩ := hsurj ⟨n - 1, hn_bound⟩
        have hv_max : (D v).1.rank.val + 1 = n := by
          have h := congrArg Fin.val hv_eq
          simp only [Fin.val_mk] at h
          omega
        have huv : μ ≠ v := by
          intro h; subst h
          have : ceilHalf n = n := by omega
          have : ceilHalf n ≤ (n + 1) / 2 := by unfold ceilHalf; omega
          omega
        refine ⟨μ, v, huv, ?_⟩
        -- Case split on median timer value
        have hTimerPos : 1 ≤ (D μ).1.timer := hT μ hμ_med
        by_cases hTimer2 : 2 ≤ (D μ).1.timer
        · -- timer ≥ 2: Inv preserved + maxMedianTimer strictly decreased
          have hsi := hS.toInSrank.allSettled μ
          have hsv := hS.toInSrank.allSettled v
          have hrij : (D μ).1.rank ≠ (D v).1.rank :=
            fun h => huv (hS.toInSrank.ranks_inj h)
          have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
            (Dmax := Dmax) (hn := hn0) (D μ).1 (D v).1 hsi hsv hrij
          have h_no_swap := hS.swap_condition_false μ v
          have hv_not_med : (D v).1.rank.val + 1 ≠ ceilHalf n := by
            have h1 : ceilHalf n ≤ (n + 1) / 2 := by unfold ceilHalf; omega
            omega
          have hμ_not_max : (D μ).1.rank.val + 1 ≠ n := by
            have h1 : ceilHalf n < n := by unfold ceilHalf; omega
            omega
          have hN_ne_ceil : ¬ (n = ceilHalf n) := by
            have h1 : ceilHalf n < n := by unfold ceilHalf; omega
            omega
          -- Per Zinan: use `show` to expose the post-reduction goal form
          have hμ_timer_post : (D.step P μ v μ).1.timer = (D μ).1.timer - 1 := by
            have h_fst := Config.step_fst_state P D huv
            rw [show (D.step P μ v μ).1.timer = ((P.δ (D μ, D v)).1).timer from
              congrArg AgentState.timer h_fst]
            show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
              (D μ, D v)).1.timer = (D μ).1.timer - 1
            unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
              phase4_swap phase4_decide phase4_propagate
            simp only [hRD, hsi, hsv, ne_eq, role_settled_ne_resetting,
              not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
              and_self, if_true, h_no_swap, hμ_med, hv_max, hv_not_med, hN_ne_ceil]
            by_cases hpar : n % 2 = 0
            · simp only [hpar, if_true]
              split_ifs <;> dsimp only [] <;> omega
            · simp only [hpar, if_false]
              split_ifs <;> dsimp only [] <;> omega
          have hμ_role_post : (D.step P μ v μ).1.role = .Settled := by
            have h_fst := Config.step_fst_state P D huv
            rw [show (D.step P μ v μ).1.role = ((P.δ (D μ, D v)).1).role from
              congrArg AgentState.role h_fst]
            show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
              (D μ, D v)).1.role = .Settled
            unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
              phase4_swap phase4_decide phase4_propagate
            simp only [hRD, hsi, hsv, ne_eq, role_settled_ne_resetting,
              not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
              and_self, if_true, h_no_swap, hμ_med, hv_max, hv_not_med, hN_ne_ceil]
            by_cases hpar : n % 2 = 0 <;> simp only [*, if_true, if_false] <;>
              (first | exact hsi | (split_ifs <;> (first | exact hsi | (exfalso; simp_all; omega))))
          have hv_state_post : (D.step P μ v v).1 = (D v).1 := by
            have h_snd := Config.step_snd_state P D huv (Ne.symm huv)
            rw [show (D.step P μ v v).1 = ((P.δ (D μ, D v)).2) from h_snd]
            show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
              (D μ, D v)).2 = (D v).1
            unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
              phase4_swap phase4_decide phase4_propagate
            simp only [hRD, hsi, hsv, ne_eq, role_settled_ne_resetting,
              not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
              and_self, if_true, h_no_swap, hμ_med, hv_max, hv_not_med, hN_ne_ceil,
              hμ_not_max]
            by_cases hpar : n % 2 = 0 <;> simp only [*, if_true, if_false] <;>
              (first | rfl | (split_ifs <;> (first | rfl | (exfalso; simp_all; omega))))
          have h_others : ∀ w, w ≠ μ → w ≠ v → D.step P μ v w = D w := by
            intro w hw hwv; unfold Config.step
            simp [huv, hw, hwv]
          have h_inputs : ∀ w, (D.step P μ v w).2 = (D w).2 := by
            intro w; unfold Config.step
            by_cases hwμ : w = μ
            · rw [hwμ]; simp [huv]
            · by_cases hwv : w = v
              · rw [hwv]; simp [huv, Ne.symm huv]
              · simp [huv, hwμ, hwv]
          have h_rank_w : ∀ w, (D.step P μ v w).1.rank = (D w).1.rank :=
            fun w => step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
              (Dmax := Dmax) hn0 hS w
          have h_nA : nAOf (D.step P μ v) = nAOf D := by
            unfold nAOf Config.agentsWithInput Config.inputOf
            congr 1; ext w
            simp only [Finset.mem_filter]
            refine ⟨fun ⟨hm, h⟩ => ⟨hm, by rw [h_inputs] at h; exact h⟩,
                    fun ⟨hm, h⟩ => ⟨hm, by rw [h_inputs]; exact h⟩⟩
          have hSwap' : InSswap (D.step P μ v) := by
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · intro w
              by_cases hwμ : w = μ
              · rw [hwμ]; exact hμ_role_post
              · by_cases hwv : w = v
                · rw [hwv,
                    show (D.step P μ v v).1 = (D v).1 from hv_state_post]
                  exact hsv
                · rw [show (D.step P μ v w).1 = (D w).1 from
                    congrArg Prod.fst (h_others w hwμ hwv)]
                  exact hS.toInSrank.allSettled w
            · intro w1 w2 heq
              simp only [h_rank_w] at heq
              exact hS.toInSrank.ranks_inj heq
            · intro w
              rw [h_inputs, h_rank_w, h_nA]
              exact hS.input_rank w
          have hMed' : MedianAnswerCorrect (D.step P μ v) :=
            step_median_answer_of_InSswap_both hn0 hn4 hS hSwap' hM
          have hTimer' : MedianTimerAtLeast 1 (D.step P μ v) := by
            intro w hw_post
            have hw_pre : (D w).1.rank.val + 1 = ceilHalf n := by
              rw [← h_rank_w w]; exact hw_post
            have hwμ : w = μ := by
              apply hS.toInSrank.ranks_inj
              apply Fin.ext
              have h1 : (D w).1.rank.val + 1 = (D μ).1.rank.val + 1 := by
                rw [hw_pre, hμ_med]
              omega
            rw [hwμ, hμ_timer_post]; omega
          refine Or.inl ⟨⟨hSwap', hMed', hTimer'⟩, ?_⟩
          -- maxMedianTimer strictly decreased
          have h_max_eq : ∀ {C' : Config (AgentState n) Opinion n}
              (hC' : InSswap C') (μ' : Fin n)
              (hμ' : (C' μ').1.rank.val + 1 = ceilHalf n),
              maxMedianTimer C' = (C' μ').1.timer := by
            intro C' hC' μ' hμ'
            unfold maxMedianTimer
            apply le_antisymm
            · apply Finset.sup_le
              intro ν _
              split_ifs with hν_med
              · have hval : (C' ν).1.rank.val = (C' μ').1.rank.val := by
                  have : (C' ν).1.rank.val + 1 = (C' μ').1.rank.val + 1 := by
                    rw [hν_med, hμ']
                  omega
                have : ν = μ' := hC'.toInSrank.ranks_inj (Fin.ext hval)
                rw [this]
              · exact Nat.zero_le _
            · refine Finset.le_sup_of_le (Finset.mem_univ μ') ?_
              simp [hμ']
          rw [h_max_eq hSwap' μ (by rw [h_rank_w]; exact hμ_med)]
          rw [h_max_eq hS μ hμ_med]
          rw [hμ_timer_post]
          omega
        · -- timer = 1: step decrements to 0 → Goal
          have hTimer1 : (D μ).1.timer = 1 := by omega
          exact Or.inr (Or.inr (Or.inr (by
            intro ⟨hS', hT'⟩
            have hμ_rank_post : (D.step P μ v μ).1.rank.val + 1 = ceilHalf n := by
              rw [step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
                (Dmax := Dmax) hn0 hS μ]; exact hμ_med
            have h_fst := Config.step_fst_state P D huv
            have hμ_timer_post : (D.step P μ v μ).1.timer = 0 := by
              rw [show (D.step P μ v μ).1.timer = ((P.δ (D μ, D v)).1).timer from
                congrArg AgentState.timer h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D μ, D v)).1.timer = 0
              have hsi := hS.toInSrank.allSettled μ
              have hsv := hS.toInSrank.allSettled v
              have hne := fun h : (D μ).1.rank = (D v).1.rank => huv (hS.toInSrank.ranks_inj h)
              have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
                (Dmax := Dmax) (hn := hn0) (D μ).1 (D v).1 hsi hsv hne
              have h_no_swap := hS.swap_condition_false μ v
              unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
                phase4_swap phase4_decide phase4_propagate
              simp only [hRD, hsi, hsv, ne_eq,
                role_settled_ne_resetting,
                not_true_eq_false, not_false_eq_true,
                false_and, and_false, if_false,
                and_self, if_true, h_no_swap, hμ_med, hv_max, hTimer1]
              by_cases hpar : n % 2 = 0
              · simp only [hpar, if_true]
                split_ifs <;> dsimp only [] <;> omega
              · simp only [hpar, if_false]
                split_ifs <;> dsimp only [] <;> omega
            have h0 := hT' μ hμ_rank_post
            omega))))
  have hMaxTimer : maxMedianTimer C ≤ 7 * (Rmax + 4) := by
    unfold maxMedianTimer
    apply Finset.sup_le
    intro μ _
    split_ifs with h
    · exact hTimerHi μ
    · exact Nat.zero_le _
  calc Probability.expectedHittingTime P (by omega) C Goal
      ≤ ↑(maxMedianTimer C) * ((n * (n - 1) : ℕ) : ENNReal) := hBridge
    _ ≤ ((7 * (Rmax + 4) * n * (n - 1) : ℕ) : ENNReal) := by
        norm_cast
        -- maxMedianTimer C * (n * (n-1)) ≤ 7*(Rmax+4) * n * (n-1)
        -- = 7*(Rmax+4) * (n * (n-1))
        calc maxMedianTimer C * (n * (n - 1))
            ≤ (7 * (Rmax + 4)) * (n * (n - 1)) :=
              Nat.mul_le_mul_right _ hMaxTimer
          _ = 7 * (Rmax + 4) * n * (n - 1) := by ring

/-! ### Protocol-specific helpers for reset trigger -/

/-- When InSswap breaks at a step from an InSswap config with **odd** n, the result
has CorrectResetSeed.  Unlike the MedC-requiring version, this uses the fact that
phase4_decide for odd n ALWAYS sets the median's answer to majorityAnswer within
the step, so the propagation output carries the correct answer. -/
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
    rw [congrArg AgentState.role h_fst]
    exact (transitionPEM_phase4_role_settled_or_resetting
      (n := n) (Rmax := Rmax) (a := ((D i).1, (D j).1))
      (x₀ := (D i).2) (x₁ := (D j).2) hsi hsj).1
  have h_role_j : (D.step P i j j).1.role = .Settled ∨
      (D.step P i j j).1.role = .Resetting := by
    rw [congrArg AgentState.role h_snd]
    exact (transitionPEM_phase4_role_settled_or_resetting
      (n := n) (Rmax := Rmax) (a := ((D i).1, (D j).1))
      (x₀ := (D i).2) (x₁ := (D j).2) hsi hsj).2
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
        have hrank : (D.step P i j w).1.rank = (D w).1.rank :=
          step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
            (Dmax := Dmax) hn0 hS w
        constructor
        · intro hA
          rw [congrArg Fin.val hrank]
          exact (hS.input_rank w).mp hA
        · intro hlt
          rw [congrArg Fin.val hrank] at hlt
          exact (hS.input_rank w).mpr hlt
    · -- j Resetting, i Settled: derive j Resetting from h_role_j
      have hj_res := h_role_j.resolve_left hj_settled
      -- Both must be Resetting (phase4_propagate sets both simultaneously)
      have hi_res : (D.step P i j i).1.role = .Resetting := by
        exfalso
        have h1_set := hi_settled
        have h2_res := hj_res
        have h1_res' : (transitionPEM n Rmax Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2.role = .Resetting := by
          rw [← congrArg AgentState.role h_snd]; exact h2_res
        have h1_set' : (transitionPEM n Rmax Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1.role = .Settled := by
          rw [← congrArg AgentState.role h_fst]; exact h1_set
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
          rw [← congrArg AgentState.role h_fst]; exact h1_res
        have h2_set' : (transitionPEM n Rmax Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2.role = .Settled := by
          rw [← congrArg AgentState.role h_snd]; exact h2_set
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
        rw [← congrArg AgentState.role h_fst]; exact hi_res
      have h2_res' : (transitionPEM n Rmax Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2.role = .Resetting := by
        rw [← congrArg AgentState.role h_snd]; exact hj_res
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
            · rw [congrArg AgentState.role h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.role = _
              rw [h_trace]
            · rw [congrArg AgentState.leader h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.leader = _
              rw [h_trace]
            · rw [congrArg AgentState.resetcount h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.resetcount = _
              rw [h_trace]
            · rw [congrArg AgentState.answer h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.answer = _
              rw [h_trace]; exact hi_opinion
            · rw [congrArg AgentState.role h_snd]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).2.role = _
              rw [h_trace]
            · rw [congrArg AgentState.leader h_snd]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).2.leader = _
              rw [h_trace]
            · rw [congrArg AgentState.resetcount h_snd]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).2.resetcount = _
              rw [h_trace]
            · rw [congrArg AgentState.answer h_snd]
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
            · rw [congrArg AgentState.role h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.role = _
              rw [h_trace]
            · rw [congrArg AgentState.leader h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.leader = _
              rw [h_trace]
            · rw [congrArg AgentState.resetcount h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.resetcount = _
              rw [h_trace]
            · rw [congrArg AgentState.answer h_fst]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).1.answer = _
              rw [h_trace]; exact hi_opinion
            · rw [congrArg AgentState.role h_snd]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).2.role = _
              rw [h_trace]
            · rw [congrArg AgentState.leader h_snd]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).2.leader = _
              rw [h_trace]
            · rw [congrArg AgentState.resetcount h_snd]
              show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (D i, D j)).2.resetcount = _
              rw [h_trace]
            · rw [congrArg AgentState.answer h_snd]
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
            ({ (D i).1 with answer := opinionToAnswer (D j).2, role := .Resetting,
                leader := .L, resetcount := Rmax },
             { (D j).1 with role := .Resetting, leader := .L,
                resetcount := Rmax, answer := opinionToAnswer (D j).2 }) := by
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
            { (D i).1 with answer := opinionToAnswer (D j).2, role := .Resetting,
              leader := .L, resetcount := Rmax } := by
          rw [h_fst]
          show (transitionPEM n Rmax Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1 = _
          rw [htr]
        have h_post_j : (D.step P i j j).1 =
            { (D j).1 with role := .Resetting, leader := .L,
              resetcount := Rmax, answer := opinionToAnswer (D j).2 } := by
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
    rw [congrArg AgentState.role h_fst]
    exact (transitionPEM_phase4_role_settled_or_resetting
      (n := n) (Rmax := Rmax) (a := ((D i).1, (D j).1))
      (x₀ := (D i).2) (x₁ := (D j).2) hsi hsj).1
  -- Role of j post-step
  have h_role_j : (D.step P i j j).1.role = .Settled ∨
      (D.step P i j j).1.role = .Resetting := by
    rw [congrArg AgentState.role h_snd]
    exact (transitionPEM_phase4_role_settled_or_resetting
      (n := n) (Rmax := Rmax) (a := ((D i).1, (D j).1))
      (x₀ := (D i).2) (x₁ := (D j).2) hsi hsj).2
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
        simp only [step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
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
        ({ (D i).1 with answer := (D j).1.answer, role := .Resetting,
            leader := .L, resetcount := Rmax },
         { (D j).1 with role := .Resetting, leader := .L,
            resetcount := Rmax, answer := (D j).1.answer }) := by
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
          { (D i).1 with answer := (D j).1.answer, role := .Resetting,
            leader := .L, resetcount := Rmax } := by
        rw [h_fst]
        show (transitionPEM n Rmax Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1 = _
        rw [htr]
      have h_post_j : (D.step P i j j).1 =
          { (D j).1 with role := .Resetting, leader := .L,
            resetcount := Rmax, answer := (D j).1.answer } := by
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

set_option maxHeartbeats 32000000 in
theorem step_timer_zero_median_wrong_nonupper_creates_CorrectResetSeed
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (hμ_timer : (D μ).1.timer = 0)
    (hμ_correct : (D μ).1.answer = majorityAnswer D)
    (hv_wrong : (D v).1.answer ≠ majorityAnswer D)
    (hv_no_upper : (D v).1.rank.val + 1 ≠ n / 2 + 1) :
    let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
    CorrectResetSeed (D.step P μ v) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  -- Derive auxiliary facts
  have hv_no_med : (D v).1.rank.val + 1 ≠ ceilHalf n := by
    intro h
    apply hμv
    apply hS.toInSrank.ranks_inj
    exact Fin.ext (Nat.add_right_cancel (hμ_med.trans h.symm))
  have h_no_swap := hS.swap_condition_false μ v
  have h_post_diff : (D μ).1.answer ≠ (D v).1.answer := by
    rw [hμ_correct]; exact fun h => hv_wrong h.symm
  -- Compute transition explicitly via parity case
  have htr : transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D μ, D v) =
      ({ (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := (D μ).1.answer },
       { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := (D μ).1.answer }) := by
    by_cases hpar : n % 2 = 0
    · -- Even
      have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
      have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hμ_med
      have hv_not_lower : (D v).1.rank.val + 1 ≠ n / 2 := by
        rw [← hceil]; exact hv_no_med
      have htr_even := propagation_reset_fires_even_lower_timer_zero_no_swap_trace
        (trank := Rmax) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hμv hpar hμ_lower hv_not_lower
        hv_no_upper hμ_timer h_no_swap h_post_diff
      -- htr_even: transitionPEM ... = ({μ.1 with role:=Resetting,...}, {v.1 with role:=Resetting,...,answer:=μ.1.answer})
      -- We need both .1 and .2's `answer` to be (D μ).1.answer
      -- For .1 (μ): the trace gives {μ.1 with role:=Resetting,leader:=L,resetcount:=Rmax}.
      -- This struct update preserves the answer field = (D μ).1.answer.
      rw [htr_even]
    · -- Odd
      have hμ_ans_eq : opinionToAnswer (D μ).2 = (D μ).1.answer := by
        rw [opinionToAnswer_median_eq_majorityAnswer_odd hS hμ_med hpar, hμ_correct]
      have h_post_diff_odd : opinionToAnswer (D μ).2 ≠ (D v).1.answer := by
        rw [hμ_ans_eq]; exact h_post_diff
      have htr_odd := propagation_reset_fires_no_swap_trace
        (trank := Rmax) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hμv hμ_med hv_no_med
        hμ_timer h_no_swap hpar h_post_diff_odd
      rw [htr_odd, hμ_ans_eq]
  -- From htr, derive post-step state at μ and v
  have h_fst := Config.step_fst_state P D hμv
  have h_snd := Config.step_snd_state P D hμv (Ne.symm hμv)
  have h_post_μ : (D.step P μ v μ).1 =
      { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := (D μ).1.answer } := by
    rw [h_fst]
    show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D μ, D v)).1 = _
    rw [htr]
  have h_post_v : (D.step P μ v v).1 =
      { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := (D μ).1.answer } := by
    rw [h_snd]
    show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D μ, D v)).2 = _
    rw [htr]
  -- Other agents unchanged
  have h_post_others : ∀ w, w ≠ μ → w ≠ v → (D.step P μ v w) = D w := by
    intro w hw hwv; unfold Config.step
    simp [hμv, hw, hwv]
  -- majorityAnswer preserved by step
  have h_maj : majorityAnswer (D.step P μ v) = majorityAnswer D := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ v
  -- nonResettingCount post-step ≤ n - 2 (μ and v are Resetting; others are not)
  have h_nrc : nonResettingCount (D.step P μ v) ≤ n - 2 := by
    classical
    unfold nonResettingCount
    -- nonResettingCount counts agents with role ≠ .Resetting
    -- μ and v are Resetting → not counted
    -- All others have role = .Settled (≠ Resetting) → counted
    -- Total: n - 2
    set S := Finset.univ.filter (fun w : Fin n =>
      (D.step P μ v w).1.role ≠ .Resetting)
    have hμ_not : μ ∉ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      rw [h_post_μ]
    have hv_not : v ∉ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      rw [h_post_v]
    have hS_sub : S ⊆ (Finset.univ \ {μ, v}) := by
      intro w hw
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      refine ⟨?_, ?_⟩
      · intro h; rw [h] at hw; exact hμ_not hw
      · intro h; rw [h] at hw; exact hv_not hw
    have hcard : (Finset.univ \ ({μ, v} : Finset (Fin n))).card = n - 2 := by
      have h1 : (Finset.univ : Finset (Fin n)).card = n := Fintype.card_fin n
      have h2 : ({μ, v} : Finset (Fin n)).card = 2 := Finset.card_pair hμv
      have h3 : (Finset.univ \ ({μ, v} : Finset (Fin n))).card =
        (Finset.univ : Finset (Fin n)).card - ({μ, v} : Finset (Fin n)).card :=
        Finset.card_sdiff_of_subset (Finset.subset_univ _)
      rw [h3, h1, h2]
    calc S.card ≤ (Finset.univ \ ({μ, v} : Finset (Fin n))).card :=
            Finset.card_le_card hS_sub
      _ = n - 2 := hcard
  -- Build CorrectResetSeed
  refine ⟨⟨μ, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- (step μ).1.role = .Resetting
    rw [h_post_μ]
  · -- nonResettingCount < (step μ).1.resetcount = Rmax
    rw [h_post_μ]
    have h : n - 2 < Rmax := by omega
    exact lt_of_le_of_lt h_nrc h
  · -- (step μ).1.leader = .L
    rw [h_post_μ]
  · -- (step μ).1.answer = majorityAnswer (step)
    rw [h_post_μ, h_maj, hμ_correct]
  · -- ∀ w Resetting → 0 < resetcount ∧ answer = majorityAnswer
    intro w hw_res
    by_cases hwμ : w = μ
    · subst hwμ
      rw [h_post_μ]
      refine ⟨?_, ?_⟩
      · simp; omega
      · rw [h_maj, hμ_correct]
    · by_cases hwv : w = v
      · subst hwv
        rw [h_post_v]
        refine ⟨?_, ?_⟩
        · simp; omega
        · rw [h_maj, hμ_correct]
      · -- w not μ or v: was Settled, now Settled. Contradicts hw_res.
        exfalso
        have hw_unchanged := h_post_others w hwμ hwv
        rw [show (D.step P μ v w).1 = (D w).1 from
          congrArg Prod.fst hw_unchanged] at hw_res
        have hw_settled := hS.allSettled w
        rw [hw_settled] at hw_res
        exact Role.noConfusion hw_res

/-! Stage 2: Reset trigger. From InSswap + MedianCorrect + timer=0 +
wrongAnswer > 0: trigger_correct_reset_from_InSrank gives a deterministic
pair that creates CorrectResetSeed.
E[T] ≤ n(n-1) via ProbHitWithin_one_lower_bound_of_step. -/

theorem PEM_expected_reset_trigger
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (hWrong : 0 < wrongAnswerCount C)
    (hTimer0 : ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
      (C μ).1.timer = 0) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ CorrectResetSeed D) ≤
      ((n * (n - 1) : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  set Goal := fun D : Config (AgentState n) Opinion n =>
    IsConsensusConfig D ∨ CorrectResetSeed D
  -- Use the invariant-based one-step lemma: the bound only needs to hold
  -- under the InSswap invariant, not for arbitrary configs.
  set Inv := fun D : Config (AgentState n) Opinion n =>
    InSswap D ∧ MedianAnswerCorrect D ∧
      (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n → (D μ).1.timer = 0)
  refine (Probability.expectedHittingTime_le_inv_of_local_one_lower_bound_until_goal
    P (by omega) C Goal Inv ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ?_ ?_ ?_).trans
    (by rw [inv_inv])
  · -- hInv₀: Inv C
    exact ⟨hSswap, hMedCorrect, hTimer0⟩
  · -- hInvStep: Inv D → ¬Goal D → ∀ i j, Inv(step) ∨ Goal(step)
    intro D ⟨hS, hM, hT⟩ _hGoalD i j
    by_cases hS' : InSswap (D.step P i j)
    · -- InSswap preserved → check other invariant components
      have hM' := step_median_answer_of_InSswap_both hn0 hn4 hS hS' hM
      left
      refine ⟨hS', hM', ?_⟩
      -- Timer at median: step_timer_le gives timer ≤ old timer = 0
      intro μ hμ
      have hrank : (D.step P i j μ).1.rank = (D μ).1.rank :=
        step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) hn0 hS μ
      have hμ_pre : (D μ).1.rank.val + 1 = ceilHalf n := by
        rwa [← show (D.step P i j μ).1.rank.val = (D μ).1.rank.val from
          congrArg Fin.val hrank]
      have h0 := hT μ hμ_pre
      have hle := step_timer_le_of_InSswap (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) hn0 hS μ
      omega
    · -- InSswap broke → phase4_propagate created Resetting agents → CorrectResetSeed
      right
      exact step_InSswap_break_creates_CorrectResetSeed hn4 hn0 hRmax hS hM hT hS'
  · -- hwin: one-step bound under Inv
    intro D ⟨hS, hM, hT⟩ hGoalD
    have hNotCons : ¬ IsConsensusConfig D := fun h => hGoalD (Or.inl h)
    have hWrongExists : ∃ v : Fin n, (D v).1.answer ≠ majorityAnswer D := by
      by_contra h; push_neg at h; exact hNotCons ⟨h⟩
    obtain ⟨μ, hμ_med⟩ := hS.toInSrank.exists_median (by omega : 0 < n)
    have hμ_correct : (D μ).1.answer = majorityAnswer D := hM μ hμ_med
    have hμ_timer : (D μ).1.timer = 0 := hT μ hμ_med
    -- Find a wrong-answer agent that is NOT the upper-median (rank n/2+1).
    -- If such exists, one step creates CorrectResetSeed (propagate fires).
    -- If no such exists, the ONLY wrong agent is the upper-median; step fixes it → consensus.
    by_cases hNonUpper : ∃ v : Fin n, (D v).1.answer ≠ majorityAnswer D ∧
        (D v).1.rank.val + 1 ≠ n / 2 + 1
    · obtain ⟨v, hv_wrong, hv_no_upper⟩ := hNonUpper
      have hμv : μ ≠ v := fun h => by subst h; exact hv_wrong hμ_correct
      apply Probability.ProbHitWithin_one_lower_bound_of_step P (by omega) D Goal
        (fun h => hGoalD h) hμv
      exact Or.inr (step_timer_zero_median_wrong_nonupper_creates_CorrectResetSeed
        hn4 hn0 hRmax hS hμv hμ_med hμ_timer hμ_correct hv_wrong hv_no_upper)
    · -- Only wrong agent has rank n/2+1 (upper median for even n).
      -- Step at (median, upper_median) via phase4_decide corrects its answer.
      -- Since it's the sole wrong agent, post-step has allAnswerCorrect → IsConsensusConfig.
      push_neg at hNonUpper
      obtain ⟨v, hv_wrong⟩ := hWrongExists
      have hμv : μ ≠ v := fun h => by subst h; exact hv_wrong hμ_correct
      apply Probability.ProbHitWithin_one_lower_bound_of_step P (by omega) D Goal
        (fun h => hGoalD h) hμv
      -- From hNonUpper applied to v with hv_wrong, v has rank+1 = n/2+1.
      have hv_upper : (D v).1.rank.val + 1 = n / 2 + 1 := by
        rcases hNonUpper v with h | h
        · exact absurd h hv_wrong
        · exact h
      -- For odd n, n/2+1 = ceilHalf n = median rank ⇒ v = μ. Contradicts μ ≠ v.
      -- So we're in even case.
      have hpar : n % 2 = 0 := by
        by_contra h
        push_neg at h
        have hceil : ceilHalf n = n / 2 + 1 := by unfold ceilHalf; omega
        apply hμv
        apply (hS.toInSrank.ranks_inj (Fin.ext ?_)).symm
        show (D v).1.rank.val = (D μ).1.rank.val
        have h1 : (D v).1.rank.val + 1 = (D μ).1.rank.val + 1 := by
          rw [hv_upper, hμ_med, hceil]
        omega
      -- Even case: μ at lower median, v at upper median. Step → IsConsensusConfig.
      left  -- IsConsensusConfig
      have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
      have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hμ_med
      have hsμ : (D μ).1.role = .Settled := hS.allSettled μ
      have hsv : (D v).1.role = .Settled := hS.allSettled v
      have h_maj : majorityAnswer (D.step P μ v) = majorityAnswer D := by
        simpa [P, PEMProtocolCoupled, PEMProtocol] using
          majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ v
      -- Case split on input agreement at (μ, v)
      by_cases hxeq : (D μ).2 = (D v).2
      · -- Agreed inputs (strict majority case)
        have hSwap' : InSswap (D.step P μ v) :=
          step_at_median_pair_even_preserves_InSswap
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            rankDeltaOSSR_satisfies_fix hS hμv hpar hμ_lower hv_upper hxeq hn4
        have hC'_eq := step_at_median_pair_even_agreed_inputs
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            rankDeltaOSSR_satisfies_fix hμv hsμ hsv hpar hμ_lower hv_upper hxeq hn4
        -- Derive strict majority (hne) from input agreement
        have h_sum := nAOf_add_nBOf D
        have hμ_rank : (D μ).1.rank.val = n / 2 - 1 := by omega
        have hv_rank : (D v).1.rank.val = n / 2 := by omega
        have hne : nAOf D ≠ nBOf D := by
          rcases hx : (D μ).2 with _ | _
          · -- x_μ = .A
            have hxv : (D v).2 = Opinion.A := by rw [← hxeq]; exact hx
            have h2 : (D v).1.rank.val < nAOf D := (hS.input_rank v).mp hxv
            intro h; omega
          · -- x_μ = .B
            have hxv : (D v).2 = Opinion.B := by rw [← hxeq]; exact hx
            have h2 : ¬ ((D v).1.rank.val < nAOf D) := by
              intro h; have := (hS.input_rank v).mpr h
              rw [hxv] at this; cases this
            intro h; omega
        have h_μ_eq_maj : opinionToAnswer (D μ).2 = majorityAnswer D :=
          opinionToAnswer_lower_median_eq_majorityAnswer_even hS hμ_lower hpar hne
        -- Build allAnswerCorrect post-step
        refine ⟨hSwap'.allSettled, hSwap'.ranks_inj, hSwap'.input_rank, ?_⟩
        intro w
        rw [h_maj]
        have h_step_w : D.step P μ v w = (
            fun w => if w = μ then ({(D μ).1 with answer := opinionToAnswer (D μ).2}, (D μ).2)
                     else if w = v then ({(D v).1 with answer := opinionToAnswer (D μ).2}, (D v).2)
                     else D w) w := by rw [hC'_eq]
        by_cases hwμ : w = μ
        · rw [h_step_w]; simp [hwμ, h_μ_eq_maj]
        · by_cases hwv : w = v
          · rw [h_step_w]; simp [hwμ, hwv, h_μ_eq_maj]
          · rw [h_step_w]; simp [hwμ, hwv]
            -- w ≠ μ, w ≠ v: by hNonUpper, w has correct answer
            rcases hNonUpper w with h | h
            · exact h
            · -- w at upper-median rank, but only v is there → w = v, contradicts hwv
              exfalso; apply hwv
              apply hS.toInSrank.ranks_inj
              exact Fin.ext (Nat.add_right_cancel (h.trans hv_upper.symm))
      · -- Disagreed inputs (tie case)
        have h_no_swap_disagree : ¬ ((D μ).2 = Opinion.B ∧ (D v).2 = Opinion.A) := by
          intro ⟨hxμB, hxvA⟩
          have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
            intro h; have := (hS.input_rank μ).mpr h
            rw [hxμB] at this; cases this
          have h2 : (D v).1.rank.val < nAOf D := (hS.input_rank v).mp hxvA
          have h_sum := nAOf_add_nBOf D
          omega
        have h_step := step_at_median_pair_even_disagreed_inputs
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            rankDeltaOSSR_satisfies_fix hμv hsμ hsv hpar hμ_lower hv_upper hxeq
            h_no_swap_disagree hn4
        obtain ⟨h_μ_post, h_v_post, h_others_post, h_inputs_post⟩ := h_step
        -- Tie case: majorityAnswer D = .outT
        have hTie : nAOf D = nBOf D := by
          have h_sum := nAOf_add_nBOf D
          -- Derive from disagreed inputs at lower-median μ and upper-median v
          rcases hxμ : (D μ).2 with _ | _
          · have hxvB : (D v).2 = Opinion.B := by
              cases hxv : (D v).2 with
              | A => exfalso; apply hxeq; rw [hxμ, hxv]
              | B => rfl
            have h1 : (D μ).1.rank.val < nAOf D := (hS.input_rank μ).mp hxμ
            have h2 : ¬ ((D v).1.rank.val < nAOf D) := by
              intro h; have := (hS.input_rank v).mpr h
              rw [hxvB] at this; cases this
            omega
          · have hxvA : (D v).2 = Opinion.A := by
              cases hxv : (D v).2 with
              | A => rfl
              | B => exfalso; apply hxeq; rw [hxμ, hxv]
            have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
              intro h; have := (hS.input_rank μ).mpr h
              rw [hxμ] at this; cases this
            have h2 : (D v).1.rank.val < nAOf D := (hS.input_rank v).mp hxvA
            omega
        have hMaj_outT : majorityAnswer D = .outT := majorityAnswer_eq_outT_of_tie hTie
        -- Build IsConsensusConfig
        constructor
        · -- allSettled
          intro w
          by_cases hwμ : w = μ
          · rw [hwμ, h_μ_post]; exact hsμ
          · by_cases hwv : w = v
            · rw [hwv, h_v_post]; exact hsv
            · rw [show (D.step P μ v w).1 = (D w).1 from
                congrArg Prod.fst (h_others_post w hwμ hwv)]
              exact hS.allSettled w
        · -- ranks_inj
          intro w1 w2 heq
          have h_rank_w : ∀ w, (D.step P μ v w).1.rank = (D w).1.rank := by
            intro w
            by_cases hwμ : w = μ
            · rw [hwμ, h_μ_post]
            · by_cases hwv : w = v
              · rw [hwv, h_v_post]
              · rw [show (D.step P μ v w).1 = (D w).1 from
                  congrArg Prod.fst (h_others_post w hwμ hwv)]
          simp only [h_rank_w] at heq
          exact hS.toInSrank.ranks_inj heq
        · -- input_rank
          intro w
          have h_nA : nAOf (D.step P μ v) = nAOf D := by
            unfold nAOf Config.agentsWithInput Config.inputOf
            congr 1; ext w'
            simp only [Finset.mem_filter]
            refine ⟨fun ⟨hm, hh⟩ => ⟨hm, by rw [h_inputs_post w'] at hh; exact hh⟩,
                    fun ⟨hm, hh⟩ => ⟨hm, by rw [h_inputs_post w']; exact hh⟩⟩
          have h_rank_w : (D.step P μ v w).1.rank = (D w).1.rank := by
            by_cases hwμ : w = μ
            · rw [hwμ, h_μ_post]
            · by_cases hwv : w = v
              · rw [hwv, h_v_post]
              · rw [show (D.step P μ v w).1 = (D w).1 from
                  congrArg Prod.fst (h_others_post w hwμ hwv)]
          rw [h_inputs_post w, h_rank_w, h_nA]
          exact hS.input_rank w
        · -- allAnswerCorrect
          intro w
          rw [h_maj, hMaj_outT]
          by_cases hwμ : w = μ
          · rw [hwμ]
            show (D.step P μ v μ).1.answer = .outT
            rw [h_μ_post]
          · by_cases hwv : w = v
            · rw [hwv]
              show (D.step P μ v v).1.answer = .outT
              rw [h_v_post]
            · -- w ≠ μ, w ≠ v: by hNonUpper, w has correct answer
              rw [show (D.step P μ v w).1 = (D w).1 from
                congrArg Prod.fst (h_others_post w hwμ hwv)]
              rcases hNonUpper w with h | h
              · rw [h, hMaj_outT]
              · exfalso; apply hwv
                apply hS.toInSrank.ranks_inj
                exact Fin.ext (Nat.add_right_cancel (h.trans hv_upper.symm))


/-! ### Axioms for proved helper theorems (proofs in TimerPosCRS.lean + Phase2Helper.lean) -/

/-- Proved in TimerPosCRS.lean.
InSswap + MedC + ¬InSswap(step) → CRS, without needing timer=0. -/
axiom crs_of_InSswap_break_with_MedC_axiom
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) (hM : MedianAnswerCorrect D)
    {i j : Fin n}
    (hS' : ¬ InSswap (D.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)) i j)) :
    CorrectResetSeed (D.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)) i j)

axiom allR_to_consensus_bound_axiom
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hDmaxN : n ≤ Dmax)
    (D : Config (AgentState n) Opinion n)
    (hAllR : ∀ w : Fin n, (D w).1.role = .Resetting)
    (hAllCorrect : ∀ w : Fin n, (D w).1.answer = majorityAnswer D) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) D IsConsensusConfig ≤
      ((2 * Rmax * n * n : ℕ) : ENNReal)

/-- Proof in RecoveryBound.lean (sorry placeholder).
From a wrong-restart state (some Resetting agents with full rc) back to
InSswap+timer or consensus. Bound: 8·Rmax·n². -/
axiom wrong_restart_recovery_axiom
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmaxN : n ≤ Dmax)
    (hDmax_le_Rmax : Dmax ≤ 2 * Rmax)
    (D : Config (AgentState n) Opinion n)
    (hBounded : IsBoundedConfig (max Rmax (max Dmax (7 * (Rmax + 4)))) D)
    (hAllRcFull :
      ∀ w : Fin n,
        (D w).1.role = .Resetting →
          (D w).1.resetcount = Rmax ∧ (D w).1.leader = .L)
    (hSomeR : ∃ r : Fin n, (D r).1.role = .Resetting) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) D
      (fun C =>
        IsConsensusConfig C ∨
          (InSswap C ∧
            MedianTimerAtLeast 1 C ∧
            IsTimerBoundedConfig (7 * (Rmax + 4)) C)) ≤
      ((8 * Rmax * n * n : ℕ) : ENNReal)

/-! Stage 3: Epidemic propagation. From CorrectResetSeed:
E[T to consensus] via nonResettingCount descent + re-ranking. -/

theorem PEM_expected_epidemic_to_consensus
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hDmaxN : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSeed : CorrectResetSeed C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C IsConsensusConfig ≤
      ((4 * Rmax * n * n : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  -- Two-phase composition via expectedHittingTime_add_le:
  -- Phase 1: From CorrectResetSeed, reach all-Resetting (nonResettingCount = 0)
  --   via deterministic descent on nonResettingCount. Bound: n · n(n-1).
  -- Phase 2: From all-Resetting with correct answers, reach IsConsensusConfig.
  --   The ranking phase re-establishes InSswap, then all answers are correct.
  --   Bound: 2 · Rmax · n².
  -- Total: n·n(n-1) + 2·Rmax·n² ≤ 3·Rmax·n² (for Rmax ≥ n ≥ 4).
  let AllR := fun D : Config (AgentState n) Opinion n =>
    IsConsensusConfig D ∨
    ((∀ w : Fin n, (D w).1.role = .Resetting) ∧
     (∀ w : Fin n, (D w).1.answer = majorityAnswer D))
  have hAllR_sub : ∀ D, IsConsensusConfig D → AllR D := fun D h => Or.inl h
  -- Phase 1: Epidemic descent. E[T to AllR] ≤ n · n(n-1).
  -- From CorrectResetSeed: ∃ seed r with Resetting, rc ≥ nonResettingCount.
  -- propagate_reset_step_nonResettingCount_lt (BurmanProof.lean) gives
  -- deterministic descent on nonResettingCount.
  have hPhase1 : Probability.expectedHittingTime P hn2 C AllR ≤
      ((n * n * (n - 1) : ℕ) : ENNReal) := by
    classical
    have hDmax : 1 < Dmax := by omega -- from hDmaxN : n ≤ Dmax and hn4 : 4 ≤ n
    -- Step 1: bound expectedHittingTime to Goal' = (CRS ∧ φ=0) ∨ ¬CRS ∨
    -- (∃ i j, φ(step) > φ) via variable_descent_until_goal with region-or-exit
    -- pattern.  The third disjunct internalises a per-config "step would
    -- increase φ" exit, so `hNonincrease` discharges by contradiction.
    set Goal' : Config (AgentState n) Opinion n → Prop := fun E =>
      (CorrectResetSeed E ∧ nonResettingCount E = 0) ∨ ¬ CorrectResetSeed E ∨
        ∃ i j : Fin n, nonResettingCount E < nonResettingCount (E.step P i j)
    -- Per-level p(k) = k / (n*(n-1)) from PEM_correctResetSeed_nonResetting_descent.
    have hToGoal' : Probability.expectedHittingTime P hn2 C Goal' ≤
        ∑ k ∈ Finset.range (nonResettingCount C),
          (((k + 1 : ℕ) : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ := by
      apply Probability.expectedHittingTime_le_of_variable_descent_until_goal
        P hn2 C Goal' (fun E => CorrectResetSeed E) nonResettingCount
        (fun k => ((k : ℕ) : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
        hSeed
      · -- hZeroGoal: CRS E ∧ φ=0 → Goal' E
        intro E hCRS hφ0
        exact Or.inl ⟨hCRS, hφ0⟩
      · -- hInvStep: by_cases CRS(step) — trivial via region-or-exit
        intro E hCRS_E _hG i j
        by_cases hCRS_step : CorrectResetSeed (E.step P i j)
        · exact Or.inl hCRS_step
        · exact Or.inr (Or.inr (Or.inl hCRS_step))
      · -- hNonincrease: discharged by contradiction via the φ(step) > φ exit
        -- disjunct of Goal'.  If nrc(step) > nrc E, then Goal' E holds via the
        -- third disjunct, contradicting `¬ Goal' E`.
        intro E _hCRS_E hG i j
        by_contra h_not_le
        push_neg at h_not_le
        exact hG (Or.inr (Or.inr ⟨i, j, h_not_le⟩))
      · -- hp: per-level prob bound using PEM_correctResetSeed_nonResetting_descent
        intro k hk E hCRS_E hφE
        have hφE_pos : 0 < nonResettingCount E := by rw [hφE]; exact hk
        have hprob := PEM_correctResetSeed_nonResetting_descent_prob_lower_bound
          (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn2 hn0 hDmax hCRS_E hφE_pos
        have hsub : (fun D => CorrectResetSeed D ∧
            nonResettingCount D < nonResettingCount E) ≤
            (fun D => Goal' D ∨ (CorrectResetSeed D ∧ nonResettingCount D < k)) := by
          intro F ⟨hF_CRS, hF_φ⟩
          right
          refine ⟨hF_CRS, ?_⟩
          rw [← hφE]; exact hF_φ
        calc ((k : ℕ) : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹
            = ((nonResettingCount E : ℕ) : ENNReal) *
                ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by rw [hφE]
          _ ≤ Probability.ProbHitWithin P hn2 E
                (fun D => CorrectResetSeed D ∧
                  nonResettingCount D < nonResettingCount E) 1 := hprob
          _ ≤ Probability.ProbHitWithin P hn2 E
                (fun D => Goal' D ∨ (CorrectResetSeed D ∧ nonResettingCount D < k)) 1 :=
              Probability.ProbHitWithin_mono_goal P hn2 E _ _ hsub 1
    -- Step 2: Bridge Goal' → AllR via `expectedHittingTime_add_le` with `Goal'` as
    -- the intermediate.  Three pieces: (i) numerical bound on the descent sum,
    -- (ii) `AllR ⊆ Goal'` for the contravariant `hMidGoal` slot, (iii) bound on
    -- `expectedHittingTime D AllR` for every `D ∈ Goal'`.  Piece (iii)'s `¬CRS`
    -- and `∃-exit` sub-cases are the residual protocol-level gap (see comment).
    -- Piece (i): the harmonic-like sum `∑ k<nrc(C), n(n-1)/(k+1)` is bounded by
    -- `nrc(C) · n(n-1) ≤ n · n(n-1) = n²(n-1)` because each term is ≤ n(n-1).
    have h_sum_le :
        (∑ k ∈ Finset.range (nonResettingCount C),
          (((k + 1 : ℕ) : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹) ≤
            ((n * n * (n - 1) : ℕ) : ENNReal) := by
      have h_term_le : ∀ k ∈ Finset.range (nonResettingCount C),
          (((k + 1 : ℕ) : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ ≤
            ((n * (n - 1) : ℕ) : ENNReal) := by
        intro k _
        have h_k1_ne_zero : ((k + 1 : ℕ) : ENNReal) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero k
        have h_k1_ne_top : ((k + 1 : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
        rw [ENNReal.mul_inv (Or.inl h_k1_ne_zero) (Or.inl h_k1_ne_top), inv_inv]
        have h_inv_le : ((k + 1 : ℕ) : ENNReal)⁻¹ ≤ 1 := by
          apply ENNReal.inv_le_one.mpr
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k)
        calc ((k + 1 : ℕ) : ENNReal)⁻¹ * ((n * (n - 1) : ℕ) : ENNReal)
            ≤ 1 * ((n * (n - 1) : ℕ) : ENNReal) :=
              mul_le_mul_right' h_inv_le _
          _ = ((n * (n - 1) : ℕ) : ENNReal) := one_mul _
      have h_nrc_le_n : nonResettingCount C ≤ n := by
        unfold nonResettingCount
        exact (Finset.card_filter_le _ _).trans (by simp)
      calc (∑ k ∈ Finset.range (nonResettingCount C),
            (((k + 1 : ℕ) : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹)
          ≤ ∑ _k ∈ Finset.range (nonResettingCount C),
              ((n * (n - 1) : ℕ) : ENNReal) :=
            Finset.sum_le_sum h_term_le
        _ = (nonResettingCount C : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ (n : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal) := by
            apply mul_le_mul_right'
            exact_mod_cast h_nrc_le_n
        _ = ((n * n * (n - 1) : ℕ) : ENNReal) := by
            push_cast; ring
    -- Piece (ii): AllR ⊆ Goal' (so that `expectedHittingTime_add_le`'s contravariant
    -- slot is satisfied).  IsConsensus implies no Resetting, hence ¬CRS, hence the
    -- second disjunct of Goal'.  all-Resetting + all-correct either satisfies CRS
    -- (with φ=0 → first disjunct) or is outside CRS (second disjunct).
    have h_AllR_sub : ∀ D, AllR D → Goal' D := by
      intro D hD
      rcases hD with hCons | ⟨hAllR_role, hAllR_ans⟩
      · -- IsConsensus → all Settled → no Resetting agent → ¬CRS
        right; left
        intro hCRS_D
        obtain ⟨r, hr_res, _⟩ := hCRS_D.1
        have hr_settled := hCons.allSettled r
        rw [hr_res] at hr_settled
        exact Role.noConfusion hr_settled
      · -- all-Resetting + all-correct
        by_cases hCRS_D : CorrectResetSeed D
        · -- CRS holds, and nrc D = 0 (since all are Resetting), so D1.
          left
          refine ⟨hCRS_D, ?_⟩
          unfold nonResettingCount
          have h_empty :
              Finset.univ.filter (fun w : Fin n => (D w).1.role ≠ .Resetting) = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro w hw
            rw [Finset.mem_filter] at hw
            exact hw.2 (hAllR_role w)
          rw [h_empty]
          exact Finset.card_empty
        · -- ¬CRS: D2.
          right; left; exact hCRS_D
    -- Piece (iii): per-state bound `expectedHittingTime D AllR ≤ M₂` for every `D`
    -- in `Goal'`.  D1 case (CRS ∧ φ=0) is 0 — D is itself AllR — proven below.
    -- D2 (¬CRS) and D3 (∃ i j, nrc(step) > nrc) are the residual gap: they need
    -- either a CRS-preservation theorem (which fails in the (Resetting,Resetting)
    -- rc=1 edge case — verified counterexample) or an outside-CRS expected-time
    -- bound (no such theorem exists in the codebase).  Merged into one named
    -- obligation so the open math is a single localised gap.
    have h_bridge_per_state :
        ∀ D, Goal' D → Probability.expectedHittingTime P hn2 D AllR ≤
          ((n * n * (n - 1) : ℕ) : ENNReal) := by
      intro D hD
      rcases hD with ⟨hCRS, hφ0⟩ | hExit
      · -- D1 case: CRS ∧ φ=0 → D is AllR via all-Resetting + all-correct.
        apply le_of_eq
        apply Probability.expectedHittingTime_eq_zero_of_goal
        -- AllR D via disjunct 2: (∀ w, role=R) ∧ (∀ w, answer=maj)
        right
        refine ⟨?_, ?_⟩
        · -- all-Resetting from nrc D = 0
          intro w
          by_contra hw
          have hw_mem :
              w ∈ Finset.univ.filter (fun w : Fin n => (D w).1.role ≠ .Resetting) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
          have h_pos : 0 < (Finset.univ.filter
              (fun w : Fin n => (D w).1.role ≠ .Resetting)).card :=
            Finset.card_pos.mpr ⟨w, hw_mem⟩
          unfold nonResettingCount at hφ0
          omega
        · -- all-correct via CRS: every Resetting agent has answer = majority,
          -- and all agents are Resetting from the previous bullet.
          intro w
          have hw_res : (D w).1.role = .Resetting := by
            by_contra hw
            have hw_mem :
                w ∈ Finset.univ.filter (fun w : Fin n => (D w).1.role ≠ .Resetting) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
            have h_pos : 0 < (Finset.univ.filter
                (fun w : Fin n => (D w).1.role ≠ .Resetting)).card :=
              Finset.card_pos.mpr ⟨w, hw_mem⟩
            unfold nonResettingCount at hφ0
            omega
          exact (hCRS.2 w hw_res).2
      · -- D2 ∨ D3: open math gap, packaged as a single placeholder.
        sorry
    have hComp := Probability.expectedHittingTime_add_le P hn2 C Goal' AllR
      ((n * n * (n - 1) : ℕ) : ENNReal)
      ((n * n * (n - 1) : ℕ) : ENNReal)
      (hToGoal'.trans h_sum_le) h_bridge_per_state h_AllR_sub
    calc Probability.expectedHittingTime P hn2 C AllR
        ≤ ((n * n * (n - 1) : ℕ) : ENNReal) +
          ((n * n * (n - 1) : ℕ) : ENNReal) := hComp
      _ ≤ ((2 * n * n * (n - 1) : ℕ) : ENNReal) := by norm_cast; omega
  -- Phase 2: From all-Resetting → IsConsensusConfig. E[T] ≤ 2·Rmax·n².
  -- After epidemic: all Resetting with correct answer (from CorrectResetSeed invariant).
  -- Re-ranking (Burman) + final phase reaches consensus.
  have hPhase2 : ∀ D : Config (AgentState n) Opinion n, AllR D →
      Probability.expectedHittingTime P hn2 D IsConsensusConfig ≤
        ((2 * Rmax * n * n : ℕ) : ENNReal) := by
    intro D hD
    rcases hD with hCons | hAllRes
    · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D IsConsensusConfig hCons]
      exact zero_le _
    · exact allR_to_consensus_bound_axiom
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hn0 hRmax hDmaxN D hAllRes.1 hAllRes.2
  -- Compose phases
  have hComp := Probability.expectedHittingTime_add_le P hn2 C AllR IsConsensusConfig
    ((n * n * (n - 1) : ℕ) : ENNReal) ((2 * Rmax * n * n : ℕ) : ENNReal)
    hPhase1 hPhase2 hAllR_sub
  calc Probability.expectedHittingTime P hn2 C IsConsensusConfig
      ≤ ((n * n * (n - 1) : ℕ) : ENNReal) + ((2 * Rmax * n * n : ℕ) : ENNReal) := hComp
    _ ≤ ((4 * Rmax * n * n : ℕ) : ENNReal) := by
        norm_cast
        have : n * n * (n - 1) ≤ 1 * Rmax * n * n := by
          calc n * n * (n - 1) ≤ n * n * n := Nat.mul_le_mul_left _ (Nat.sub_le n 1)
            _ ≤ Rmax * (n * n) := by nlinarith
            _ = 1 * Rmax * n * n := by ring
        linarith

/-! Full median-correct → consensus via Strong Markov on stages 1-3. -/

theorem PEM_expected_median_correct_to_consensus
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (hTimerLo : MedianTimerAtLeast 1 C)
    (hTimerHi : IsTimerBoundedConfig (7 * (Rmax + 4)) C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C IsConsensusConfig ≤
      ((18 * Rmax * n * n : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  let Mid := fun D : Config (AgentState n) Opinion n =>
    IsConsensusConfig D ∨ CorrectResetSeed D
  have hMidGoal : ∀ D, IsConsensusConfig D → Mid D := fun D h => Or.inl h
  have hStage1 : Probability.expectedHittingTime P hn2 C Mid ≤
      ((7 * (Rmax + 4) * n * (n - 1) + n * (n - 1) : ℕ) : ENNReal) := by
    -- Strong Markov composition of timer drain + reset trigger.
    -- Stage 1: Timer drain reaches TimerDrainExit = Mid ∨ ¬(InSswap ∧ timer≥1)
    -- Stage 2: From ¬(InSswap ∧ timer≥1), the reset trigger reaches Mid
    let TimerDrainExit := fun D : Config (AgentState n) Opinion n =>
      IsConsensusConfig D ∨ CorrectResetSeed D ∨
        (InSswap D ∧ MedianAnswerCorrect D ∧ ¬ MedianTimerAtLeast 1 D)
    have hTDE_sub_Mid : ∀ D, Mid D → TimerDrainExit D := by
      intro D hD
      rcases hD with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have hStage1a : Probability.expectedHittingTime P hn2 C TimerDrainExit ≤
        ((7 * (Rmax + 4) * n * (n - 1) : ℕ) : ENNReal) :=
      PEM_expected_timer_drain hn4 hn0 hRmax C hSswap hMedCorrect hTimerLo hTimerHi
    have hStage1b : ∀ D : Config (AgentState n) Opinion n, TimerDrainExit D →
        Probability.expectedHittingTime P hn2 D Mid ≤
          ((n * (n - 1) : ℕ) : ENNReal) := by
      intro D hD
      rcases hD with hCons | hSeed | hExit
      · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D Mid (Or.inl hCons)]
        exact zero_le _
      · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D Mid (Or.inr hSeed)]
        exact zero_le _
      · -- InSswap ∧ MedianCorrect ∧ ¬timer≥1: use PEM_expected_reset_trigger
        obtain ⟨hInS, hMedC, hNotTimer⟩ := hExit
        have hTimer0 : ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
            (D μ).1.timer = 0 := by
          intro μ hμ; by_contra h; push_neg at h
          exact hNotTimer (fun μ' hμ' => by
            have := hInS.toInSrank.ranks_inj (Fin.ext (by omega : (D μ').1.rank.val = (D μ).1.rank.val))
            subst this; exact Nat.pos_of_ne_zero (by omega))
        by_cases hwrong : 0 < wrongAnswerCount D
        · exact PEM_expected_reset_trigger hn4 hn0 hRmax _hEmax _hDmax D
            hInS hMedC hwrong hTimer0
        · -- wrongAnswerCount = 0 → all answers correct → IsConsensusConfig → Mid
          push_neg at hwrong
          have h0 := Nat.le_zero.mp hwrong
          have hAll := (wrongAnswerCount_eq_zero_iff D).mp h0
          rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D Mid
            (Or.inl ⟨hAll⟩)]
          exact zero_le _
    have hMidTDE : ∀ D, Mid D → TimerDrainExit D := hTDE_sub_Mid
    have hComp := Probability.expectedHittingTime_add_le P hn2 C TimerDrainExit Mid
      ((7 * (Rmax + 4) * n * (n - 1) : ℕ) : ENNReal)
      ((n * (n - 1) : ℕ) : ENNReal)
      hStage1a hStage1b hMidTDE
    calc Probability.expectedHittingTime P hn2 C Mid
        ≤ ((7 * (Rmax + 4) * n * (n - 1) : ℕ) : ENNReal) +
          ((n * (n - 1) : ℕ) : ENNReal) := hComp
      _ = ((7 * (Rmax + 4) * n * (n - 1) + n * (n - 1) : ℕ) : ENNReal) := by
          norm_cast
  have hStage3 : ∀ D : Config (AgentState n) Opinion n, Mid D →
      Probability.expectedHittingTime P hn2 D IsConsensusConfig ≤
        ((4 * Rmax * n * n : ℕ) : ENNReal) := by
    intro D hD
    rcases hD with hCons | hSeed
    · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D IsConsensusConfig hCons]
      exact zero_le _
    · exact PEM_expected_epidemic_to_consensus hn4 hn0 hRmax hDmax D hSeed
  have hCompose := Probability.expectedHittingTime_add_le P hn2 C Mid IsConsensusConfig
    ((7 * (Rmax + 4) * n * (n - 1) + n * (n - 1) : ℕ) : ENNReal)
    ((4 * Rmax * n * n : ℕ) : ENNReal)
    hStage1 hStage3 hMidGoal
  calc Probability.expectedHittingTime P hn2 C IsConsensusConfig
      ≤ ((7 * (Rmax + 4) * n * (n - 1) + n * (n - 1) : ℕ) : ENNReal) +
        ((4 * Rmax * n * n : ℕ) : ENNReal) := hCompose
    _ ≤ ((18 * Rmax * n * n : ℕ) : ENNReal) := by
        -- arithmetic: 7(Rmax+4)n(n-1) + n(n-1) + 3Rmax·n² ≤ 18Rmax·n²
        -- for Rmax ≥ n ≥ 4
        norm_cast
        have hn1 : 1 ≤ n := by omega
        have hn_sub : n - 1 ≤ n := Nat.sub_le n 1
        have h1 : 7 * (Rmax + 4) * n * (n - 1) ≤ 14 * Rmax * n * n := by
          calc 7 * (Rmax + 4) * n * (n - 1)
              ≤ 7 * (Rmax + 4) * n * n := Nat.mul_le_mul_left _ hn_sub
            _ = 7 * (Rmax + 4) * (n * n) := by ring
            _ = (7 * Rmax + 28) * (n * n) := by ring
            _ ≤ (7 * Rmax + 7 * Rmax) * (n * n) := by
                apply Nat.mul_le_mul_right
                apply Nat.add_le_add_left
                calc 28 ≤ 7 * 4 := by omega
                  _ ≤ 7 * Rmax := Nat.mul_le_mul_left _ (by omega)
            _ = 14 * Rmax * (n * n) := by ring
            _ = 14 * Rmax * n * n := by ring
        have h2 : n * (n - 1) ≤ 1 * Rmax * n * n := by
          calc 2 * n * (n - 1)
              ≤ 2 * (n * n) := by nlinarith
            _ ≤ Rmax * (n * n) := Nat.le_mul_of_pos_left _ (by omega)
            _ = 1 * Rmax * n * n := by ring
        linarith

/-! Phase C assembly: compose median-wrong descent + median-correct via
strong Markov to get the full hConsensusBound. -/

theorem PEM_hConsensusBound_from_bridge
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hTimerLo : MedianTimerAtLeast 1 C)
    (hTimerHi : IsTimerBoundedConfig (7 * (Rmax + 4)) C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C IsConsensusConfig ≤
      ((20 * Rmax * n * n : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  have hDecision : Probability.expectedHittingTime P hn2 C (DecisionProgress Rmax) ≤
      ((2 * n * (n - 1) : ℕ) : ENNReal) := by
    by_cases hMedC : MedianAnswerCorrect C
    · -- C already satisfies the third disjunct of DecisionProgress
      rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 C (DecisionProgress Rmax)
        (Or.inr (Or.inr ⟨hSswap, hMedC, hTimerLo, hTimerHi⟩))]
      exact zero_le _
    · -- C lacks MedianAnswerCorrect. Two-phase composition:
      -- Phase A: reach MedC ∨ DP.  Step at (median, upper-median) either
      --   establishes MedC (if InSswap preserved) or breaks InSswap → DP.
      -- Phase B: from MedC, existing machinery gives DP.
      -- Total: 2·n(n-1) ≤ n(n-1) (fits in the bound since we only need ≤ n(n-1)).
      -- Actually: we use expectedHittingTime_le_inv_of_local_one_lower_bound_until_goal
      -- with Inv = InSswap ∧ timerBounded and Goal = MedC ∨ DP.
      -- The one-step bound: from any Inv D with ¬Goal D, step at (median, upper-median)
      -- reaches MedC or breaks InSswap → DP.  Both are in Goal.
      -- Two-phase via expectedHittingTime_add_le:
      -- Mid D = MedianAnswerCorrect D ∨ DecisionProgress Rmax D
      let Mid := fun D : Config (AgentState n) Opinion n =>
        (MedianAnswerCorrect D ∧ InSswap D ∧
          IsTimerBoundedConfig (7 * (Rmax + 4)) D) ∨
        DecisionProgress Rmax D
      have hMidGoal : ∀ D, DecisionProgress Rmax D → Mid D :=
        fun D h => Or.inr h
      -- Phase A: E[T to Mid from C] ≤ n(n-1)
      have hPhaseA : Probability.expectedHittingTime P hn2 C Mid ≤
          ((n * (n - 1) : ℕ) : ENNReal) := by
        apply (Probability.expectedHittingTime_le_inv_of_local_one_lower_bound_until_goal
          P hn2 C Mid
          (fun D => InSswap D ∧ IsTimerBoundedConfig (7 * (Rmax + 4)) D)
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹
          ⟨hSswap, hTimerHi⟩
          (by -- hInvStep
              intro D ⟨hSD, hTBD⟩ _hGoalD i j
              by_cases hSD' : InSswap (D.step P i j)
              · left; exact ⟨hSD', by
                  intro w
                  calc (D.step P i j w).1.timer
                      ≤ (D w).1.timer :=
                        step_timer_le_of_InSswap (Rmax := Rmax) (Emax := Emax)
                          (Dmax := Dmax) hn0 hSD w
                    _ ≤ 7 * (Rmax + 4) := hTBD w⟩
              · -- InSswap broke → CRS → DP → Mid
                right
                by_cases hpar : n % 2 = 0
                · -- Even n: split on pre-step MedC
                  by_cases hMedC_D : MedianAnswerCorrect D
                  · -- MedC pre-step: use step_InSswap_break_creates_CorrectResetSeed
                    -- Need hT (timer=0). InSswap break implies propagation fired →
                    -- timer=0 (post-decrement). Derive pre-step timer value.
                    -- Even n + MedC: use existing CRS lemma with sorry for hT
                    -- InSswap break with MedC: use existing CRS lemma if timer=0,
                    -- or CRS-odd approach adapted for even n if timer=1.
                    -- For timer=0: existing lemma applies directly.
                    -- For timer=1: same CRS but with decrement.
                    obtain ⟨μ', hμ'_med⟩ := hSD.toInSrank.exists_median (by omega : 0 < n)
                    by_cases hT0 : (D μ').1.timer = 0
                    · have hT : ∀ μ'' : Fin n, (D μ'').1.rank.val + 1 = ceilHalf n →
                          (D μ'').1.timer = 0 := by
                        intro μ'' hμ''_med
                        have := hSD.toInSrank.ranks_inj (Fin.ext (by omega))
                        subst this; exact hT0
                      exact Or.inr (step_InSswap_break_creates_CorrectResetSeed
                        hn4 hn0 hRmax hSD hMedC_D hT hSD')
                    · -- timer > 0: even n + MedC + timer>0 + InSswap break → CRS
                      -- Uses step_InSswap_break_creates_CorrectResetSeed_even_MedC
                      exact Or.inr (by
                        simpa [P, PEMProtocolCoupled, PEMProtocol] using
                          crs_of_InSswap_break_with_MedC_axiom
                            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                            hn4 hn0 hRmax hSD hMedC_D
                            (by
                              simpa [P, PEMProtocolCoupled, PEMProtocol] using hSD'))
                  · -- ¬MedC pre-step: for even n, InSswap break without MedC
                    -- creates Resetting agents with wrong answer → neither MedC nor DP.
                    -- This is the genuine even-n gap.
                    sorry -- Even n + ¬MedC + InSswap break: structural gap
                · -- Odd n: phase4_decide corrects → CRS
                  exact Or.inr (Or.inr (step_InSswap_break_creates_CorrectResetSeed_odd
                    hn4 hn0 hRmax hSD hpar hSD')))
          (by -- hwin: step at (median, upper-median) → MedC or DP → Mid
              intro D ⟨hSD, hTBD⟩ hGoalD
              have hNotMid : ¬ Mid D := hGoalD
              obtain ⟨μ, hμ_med⟩ := hSD.toInSrank.exists_median (by omega : 0 < n)
              by_cases hpar : n % 2 = 0
              · -- Even n: pick upper-median, phase4_decide fires at (n/2, n/2+1)
                -- Even n: pick upper-median ξ at rank n/2
                have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
                have h_upper_lt : n / 2 < n := by omega
                obtain ⟨ξ, hξ_rank⟩ := hSD.toInSrank.exists_at_rank (by omega : 0 < n) ⟨n / 2, h_upper_lt⟩
                have hμξ : μ ≠ ξ := by
                  intro h; subst h
                  have : (D μ).1.rank.val = n / 2 := by rw [hξ_rank]
                  have : (D μ).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hμ_med
                  omega
                have hMidStep : Mid (D.step P μ ξ) := by
                  by_cases hSD' : InSswap (D.step P μ ξ)
                  · -- InSswap preserved → MedC via phase4_decide at (n/2, n/2+1)
                    left; refine ⟨?_, hSD', ?_⟩
                    · -- MedC at step for even n at (μ, ξ)
                      -- Even n at (μ, ξ) = (lower-median, upper-median)
                      intro ν hν
                      rw [show majorityAnswer (D.step P μ ξ) = majorityAnswer D from by
                        simpa [P, PEMProtocolCoupled, PEMProtocol] using
                          majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
                            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ ξ]
                      have hν_pre : (D ν).1.rank.val + 1 = ceilHalf n := by
                        rwa [← show (D.step P μ ξ ν).1.rank.val = (D ν).1.rank.val from
                          congrArg Fin.val (step_rank_preserved_of_InSswap
                            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hSD ν)]
                      have hνμ : ν = μ := hSD.toInSrank.ranks_inj (Fin.ext (by omega))
                      subst hνμ
                      -- μ is the first agent in (μ, ξ). phase4_decide at (n/2, n/2+1) fires.
                      have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hμ_med
                      have hξ_upper : (D ξ).1.rank.val + 1 = n / 2 + 1 := by rw [hξ_rank]
                      -- Protocol unfolding for even n at (lower-median, upper-median)
                      rw [show (D.step P μ ξ μ).1.answer =
                          (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                            (D μ, D ξ)).1.answer from
                        congrArg AgentState.answer (Config.step_fst_state P D
                          (by intro h; exact hμξ (hSD.toInSrank.ranks_inj
                            (Fin.ext (show (D μ).1.rank.val = (D ξ).1.rank.val by rw [h])))))]
                      have hsi := hSD.toInSrank.allSettled μ
                      have hsξ := hSD.toInSrank.allSettled ξ
                      have hrij : (D μ).1.rank ≠ (D ξ).1.rank := by
                        intro h; exact hμξ (hSD.toInSrank.ranks_inj h)
                      have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
                        (Dmax := Dmax) (hn := hn0) (D μ).1 (D ξ).1 hsi hsξ hrij
                      have h_no_swap := hSD.swap_condition_false μ ξ
                      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
                        phase4_swap phase4_decide phase4_propagate
                      simp only [hRD, hsi, hsξ, ne_eq, role_settled_ne_resetting,
                        not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
                        and_self, if_true, h_no_swap, hpar, hμ_lower, hξ_upper]
                      -- After simp: the median's answer is set by phase4_decide (even n)
                      -- to opinionToAnswer of the majority opinion.
                      by_cases hxeq : (D μ).2 = (D ξ).2
                      · -- Agreed inputs (strict majority)
                        simp only [hxeq, if_true]
                        have hne : nAOf D ≠ nBOf D := by
                          have h_sum := nAOf_add_nBOf D
                          cases hx : (D μ).2 with
                          | A => have hξA := hxeq ▸ hx
                                 have h2 : (D ξ).1.rank.val < nAOf D := (hSD.input_rank ξ).mp hξA
                                 intro h; omega
                          | B => have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
                                   intro hh; have := (hSD.input_rank μ).mpr hh; rw [hx] at this; cases this
                                 intro h; omega
                        exact opinionToAnswer_lower_median_eq_majorityAnswer_even hSD hμ_lower hpar hne
                      · -- Disagreed inputs (tie)
                        simp only [show ¬((D μ).2 = (D ξ).2) from hxeq, if_false]
                        -- Tie: nAOf = nBOf, both get .outT = majorityAnswer
                        have hTie : nAOf D = nBOf D := by
                          have h_sum := nAOf_add_nBOf D
                          cases hxμ : (D μ).2 with
                          | A => cases hxξ : (D ξ).2 with
                                 | A => exact absurd (hxμ.trans hxξ.symm) hxeq
                                 | B => have h1 := (hSD.input_rank μ).mp hxμ
                                        have h2 : ¬ ((D ξ).1.rank.val < nAOf D) := by
                                          intro hh; have := (hSD.input_rank ξ).mpr hh
                                          rw [hxξ] at this; cases this
                                        omega
                          | B => cases hxξ : (D ξ).2 with
                                 | A => have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
                                          intro hh; have := (hSD.input_rank μ).mpr hh
                                          rw [hxμ] at this; cases this
                                        have h2 := (hSD.input_rank ξ).mp hxξ
                                        omega
                                 | B => exact absurd (hxμ.trans hxξ.symm) hxeq
                        rw [majorityAnswer_eq_outT_of_tie hTie]
                        split_ifs <;> rfl
                    · intro w
                      calc (D.step P μ ξ w).1.timer
                          ≤ (D w).1.timer :=
                            step_timer_le_of_InSswap (Rmax := Rmax) (Emax := Emax)
                              (Dmax := Dmax) hn0 hSD w
                        _ ≤ 7 * (Rmax + 4) := hTBD w
                  · -- InSswap broke at (μ, ξ) → phase4_decide set correct answer → CRS
                    right
                    -- At (μ, ξ) = (n/2, n/2+1) for even n with InSswap:
                    -- phase4_decide fires and sets BOTH answers to majorityAnswer.
                    -- After decide: no disagreement → propagation doesn't fire →
                    -- InSswap is PRESERVED. So ¬InSswap(step) is IMPOSSIBLE.
                    exfalso
                    apply hSD'
                    -- InSswap preserved at (μ, ξ) = (n/2, n/2+1)
                    have hRankFix := rankDeltaOSSR_satisfies_fix
                      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
                    by_cases hxeq : (D μ).2 = (D ξ).2
                    · simpa [P, PEMProtocolCoupled, PEMProtocol] using
                        step_at_median_pair_even_preserves_InSswap
                          (n := n) (trank := Rmax) (Rmax := Rmax)
                          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
                          hRankFix hSD hμξ hpar hμ_lower hξ_upper hxeq hn4
                    · -- Disagreed inputs (tie): both get .outT, no propagation
                      have hNotMedC : ¬ MedianAnswerCorrect D := by
                        intro hM; exact hNotMid (Or.inl ⟨hM, hSD, hTBD⟩)
                      have hμ_wrong : (D μ).1.answer ≠ majorityAnswer D := by
                        intro h; exact hNotMedC (fun ν hν => by
                          have := hSD.toInSrank.ranks_inj (Fin.ext (by omega))
                          subst this; exact h)
                      have hTie : nAOf D = nBOf D := by
                        by_contra hne; push_neg at hne
                        exact hxeq (InSswap_even_median_pair_inputs_agree_of_strict
                          hSD hpar hne hμ_lower hξ_upper)
                      simpa [P, PEMProtocolCoupled, PEMProtocol] using
                        (decision_step_at_median_pair_even_tie_decreases
                          (trank := Rmax) (Rmax := Rmax)
                          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
                          rankDeltaOSSR_satisfies_fix hSD hμξ hpar hμ_lower hξ_upper
                          hxeq hTie hn4 (Or.inl hμ_wrong)).1
                exact Probability.ProbHitWithin_one_lower_bound_of_step P hn2 D Mid
                  hNotMid hμξ hMidStep
              · -- Odd n: any v works, phase4_decide fires for any median step
                have hn_ge : 1 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
                obtain ⟨v, hv_ne⟩ := Fintype.exists_ne_of_one_lt_card hn_ge μ
                have hMidStep : Mid (D.step P μ v) := by
                  by_cases hSD' : InSswap (D.step P μ v)
                  · left; refine ⟨?_, hSD', ?_⟩
                    · -- MedC at step: odd n, protocol unfolding
                      intro ν hν
                      rw [show majorityAnswer (D.step P μ v) = majorityAnswer D from by
                        simpa [P, PEMProtocolCoupled, PEMProtocol] using
                          majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
                            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ v]
                      have hν_pre : (D ν).1.rank.val + 1 = ceilHalf n := by
                        rwa [← show (D.step P μ v ν).1.rank.val = (D ν).1.rank.val from
                          congrArg Fin.val (step_rank_preserved_of_InSswap
                            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hSD ν)]
                      have hνμ : ν = μ := hSD.toInSrank.ranks_inj (Fin.ext (by omega))
                      subst hνμ
                      rw [show (D.step P μ v μ).1.answer =
                          (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                            (D μ, D v)).1.answer from
                        congrArg AgentState.answer (Config.step_fst_state P D
                          (by intro h; exact hv_ne.symm (hSD.toInSrank.ranks_inj
                            (Fin.ext (show (D μ).1.rank.val = (D v).1.rank.val by rw [h])))))]
                      have hsi := hSD.toInSrank.allSettled μ
                      have hsv := hSD.toInSrank.allSettled v
                      have hrij : (D μ).1.rank ≠ (D v).1.rank := by
                        intro h; exact hv_ne.symm (hSD.toInSrank.ranks_inj h)
                      have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
                        (Dmax := Dmax) (hn := hn0) (D μ).1 (D v).1 hsi hsv hrij
                      have h_no_swap := hSD.swap_condition_false μ v
                      have hvR_no_med : ¬ ((D v).1.rank.val + 1 = ceilHalf n) := by
                        intro h; exact hrij (Fin.ext (by omega))
                      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
                        phase4_swap phase4_decide phase4_propagate
                      simp only [hRD, hsi, hsv, ne_eq, role_settled_ne_resetting,
                        not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
                        and_self, if_true, h_no_swap, hpar, hμ_med, hvR_no_med]
                      exact opinionToAnswer_median_eq_majorityAnswer_odd hSD hμ_med hpar
                    · intro w
                      calc (D.step P μ v w).1.timer
                          ≤ (D w).1.timer :=
                            step_timer_le_of_InSswap (Rmax := Rmax) (Emax := Emax)
                              (Dmax := Dmax) hn0 hSD w
                        _ ≤ 7 * (Rmax + 4) := hTBD w
                  · right
                    exact Or.inr (step_InSswap_break_creates_CorrectResetSeed_odd
                      hn4 hn0 hRmax hSD hpar hSD')
                exact Probability.ProbHitWithin_one_lower_bound_of_step P hn2 D Mid
                  hNotMid hv_ne.symm hMidStep)).trans
          (by rw [inv_inv])
      -- Phase B: E[T to DP from Mid] ≤ n(n-1)
      have hPhaseB : ∀ D : Config (AgentState n) Opinion n, Mid D →
          Probability.expectedHittingTime P hn2 D (DecisionProgress Rmax) ≤
            ((n * (n - 1) : ℕ) : ENNReal) := by
        intro D hD
        rcases hD with ⟨hMedD, hSD_D, hTBD_D⟩ | hDP
        · -- MedC + InSswap + timerBounded → DP ≤ n(n-1)
          -- Timer≥1 case: DP immediately. Timer=0: one step to CRS.
          by_cases hTimer : MedianTimerAtLeast 1 D
          · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D
              (DecisionProgress Rmax) (Or.inr (Or.inr ⟨hSD_D, hMedD, hTimer, hTBD_D⟩))]
            exact zero_le _
          · -- timer=0 + MedC + InSswap → DP via one-step or IsConsensusConfig
            by_cases hWrong : 0 < wrongAnswerCount D
            · -- wrongAnswer > 0: use PEM_expected_reset_trigger or one-step bound
              -- timer=0 derived from ¬MedianTimerAtLeast 1 + InSswap (unique median)
              have hTimer0 : ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
                  (D μ).1.timer = 0 := by
                intro μ hμ; by_contra h; push_neg at h
                exact hTimer (fun μ' hμ' => by
                  have := hSD_D.toInSrank.ranks_inj (Fin.ext (by omega))
                  subst this; exact Nat.pos_of_ne_zero (by omega))
              calc Probability.expectedHittingTime P hn2 D (DecisionProgress Rmax)
                  ≤ Probability.expectedHittingTime P hn2 D
                    (fun E => IsConsensusConfig E ∨ CorrectResetSeed E) :=
                      Probability.expectedHittingTime_mono_goal P hn2 D _ _
                        (fun E hE => by rcases hE with h | h; exact Or.inl h; exact Or.inr (Or.inl h))
                _ ≤ ((n * (n - 1) : ℕ) : ENNReal) :=
                      PEM_expected_reset_trigger hn4 hn0 hRmax hEmax hDmaxN D
                        hSD_D hMedD hWrong hTimer0
            · -- wrongAnswer = 0: all answers correct → IsConsensusConfig → DP
              push_neg at hWrong
              have hZero : wrongAnswerCount D = 0 := Nat.le_zero.mp hWrong
              have hAll := (wrongAnswerCount_eq_zero_iff D).mp hZero
              rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D
                (DecisionProgress Rmax) (Or.inl ⟨hSD_D.allSettled, hSD_D.ranks_inj,
                  hSD_D.input_rank, hAll⟩)]
              exact zero_le _
        · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D
            (DecisionProgress Rmax) hDP]
          exact zero_le _
      -- Compose
      exact le_trans
        (Probability.expectedHittingTime_add_le P hn2 C Mid
          (DecisionProgress Rmax)
          ((n * (n - 1) : ℕ) : ENNReal) ((n * (n - 1) : ℕ) : ENNReal)
          hPhaseA hPhaseB hMidGoal)
        (by norm_cast; omega)
  have hFromDP : ∀ D : Config (AgentState n) Opinion n, DecisionProgress Rmax D →
      Probability.expectedHittingTime P hn2 D IsConsensusConfig ≤
        ((18 * Rmax * n * n : ℕ) : ENNReal) := by
    intro D hD
    rcases hD with hCons | hSeed | ⟨hSwap, hMed, hTLo, hTHi⟩
    · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D IsConsensusConfig hCons]
      exact zero_le _
    · calc Probability.expectedHittingTime P hn2 D IsConsensusConfig
          ≤ ((4 * Rmax * n * n : ℕ) : ENNReal) :=
            PEM_expected_epidemic_to_consensus hn4 hn0 hRmax hDmax D hSeed
        _ ≤ ((18 * Rmax * n * n : ℕ) : ENNReal) := by
            norm_cast; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    · exact PEM_expected_median_correct_to_consensus hn4 hn0 hRmax hEmax hDmax D
        hSwap hMed hTLo hTHi
  have hMidGoal : ∀ D : Config (AgentState n) Opinion n,
      IsConsensusConfig D → DecisionProgress Rmax D := by
    intro D hD; exact Or.inl hD
  have hCompose := Probability.expectedHittingTime_add_le P hn2 C
    (DecisionProgress Rmax) IsConsensusConfig
    ((2 * n * (n - 1) : ℕ) : ENNReal) ((18 * Rmax * n * n : ℕ) : ENNReal)
    hDecision hFromDP hMidGoal
  calc Probability.expectedHittingTime P hn2 C IsConsensusConfig
      ≤ ((2 * n * (n - 1) : ℕ) : ENNReal) + ((18 * Rmax * n * n : ℕ) : ENNReal) := hCompose
    _ ≤ ((20 * Rmax * n * n : ℕ) : ENNReal) := by
        -- arithmetic: n(n-1) + 18Rmax·n² ≤ 20Rmax·n² for Rmax≥n≥4
        norm_cast
        have hn_sub : n - 1 ≤ n := Nat.sub_le n 1
        have h1 : 2 * n * (n - 1) ≤ 2 * Rmax * n * n := by
          calc 2 * n * (n - 1)
              ≤ 2 * (n * n) := by nlinarith
            _ ≤ 2 * (Rmax * (n * n)) := by nlinarith
            _ = 2 * Rmax * n * n := by ring
        linarith

end SSEM
