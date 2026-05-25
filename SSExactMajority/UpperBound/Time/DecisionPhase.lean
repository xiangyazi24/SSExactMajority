import SSExactMajority.UpperBound.Time.Defs
import SSExactMajority.UpperBound.Time.SwapPhase

namespace SSEM

open scoped ENNReal

/-! ### Decision-phase one-step probability witnesses -/

/-- Any concrete one-step decision witness gives the exact ordered-pair
scheduler lower bound for decreasing `wrongAnswerCount`. -/
theorem PEM_wrongAnswer_one_step_descent_prob_lower_bound_of_step
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hdec :
      wrongAnswerCount
        (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) u v) <
      wrongAnswerCount C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := by
  exact Probability.ProbHitWithin_one_lower_bound_of_step
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
    (fun D => wrongAnswerCount D < wrongAnswerCount C)
    (by exact Nat.lt_irrefl (wrongAnswerCount C)) huv hdec

/-- Even-population median-pair decision step as a one-step probability lower
bound for decreasing `wrongAnswerCount`. -/
theorem PEM_even_median_pair_decision_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {u v : Fin n} (huv : u ≠ v)
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (h_inputs_agree : (C u).2 = (C v).2)
    (hne : nAOf C ≠ nBOf C)
    (h_one_wrong : (C u).1.answer ≠ majorityAnswer C ∨
      (C v).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := by
  apply PEM_wrongAnswer_one_step_descent_prob_lower_bound_of_step
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 huv
  simpa [PEMProtocolCoupled, PEMProtocol] using
    (decision_step_at_median_pair_even_decreases
      (n := n) (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hC huv hpar hu_med hv_upper h_inputs_agree hne hn4 h_one_wrong).2

/-- Even-population tie-case median-pair decision step as a one-step
probability lower bound for decreasing `wrongAnswerCount`. -/
theorem PEM_even_median_pair_tie_decision_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {u v : Fin n} (huv : u ≠ v)
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (h_inputs_disagree : (C u).2 ≠ (C v).2)
    (hTie : nAOf C = nBOf C)
    (h_one_wrong : (C u).1.answer ≠ majorityAnswer C ∨
      (C v).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := by
  apply PEM_wrongAnswer_one_step_descent_prob_lower_bound_of_step
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 huv
  simpa [PEMProtocolCoupled, PEMProtocol] using
    (decision_step_at_median_pair_even_tie_decreases
      (n := n) (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hC huv hpar hu_med hv_upper h_inputs_disagree hTie hn4 h_one_wrong).2

/-- If `n` is even and some median agent is wrong, then the appropriate
median-pair witness (strict-majority or tie case) gives a one-step scheduler
lower bound for decreasing `wrongAnswerCount`. -/
theorem PEM_even_median_wrong_decision_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hpar : n % 2 = 0)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := by
  classical
  by_cases hTie : nAOf C = nBOf C
  · obtain ⟨u, v, huv, hu_med, hv_upper, h_disagree, h_wrong⟩ :=
      evenCase_witness_when_median_wrong_tie hC hpar hn4 hTie h_med_wrong
    exact PEM_even_median_pair_tie_decision_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC huv hpar hu_med hv_upper h_disagree hTie h_wrong
  · obtain ⟨u, v, huv, hu_med, hv_upper, h_agree, h_wrong⟩ :=
      evenCase_witness_when_median_wrong hC hpar hn4 hTie h_med_wrong
    exact PEM_even_median_pair_decision_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC huv hpar hu_med hv_upper h_agree hTie h_wrong

/-- Even-population median-wrong decision reaches the local `Sdec` predicate
(`MedianAnswerCorrect`) in one median-pair step, preserving `InSswap`. -/
theorem PEM_even_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hpar : n % 2 = 0)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hRankFix := rankDeltaOSSR_satisfies_fix
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
  have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
  have htarget_not : ¬ (InSswap C ∧ MedianAnswerCorrect C) := by
    intro hTarget
    rcases h_med_wrong with ⟨μ, hμ, hwrong⟩
    exact hwrong (hTarget.2 μ hμ)
  by_cases hTie : nAOf C = nBOf C
  · obtain ⟨u, v, huv, hu_med, hv_upper, h_disagree, h_wrong⟩ :=
      evenCase_witness_when_median_wrong_tie hC hpar hn4 hTie h_med_wrong
    have hsu := hC.allSettled u
    have hsv := hC.allSettled v
    have h_no_swap : ¬((C u).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
      intro h
      rcases h with ⟨huB, _hvA⟩
      have hsum := nAOf_add_nBOf C
      have hu_low : (C u).1.rank.val < nAOf C := by omega
      have huA : (C u).2 = Opinion.A := (hC.input_rank u).mpr hu_low
      rw [huA] at huB
      cases huB
    obtain ⟨h_u, _h_v, h_others, _h_inputs⟩ :=
      step_at_median_pair_even_disagreed_inputs
        (trank := Rmax) (Rmax := Rmax)
        hRankFix huv hsu hsv hpar hu_med hv_upper h_disagree h_no_swap hn4
    have hSwap' : InSswap (C.step P u v) := by
      have hdec := decision_step_at_median_pair_even_tie_decreases
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        hRankFix hC huv hpar hu_med hv_upper h_disagree hTie hn4 h_wrong
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hdec.1
    have hmaj : majorityAnswer (C.step P u v) = majorityAnswer C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C u v)
    have h_u_correct : (C.step P u v u).1.answer = majorityAnswer (C.step P u v) := by
      have h_outT : majorityAnswer C = .outT := majorityAnswer_eq_outT_of_tie hTie
      have hu_state : (C.step P u v u).1 = {(C u).1 with answer := .outT} := by
        simpa [P, PEMProtocolCoupled, PEMProtocol] using h_u
      rw [hmaj, h_outT, hu_state]
    have h_u_med' : (C.step P u v u).1.rank.val + 1 = ceilHalf n := by
      have hu_state : (C.step P u v u).1 = {(C u).1 with answer := .outT} := by
        simpa [P, PEMProtocolCoupled, PEMProtocol] using h_u
      rw [hu_state, hceil]
      simpa using hu_med
    have hGoal : InSswap (C.step P u v) ∧ MedianAnswerCorrect (C.step P u v) := by
      refine ⟨hSwap', ?_⟩
      intro η hη
      have hηu : η = u := by
        apply hSwap'.ranks_inj
        apply Fin.eq_of_val_eq
        have hηval : (C.step P u v η).1.rank.val = ceilHalf n - 1 := by omega
        have huval : (C.step P u v u).1.rank.val = ceilHalf n - 1 := by omega
        exact hηval.trans huval.symm
      subst η
      exact h_u_correct
    exact Probability.ProbHitWithin_one_lower_bound_of_step
      (P := P) hn2 C (fun D => InSswap D ∧ MedianAnswerCorrect D)
      htarget_not huv hGoal
  · obtain ⟨u, v, huv, hu_med, hv_upper, h_agree, h_wrong⟩ :=
      evenCase_witness_when_median_wrong hC hpar hn4 hTie h_med_wrong
    have hsu := hC.allSettled u
    have hsv := hC.allSettled v
    have hC'_eq := step_at_median_pair_even_agreed_inputs
      (n := n) (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      hRankFix huv hsu hsv hpar hu_med hv_upper h_agree hn4
    have hSwap' : InSswap (C.step P u v) := by
      have hdec := decision_step_at_median_pair_even_decreases
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        hRankFix hC huv hpar hu_med hv_upper h_agree hTie hn4 h_wrong
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hdec.1
    have hmaj : majorityAnswer (C.step P u v) = majorityAnswer C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C u v)
    have h_correct : opinionToAnswer (C u).2 = majorityAnswer C :=
      opinionToAnswer_lower_median_eq_majorityAnswer_even hC hu_med hpar hTie
    have h_u_correct : (C.step P u v u).1.answer = majorityAnswer (C.step P u v) := by
      rw [hmaj]
      have hval := congrFun hC'_eq u
      rw [show (C.step P u v u) =
          (if u = u then ({(C u).1 with answer := opinionToAnswer (C u).2}, (C u).2)
            else if u = v then ({(C v).1 with answer := opinionToAnswer (C u).2}, (C v).2)
            else C u) by simpa [P, PEMProtocolCoupled, PEMProtocol] using hval]
      simp [h_correct]
    have h_u_med' : (C.step P u v u).1.rank.val + 1 = ceilHalf n := by
      have hval := congrFun hC'_eq u
      rw [show (C.step P u v u) =
          (if u = u then ({(C u).1 with answer := opinionToAnswer (C u).2}, (C u).2)
            else if u = v then ({(C v).1 with answer := opinionToAnswer (C u).2}, (C v).2)
            else C u) by simpa [P, PEMProtocolCoupled, PEMProtocol] using hval]
      simp [hceil, hu_med]
    have hGoal : InSswap (C.step P u v) ∧ MedianAnswerCorrect (C.step P u v) := by
      refine ⟨hSwap', ?_⟩
      intro η hη
      have hηu : η = u := by
        apply hSwap'.ranks_inj
        apply Fin.eq_of_val_eq
        have hηval : (C.step P u v η).1.rank.val = ceilHalf n - 1 := by omega
        have huval : (C.step P u v u).1.rank.val = ceilHalf n - 1 := by omega
        exact hηval.trans huval.symm
      subst η
      exact h_u_correct
    exact Probability.ProbHitWithin_one_lower_bound_of_step
      (P := P) hn2 C (fun D => InSswap D ∧ MedianAnswerCorrect D)
      htarget_not huv hGoal

/-- Odd-population median no-swap decision step as a one-step probability
lower bound for decreasing `wrongAnswerCount`. -/
theorem PEM_odd_median_decision_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_max : (C v).1.rank.val + 1 ≠ n)
    (h_rank_gt : (C v).1.rank < (C μ).1.rank)
    (h_timer : 1 ≤ (C μ).1.timer)
    (h_μ_wrong : (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := by
  apply PEM_wrongAnswer_one_step_descent_prob_lower_bound_of_step
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hμv
  simpa [PEMProtocolCoupled, PEMProtocol] using
    (decision_step_at_median_no_swap_odd_decreases
      (n := n) (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hC hμv hpar hμ_med hv_no_med hv_no_max h_rank_gt h_timer h_μ_wrong).2

/-- Odd-population median-wrong decision progress has `ceilHalf n - 1`
ordered good pairs: the wrong median can interact with any lower-rank agent.
This is the quantitative strengthening needed for the `Tswap -> Sdec`
window, not just a single deterministic witness. -/
theorem PEM_odd_median_wrong_lower_rank_decision_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ : Fin n}
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : 1 ≤ (C μ).1.timer)
    (h_μ_wrong : (C μ).1.answer ≠ majorityAnswer C) :
    (((ceilHalf n - 1 : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := by
  classical
  let lowerSet : Finset (Fin n) :=
    Finset.univ.filter fun v : Fin n => (C v).1.rank.val < (C μ).1.rank.val
  let S : Finset (Fin n × Fin n) := lowerSet.image fun v => (μ, v)
  have hμ_rank : (C μ).1.rank.val = ceilHalf n - 1 := by omega
  have hceil_le_n : ceilHalf n ≤ n := by
    unfold ceilHalf
    omega
  have hcardLower : lowerSet.card = ceilHalf n - 1 := by
    have hk : (C μ).1.rank.val ≤ n := Nat.le_of_lt (C μ).1.rank.isLt
    have hcard := time_card_filter_rank_lt hC.toInSrank (k := (C μ).1.rank.val) hk
    simpa [lowerSet, hμ_rank] using hcard
  have hS_card : S.card = ceilHalf n - 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective]
    · exact hcardLower
    · intro a b h
      exact congrArg Prod.snd h
  have hS_sub : S ⊆ Probability.OffDiagonalPairs n := by
    intro p hp
    dsimp [S] at hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨v, hv, hpv⟩
    rw [Probability.mem_offDiagonalPairs]
    rw [← hpv]
    intro hμv
    have hv_lt : (C v).1.rank.val < (C μ).1.rank.val :=
      (Finset.mem_filter.mp hv).2
    have hμ_eq_v : μ = v := by
      simpa using hμv
    subst v
    exact (Nat.lt_irrefl (C μ).1.rank.val) hv_lt
  have hstep : ∀ p ∈ S,
      wrongAnswerCount (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) p.1 p.2) <
        wrongAnswerCount C := by
    intro p hp
    dsimp [S] at hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨v, hv, hpv⟩
    rw [← hpv]
    have hv_lt_val : (C v).1.rank.val < (C μ).1.rank.val :=
      (Finset.mem_filter.mp hv).2
    have hμv : μ ≠ v := by
      intro h
      subst v
      exact (Nat.lt_irrefl (C μ).1.rank.val) hv_lt_val
    have hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
      omega
    have hv_no_max : (C v).1.rank.val + 1 ≠ n := by
      have hv_lt_ceil : (C v).1.rank.val + 1 < ceilHalf n := by omega
      omega
    have h_rank_gt : (C v).1.rank < (C μ).1.rank := by
      exact_mod_cast hv_lt_val
    simpa [PEMProtocolCoupled, PEMProtocol] using
      (decision_step_at_median_no_swap_odd_decreases
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (rankDeltaOSSR_satisfies_fix
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
        hC hμv hpar hμ_med hv_no_med hv_no_max h_rank_gt h_timer h_μ_wrong).2
  have hmass :
      Probability.pairSetMass n hn2 S =
        (((ceilHalf n - 1 : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
    rw [Probability.pairSetMass_eq_card_mul_inv_of_subset n hn2 S hS_sub,
      hS_card]
  calc
    (((ceilHalf n - 1 : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
        = Probability.pairSetMass n hn2 S := hmass.symm
    _ ≤ Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 :=
          Probability.ProbHitWithin_one_lower_bound_of_pairSet
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
            (fun D => wrongAnswerCount D < wrongAnswerCount C)
            (by exact Nat.lt_irrefl (wrongAnswerCount C))
            S hS_sub hstep

/-- Odd-population median-wrong decision reaches the local `Sdec` predicate
(`MedianAnswerCorrect`) in one step with the mass of all lower-rank partners,
while preserving `InSswap`. -/
theorem PEM_odd_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ : Fin n}
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : 1 ≤ (C μ).1.timer)
    (h_μ_wrong : (C μ).1.answer ≠ majorityAnswer C) :
    (((ceilHalf n - 1 : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 := by
  classical
  let lowerSet : Finset (Fin n) :=
    Finset.univ.filter fun v : Fin n => (C v).1.rank.val < (C μ).1.rank.val
  let S : Finset (Fin n × Fin n) := lowerSet.image fun v => (μ, v)
  have hμ_rank : (C μ).1.rank.val = ceilHalf n - 1 := by omega
  have hcardLower : lowerSet.card = ceilHalf n - 1 := by
    have hk : (C μ).1.rank.val ≤ n := Nat.le_of_lt (C μ).1.rank.isLt
    have hcard := time_card_filter_rank_lt hC.toInSrank (k := (C μ).1.rank.val) hk
    simpa [lowerSet, hμ_rank] using hcard
  have hS_card : S.card = ceilHalf n - 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective]
    · exact hcardLower
    · intro a b h
      exact congrArg Prod.snd h
  have hS_sub : S ⊆ Probability.OffDiagonalPairs n := by
    intro p hp
    dsimp [S] at hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨v, hv, hpv⟩
    rw [Probability.mem_offDiagonalPairs]
    rw [← hpv]
    intro hμv
    have hv_lt : (C v).1.rank.val < (C μ).1.rank.val :=
      (Finset.mem_filter.mp hv).2
    have hμ_eq_v : μ = v := by
      simpa using hμv
    subst v
    exact (Nat.lt_irrefl (C μ).1.rank.val) hv_lt
  have hstep : ∀ p ∈ S,
      InSswap (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) p.1 p.2) ∧
        MedianAnswerCorrect
          (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) p.1 p.2) := by
    intro p hp
    dsimp [S] at hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨v, hv, hpv⟩
    rw [← hpv]
    have hv_lt_val : (C v).1.rank.val < (C μ).1.rank.val :=
      (Finset.mem_filter.mp hv).2
    have hμv : μ ≠ v := by
      intro h
      subst v
      exact (Nat.lt_irrefl (C μ).1.rank.val) hv_lt_val
    have hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
      omega
    have hv_no_max : (C v).1.rank.val + 1 ≠ n := by
      have hv_lt_ceil : (C v).1.rank.val + 1 < ceilHalf n := by omega
      omega
    have h_rank_gt : (C v).1.rank < (C μ).1.rank := by
      exact_mod_cast hv_lt_val
    have hRankFix := rankDeltaOSSR_satisfies_fix
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
    have hSwap' : InSswap
        (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v) := by
      simpa [PEMProtocolCoupled, PEMProtocol] using
        (step_at_median_no_swap_odd_preserves_InSswap
          (n := n) (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
          hRankFix hC hμv hpar hμ_med hv_no_med hv_no_max
          h_rank_gt h_timer)
    have hC'_eq :
        C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v =
          fun w =>
            if w = μ then
              ({(C μ).1 with answer := opinionToAnswer (C μ).2}, (C μ).2)
            else if w = v then
              ((C v).1, (C v).2)
            else C w := by
      simpa [PEMProtocolCoupled, PEMProtocol] using
        (step_at_median_no_swap_odd_v_not_max
          (n := n) (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
          hRankFix hμv (hC.allSettled μ) (hC.allSettled v) hpar
          hμ_med hv_no_med hv_no_max h_rank_gt h_timer)
    have hmaj :
        majorityAnswer (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v) =
          majorityAnswer C := by
      simpa [PEMProtocolCoupled, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C μ v)
    have hμ_correct :
        (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v μ).1.answer =
          majorityAnswer (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v) := by
      rw [hmaj, hC'_eq]
      simp [opinionToAnswer_median_eq_majorityAnswer_odd hC hμ_med hpar]
    have hμ_med' :
        (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v μ).1.rank.val + 1 =
          ceilHalf n := by
      rw [hC'_eq]
      simp [hμ_med]
    refine ⟨hSwap', ?_⟩
    intro η hη
    have hημ : η = μ := by
      apply hSwap'.ranks_inj
      apply Fin.eq_of_val_eq
      have hη_med' :
          (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v η).1.rank.val + 1 =
            ceilHalf n := by
        simpa using hη
      have hηval :
          (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v η).1.rank.val =
            ceilHalf n - 1 := by omega
      have hμval :
          (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v μ).1.rank.val =
            ceilHalf n - 1 := by omega
      exact hηval.trans hμval.symm
    subst η
    exact hμ_correct
  have hmass :
      Probability.pairSetMass n hn2 S =
        (((ceilHalf n - 1 : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
    rw [Probability.pairSetMass_eq_card_mul_inv_of_subset n hn2 S hS_sub,
      hS_card]
  calc
    (((ceilHalf n - 1 : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
        = Probability.pairSetMass n hn2 S := hmass.symm
    _ ≤ Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 :=
          Probability.ProbHitWithin_one_lower_bound_of_pairSet
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
            (fun D => InSswap D ∧ MedianAnswerCorrect D)
            (by
              intro hGoal
              exact h_μ_wrong (hGoal.2 μ hμ_med))
            S hS_sub hstep

/-- Odd-population witness form of the median-wrong decision probability
bound.  The lower bound uses all lower-rank partners for the wrong median. -/
theorem PEM_odd_median_wrong_decision_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hpar : ¬ n % 2 = 0)
    (h_med_timer : ∀ μ : Fin n,
      (C μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (C μ).1.timer)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    (((ceilHalf n - 1 : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := by
  obtain ⟨μ, hμ_med, hμ_wrong⟩ := h_med_wrong
  exact PEM_odd_median_wrong_lower_rank_decision_prob_lower_bound
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn2 hn0 hC hpar hμ_med (h_med_timer μ hμ_med) hμ_wrong

/-- Parity-unified median-wrong decision probability bound: if some median is
wrong and median timers are positive, one random interaction decreases
`wrongAnswerCount` with at least the mass of one ordered scheduler pair. -/
theorem PEM_median_wrong_decision_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_med_timer : ∀ μ : Fin n,
      (C μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (C μ).1.timer)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := by
  by_cases hpar : n % 2 = 0
  · exact PEM_even_median_wrong_decision_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC hpar h_med_wrong
  · have hodd :=
      PEM_odd_median_wrong_decision_descent_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hC hpar h_med_timer h_med_wrong
    have hcoef : (1 : ENNReal) ≤ ((ceilHalf n - 1 : ℕ) : ENNReal) := by
      have hnat : 1 ≤ ceilHalf n - 1 := by
        unfold ceilHalf
        omega
      exact_mod_cast hnat
    calc
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹
          = (1 : ENNReal) *
              ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by simp
      _ ≤ ((ceilHalf n - 1 : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
            exact mul_le_mul_left hcoef _
      _ ≤ Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
          (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := hodd

/-- Marginal one-step version of
`PEM_median_wrong_decision_descent_prob_lower_bound`, for phase
composition.  The strict-descent target is false at the start state. -/
theorem PEM_median_wrong_decision_descent_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_med_timer : ∀ μ : Fin n,
      (C μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (C μ).1.timer)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by infer_instance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => wrongAnswerCount D < wrongAnswerCount C
  have hGoal : ¬ Goal C := by
    intro h
    exact Nat.lt_irrefl _ h
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_median_wrong_decision_descent_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC h_med_timer h_med_wrong)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-- Parity-unified `Tswap -> Sdec` one-step probability bound.  If some
median answer is wrong and the median timers are positive, then one scheduler
step reaches the local decision predicate with at least the mass of one
ordered pair, while preserving `InSswap`. -/
theorem PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 := by
  by_cases hpar : n % 2 = 0
  · exact PEM_even_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC hpar h_med_wrong
  · obtain ⟨μ, hμ_med, hμ_wrong⟩ := h_med_wrong
    have hodd :=
      PEM_odd_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hC hpar hμ_med (h_med_timer μ hμ_med) hμ_wrong
    have hcoef : (1 : ENNReal) ≤ ((ceilHalf n - 1 : ℕ) : ENNReal) := by
      have hnat : 1 ≤ ceilHalf n - 1 := by
        unfold ceilHalf
        omega
      exact_mod_cast hnat
    calc
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹
          = (1 : ENNReal) *
              ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by simp
      _ ≤ ((ceilHalf n - 1 : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
            exact mul_le_mul_left hcoef _
      _ ≤ Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
          (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 := hodd

/-- Marginal one-step form of
`PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound`, for phase
composition.  The start state is not already in the target because a median
wrong witness contradicts `MedianAnswerCorrect`. -/
theorem PEM_median_wrong_to_MedianAnswerCorrect_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by classical exact inferInstance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianAnswerCorrect D
  have hGoal : ¬ Goal C := by
    rintro ⟨_, hDec⟩
    rcases h_med_wrong with ⟨μ, hμ, hwrong⟩
    exact hwrong (hDec μ hμ)
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC h_med_timer h_med_wrong)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-- Window amplification for the `Tswap -> Sdec` local phase.  Starting in
`InSswap` with live median timers and with a wrong median answer, within `t`
steps the chain either reaches the local decision predicate or leaves the
timer-live swap region with the usual geometric lower bound. -/
theorem PEM_Tswap_to_MedianAnswerCorrect_or_exit_prob_window
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (h_not_dec : ¬ MedianAnswerCorrect C) :
    ∀ t : ℕ,
      1 - (1 - ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ^ t ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
          (fun D =>
            (InSswap D ∧ MedianAnswerCorrect D) ∨
              ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)) t := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  apply Probability.ProbHitWithin_ge_one_sub_pow_of_local_one_lower_bound
    (P := P) (hn := hn2) (C₀ := C)
    (Region := fun D => InSswap D ∧ MedianTimerAtLeast 1 D)
    (Goal := fun D => InSswap D ∧ MedianAnswerCorrect D)
    (p := ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
  · exact ⟨hC, h_med_timer⟩
  · intro hGoal
    exact h_not_dec hGoal.2
  · intro D hRegionD hGoalD
    have h_med_wrong :
        ∃ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n ∧
          (D μ).1.answer ≠ majorityAnswer D := by
      rw [← not_MedianAnswerCorrect_iff_exists_median_wrong]
      intro hDec
      exact hGoalD ⟨hRegionD.1, hDec⟩
    have hbase :
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
          Probability.ProbHitWithin P hn2 D
            (fun E => InSswap E ∧ MedianAnswerCorrect E) 1 := by
      simpa [P] using
        (PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn2 hn0 hn4 hRegionD.1 hRegionD.2 h_med_wrong)
    have hTargetD :
        ¬ ((fun E =>
          (InSswap E ∧ MedianAnswerCorrect E) ∨
            ¬ (InSswap E ∧ MedianTimerAtLeast 1 E)) D) := by
      intro hTarget
      rcases hTarget with hGoal | hExit
      · exact hGoalD hGoal
      · exact hExit hRegionD
    have hmono :
        Probability.ProbHitWithin P hn2 D
            (fun E => InSswap E ∧ MedianAnswerCorrect E) 1 ≤
          Probability.ProbHitWithin P hn2 D
            (fun E =>
              (InSswap E ∧ MedianAnswerCorrect E) ∨
                ¬ (InSswap E ∧ MedianTimerAtLeast 1 E)) 1 :=
      Probability.ProbHitWithin_one_mono_goal
        (P := P) (hn := hn2) (C₀ := D)
        (Goal₁ := fun E => InSswap E ∧ MedianAnswerCorrect E)
        (Goal₂ := fun E =>
          (InSswap E ∧ MedianAnswerCorrect E) ∨
            ¬ (InSswap E ∧ MedianTimerAtLeast 1 E))
        hGoalD hTargetD (fun E h => Or.inl h)
    exact le_trans hbase hmono

/-- Table-2 Phase-3 live-region wrapper.

This is the provable form of the `Sswap -> Sdec` window from the existing
one-step median-wrong lemma: while the median timers are live, the process
geometrically reaches `InSswap ∧ MedianAnswerCorrect`; otherwise the window
has exited the live swap region, which must be handled by a surrounding
phase-composition argument. -/
theorem PEM_phase3_live_or_exit_window
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (h_not_dec : ¬ MedianAnswerCorrect C) :
    1 - (1 - ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ^
        (4 * n * n) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D =>
          (InSswap D ∧ MedianAnswerCorrect D) ∨
            ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (4 * n * n) := by
  simpa using
    (PEM_Tswap_to_MedianAnswerCorrect_or_exit_prob_window
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC h_med_timer h_not_dec (4 * n * n))

/-- Same Phase-3 decision-or-exit window with the paper Lemma-9 live-timer
entry condition.  The remaining Lemma-9 work is to separate the decision
success mass from the early timer-expiration exit mass. -/
theorem PEM_phase3_timer28_live_or_exit_window
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 28 C)
    (h_not_dec : ¬ MedianAnswerCorrect C) :
    1 - (1 - ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ^
        (4 * n * n) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D =>
          (InSswap D ∧ MedianAnswerCorrect D) ∨
            ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (4 * n * n) := by
  exact PEM_phase3_live_or_exit_window
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn2 hn0 hn4 hC
    (MedianTimerAtLeast.mono (n := n) (a := 1) (b := 28) (by norm_num)
      h_med_timer)
    h_not_dec

private theorem real_one_sub_one_div_pow_self_le_half {m : ℕ} (hm : 2 ≤ m) :
    (1 - (1 / (m : ℝ))) ^ m ≤ (1 / 2 : ℝ) := by
  have hm_pos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hm_gt_one : (1 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hm)
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  set q : ℝ := 1 - (1 / (m : ℝ))
  have hq_pos : 0 < q := by
    dsimp [q]
    field_simp [ne_of_gt hm_pos]
    nlinarith
  have hbase : q⁻¹ = 1 + 1 / ((m : ℝ) - 1) := by
    dsimp [q]
    field_simp [ne_of_gt hm_pos, ne_of_gt hm1_pos]
    ring
  have hbern :
      1 + (m : ℝ) * (1 / ((m : ℝ) - 1)) ≤
        (1 + 1 / ((m : ℝ) - 1)) ^ m := by
    exact one_add_mul_le_pow (a := 1 / ((m : ℝ) - 1)) (n := m)
      (by
        have hpos : 0 < 1 / ((m : ℝ) - 1) := one_div_pos.mpr hm1_pos
        linarith)
  have h2_le_linear :
      (2 : ℝ) ≤ 1 + (m : ℝ) * (1 / ((m : ℝ) - 1)) := by
    have hfrac : (1 : ℝ) ≤ (m : ℝ) / ((m : ℝ) - 1) := by
      rw [one_le_div hm1_pos]
      linarith
    rw [mul_one_div]
    linarith
  have h2_inv : (2 : ℝ) ≤ (q ^ m)⁻¹ := by
    rw [← inv_pow, hbase]
    exact h2_le_linear.trans hbern
  have h := inv_anti₀ (by norm_num : (0 : ℝ) < 2) h2_inv
  simpa [one_div] using h

private theorem ennreal_one_sub_inv_nat_pow_self_le_half {m : ℕ} (hm : 2 ≤ m) :
    (1 - ((m : ENNReal)⁻¹)) ^ m ≤ (2 : ENNReal)⁻¹ := by
  rw [← ENNReal.toReal_le_toReal]
  · rw [ENNReal.toReal_pow]
    rw [ENNReal.toReal_sub_of_le]
    · simpa [one_div] using real_one_sub_one_div_pow_self_le_half hm
    · exact ENNReal.inv_le_one.mpr
        (by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hm))
    · exact ENNReal.one_ne_top
  · simp
  · simp

private theorem ennreal_inv_two_pow_four_le_three_inv_eight :
    ((2 : ENNReal)⁻¹) ^ 4 ≤ (3 : ENNReal) * (8 : ENNReal)⁻¹ := by
  have h2 : ((2 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have h8 : ((8 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have hleft : (((2 : ENNReal)⁻¹) ^ 4) ≠ ⊤ := by simp [h2]
  have hright : ((3 : ENNReal) * (8 : ENNReal)⁻¹) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top 3) h8
  rw [← ENNReal.toReal_le_toReal hleft hright]
  simp [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_mul]
  norm_num

private theorem ennreal_half_add_eighth_add_three_eighth_le_one :
    ((2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹) +
      (3 : ENNReal) * (8 : ENNReal)⁻¹ ≤ 1 := by
  have h2 : ((2 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have h8 : ((8 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have hsum : ((2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨h2, h8⟩
  have hmul : ((3 : ENNReal) * (8 : ENNReal)⁻¹) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top 3) h8
  have hleft :
      (((2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹) +
        (3 : ENNReal) * (8 : ENNReal)⁻¹) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hsum, hmul⟩
  rw [← ENNReal.toReal_le_toReal hleft ENNReal.one_ne_top]
  rw [ENNReal.toReal_add hsum hmul]
  rw [ENNReal.toReal_add h2 h8]
  simp [ENNReal.toReal_inv, ENNReal.toReal_mul]
  norm_num

/-- The geometric part of the Phase-3 decision-or-exit window is already
larger than `1/2 + 1/8` for `n ≥ 4`. -/
theorem PEM_phase3_geometric_live_or_exit_lower_bound
    {n : ℕ} (hn4 : 4 ≤ n) :
    (2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹ ≤
      1 - (1 - ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ^
        (4 * n * n) := by
  let m := n * (n - 1)
  let q : ENNReal := 1 - ((m : ENNReal)⁻¹)
  have hm : 2 ≤ m := by
    dsimp [m]
    calc
      2 ≤ 4 := by norm_num
      _ ≤ n * (n - 1) := by
        exact Nat.mul_le_mul hn4 (by omega : 1 ≤ n - 1)
  have hq_le_one : q ≤ 1 := by
    dsimp [q]
    exact tsub_le_self
  have hqm : q ^ m ≤ (2 : ENNReal)⁻¹ := by
    simpa [q, m] using ennreal_one_sub_inv_nat_pow_self_le_half hm
  have hq4m : q ^ (4 * m) ≤ ((2 : ENNReal)⁻¹) ^ 4 := by
    rw [show 4 * m = m * 4 by ring, pow_mul]
    exact ENNReal.pow_le_pow_left hqm
  have htime : 4 * m ≤ 4 * n * n := by
    dsimp [m]
    rw [show 4 * (n * (n - 1)) = 4 * n * (n - 1) by ring]
    exact Nat.mul_le_mul_left (4 * n) (Nat.sub_le n 1)
  have hfail :
      q ^ (4 * n * n) ≤ (3 : ENNReal) * (8 : ENNReal)⁻¹ := by
    exact (pow_le_pow_of_le_one (zero_le q) hq_le_one htime).trans
      (hq4m.trans ennreal_inv_two_pow_four_le_three_inv_eight)
  have hsum :
      ((2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹) + q ^ (4 * n * n) ≤ 1 := by
    exact (add_le_add_right hfail ((2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹)).trans
      ennreal_half_add_eighth_add_three_eighth_le_one
  have hthree_ne_top : ((3 : ENNReal) * (8 : ENNReal)⁻¹) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.natCast_ne_top 3
    · rw [ENNReal.inv_ne_top]
      norm_num
  have hqpow_ne_top : q ^ (4 * n * n) ≠ ⊤ :=
    ne_top_of_le_ne_top hthree_ne_top hfail
  simpa [q, m] using ENNReal.le_sub_of_add_le_right hqpow_ne_top hsum

/-- Phase-3 subtraction wrapper.

The existing local-good-pair argument gives a lower bound for reaching
`decision ∨ exit-live-region`.  If the early live-region exit probability is
at most `1/2`, and the geometric lower bound is at least `1/2 + 1/8`, the
finite-prefix union bound leaves at least `1/8` probability for hitting the
live decision predicate. -/
theorem PEM_phase3_live_decision_hit_lower_bound_of_exit_le_half
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 28 C)
    (h_not_dec : ¬ MedianAnswerCorrect C)
    (hExit :
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (4 * n * n) ≤ (2 : ENNReal)⁻¹) :
    (8 : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D)
        (4 * n * n) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let A : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
  let B : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
  have hGoalEq :
      (fun D : Config (AgentState n) Opinion n =>
          (InSswap D ∧ MedianAnswerCorrect D) ∨
            ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)) =
        (fun D => A D ∨ B D) := by
    funext D
    apply propext
    constructor
    · intro h
      rcases h with hdec | hexit
      · by_cases htimer : MedianTimerAtLeast 1 D
        · exact Or.inl ⟨hdec.1, hdec.2, htimer⟩
        · exact Or.inr (fun hLive => htimer hLive.2)
      · exact Or.inr hexit
    · intro h
      rcases h with hdec | hexit
      · exact Or.inl ⟨hdec.1, hdec.2.1⟩
      · exact Or.inr hexit
  have hor :
      (2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin P hn2 C (fun D => A D ∨ B D) (4 * n * n) := by
    calc
      (2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹
          ≤ 1 - (1 - ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ^
              (4 * n * n) :=
          PEM_phase3_geometric_live_or_exit_lower_bound hn4
      _ ≤ Probability.ProbHitWithin P hn2 C
            (fun D =>
              (InSswap D ∧ MedianAnswerCorrect D) ∨
                ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
            (4 * n * n) :=
          PEM_phase3_timer28_live_or_exit_window
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn2 hn0 hn4 hC h_med_timer h_not_dec
      _ = Probability.ProbHitWithin P hn2 C (fun D => A D ∨ B D)
            (4 * n * n) := by rw [hGoalEq]
  exact
    Probability.ProbHitWithin_left_ge_inv8_of_or_ge_half_add_inv8_and_right_le_half
      P hn2 C A B (4 * n * n) hor (by simpa [P, B] using hExit)

/-- Phase-3 subtraction wrapper with an enlarged target predicate. -/
theorem PEM_phase3_live_decision_hit_lower_bound_of_exit_le_half_mono
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (G : Config (AgentState n) Opinion n → Prop)
    (hG : ∀ D : Config (AgentState n) Opinion n,
      InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D → G D)
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 28 C)
    (h_not_dec : ¬ MedianAnswerCorrect C)
    (hExit :
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (4 * n * n) ≤ (2 : ENNReal)⁻¹) :
    (8 : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C G
        (4 * n * n) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let A : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
  exact
    (PEM_phase3_live_decision_hit_lower_bound_of_exit_le_half
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC h_med_timer h_not_dec hExit).trans
      (Probability.ProbHitWithin_mono_goal P hn2 C A G hG (4 * n * n))

/-- Standalone Phase-3 endpoint theorem.

The remaining probabilistic work for Lemma 9 is exactly the joint-event
hypothesis: with probability at least `1/8`, the finite prefix has hit the
decision predicate and the endpoint of the whole `4*n*n` window still lies in
the timer-live `Sdec` phase predicate.  This wrapper converts that path-level
joint event into the exact-time `probReached` hypothesis required by the
Table-2 phase composition. -/
theorem PEM_decision_phase_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSdecTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (_hC : InSswap C)
    (_h_med_timer : MedianTimerAtLeast 28 C)
    (_h_timer_upper : MedianTimerAtMost (7 * (Rmax + 4)) C)
    (_h_not_consensus : ¬ IsConsensusConfig C)
    (hJoint :
      (8 : ENNReal)⁻¹ ≤
        Probability.probHitAndIn
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C
          (fun D => InSswap D ∧ MedianAnswerCorrect D)
          (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n)) :
    (8 : ENNReal)⁻¹ ≤
      Probability.probReached
        (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C
        (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n) := by
  exact Probability.probReached_ge_of_probHitAndIn
    (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
    (by omega : 2 ≤ n) C
    (fun D => InSswap D ∧ MedianAnswerCorrect D)
    (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n)
    ((8 : ENNReal)⁻¹) hJoint

/-- Expected sequential-time form of
`PEM_Tswap_to_MedianAnswerCorrect_or_exit_prob_window`. -/
theorem PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (h_not_dec : ¬ MedianAnswerCorrect C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
      (fun D =>
        (InSswap D ∧ MedianAnswerCorrect D) ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)) ≤
      (((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  apply Probability.expectedHittingTime_le_inv_of_local_one_lower_bound
    (P := P) (hn := hn2) (C₀ := C)
    (Region := fun D => InSswap D ∧ MedianTimerAtLeast 1 D)
    (Goal := fun D => InSswap D ∧ MedianAnswerCorrect D)
    (p := ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
  · exact ⟨hC, h_med_timer⟩
  · intro hGoal
    exact h_not_dec hGoal.2
  · intro D hRegionD hGoalD
    have h_med_wrong :
        ∃ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n ∧
          (D μ).1.answer ≠ majorityAnswer D := by
      rw [← not_MedianAnswerCorrect_iff_exists_median_wrong]
      intro hDec
      exact hGoalD ⟨hRegionD.1, hDec⟩
    have hbase :
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
          Probability.ProbHitWithin P hn2 D
            (fun E => InSswap E ∧ MedianAnswerCorrect E) 1 := by
      simpa [P] using
        (PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn2 hn0 hn4 hRegionD.1 hRegionD.2 h_med_wrong)
    have hTargetD :
        ¬ ((fun E =>
          (InSswap E ∧ MedianAnswerCorrect E) ∨
            ¬ (InSswap E ∧ MedianTimerAtLeast 1 E)) D) := by
      intro hTarget
      rcases hTarget with hGoal | hExit
      · exact hGoalD hGoal
      · exact hExit hRegionD
    have hmono :
        Probability.ProbHitWithin P hn2 D
            (fun E => InSswap E ∧ MedianAnswerCorrect E) 1 ≤
          Probability.ProbHitWithin P hn2 D
            (fun E =>
              (InSswap E ∧ MedianAnswerCorrect E) ∨
                ¬ (InSswap E ∧ MedianTimerAtLeast 1 E)) 1 :=
      Probability.ProbHitWithin_one_mono_goal
        (P := P) (hn := hn2) (C₀ := D)
        (Goal₁ := fun E => InSswap E ∧ MedianAnswerCorrect E)
        (Goal₂ := fun E =>
          (InSswap E ∧ MedianAnswerCorrect E) ∨
            ¬ (InSswap E ∧ MedianTimerAtLeast 1 E))
        hGoalD hTargetD (fun E h => Or.inl h)
    exact le_trans hbase hmono

/-- Version of `PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le` that
also covers the already-decided case. -/
theorem PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le_live
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
      (fun D =>
        (InSswap D ∧ MedianAnswerCorrect D) ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)) ≤
      (((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ := by
  classical
  by_cases h_dec : MedianAnswerCorrect C
  · rw [Probability.expectedHittingTime_eq_zero_of_goal
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
      (fun D =>
        (InSswap D ∧ MedianAnswerCorrect D) ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
      (Or.inl ⟨hC, h_dec⟩)]
    exact zero_le _
  · exact PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC h_med_timer h_dec

private theorem ennreal_inv_two_eq_inv_four_add_inv_four :
    ((2 : ENNReal)⁻¹) = ((4 : ENNReal)⁻¹) + ((4 : ENNReal)⁻¹) := by
  have h2 : ((2 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have h4 : ((4 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have hsum : ((4 : ENNReal)⁻¹ + (4 : ENNReal)⁻¹) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨h4, h4⟩
  rw [← ENNReal.toReal_eq_toReal_iff' h2 hsum]
  rw [ENNReal.toReal_add h4 h4]
  simp [ENNReal.toReal_inv]
  norm_num

theorem ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4
    {n : ℕ} (P : Protocol (AgentState n) Opinion Output) (hn : 2 ≤ n)
    (C₀ : Config (AgentState n) Opinion n)
    (A B : Config (AgentState n) Opinion n → Prop)
    [DecidablePred A] [DecidablePred B] (t : ℕ)
    (hor : ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t)
    (hB : Probability.ProbHitWithin P hn C₀ B t ≤ (4 : ENNReal)⁻¹) :
    ((4 : ENNReal)⁻¹) ≤ Probability.ProbHitWithin P hn C₀ A t := by
  let x := Probability.ProbHitWithin P hn C₀ A t
  let y := Probability.ProbHitWithin P hn C₀ B t
  have hOr :
      Probability.ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t ≤ x + y := by
    simpa [x, y] using Probability.ProbHitWithin_union_le P hn C₀ A B t
  have hhalf_le : ((2 : ENNReal)⁻¹) ≤ x + (4 : ENNReal)⁻¹ := by
    calc
      ((2 : ENNReal)⁻¹)
          ≤ Probability.ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t := hor
      _ ≤ x + y := hOr
      _ ≤ x + (4 : ENNReal)⁻¹ := by
        exact add_le_add_right (show y ≤ (4 : ENNReal)⁻¹ from hB) x
  have hquarter_ne_top : ((4 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  rw [ennreal_inv_two_eq_inv_four_add_inv_four] at hhalf_le
  rw [add_comm x ((4 : ENNReal)⁻¹)] at hhalf_le
  exact (ENNReal.add_le_add_iff_left hquarter_ne_top).mp hhalf_le

/-- Decision-only Phase-3 lower bound from the expectation-to-`decision ∨ exit`
lemma plus a finite-window union-bound subtraction.

This is intentionally conditional on an exit upper bound; the remaining
probabilistic work is to control the probability of leaving the live swap
region before the decision hit. -/
theorem PEM_phase3_decision_hit_lower_bound_of_exit_le_quarter_from_expected
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (hExit :
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * n * (n - 1)) ≤ (4 : ENNReal)⁻¹) :
    (4 : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D)
        (2 * n * (n - 1)) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let A : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianAnswerCorrect D
  let B : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
  let Goal : Config (AgentState n) Opinion n → Prop := fun D => A D ∨ B D
  have hE₀ :
      Probability.expectedHittingTime P hn2 C Goal ≤
        (((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ := by
    simpa [P, Goal, A, B] using
      (PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le_live
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC h_med_timer)
  have hE :
      Probability.expectedHittingTime P hn2 C Goal ≤
        ((n * (n - 1) : ℕ) : ENNReal) := by
    simpa using hE₀
  have hWindow : 2 * (n * (n - 1)) ≤ 2 * n * (n - 1) + 1 := by
    nlinarith
  have hor :
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C Goal (2 * n * (n - 1)) :=
    Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
      P hn2 C Goal hE hWindow
  have hA :
      ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C A (2 * n * (n - 1)) :=
    ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4
      P hn2 C A B (2 * n * (n - 1))
      (by simpa [Goal, A, B] using hor)
      (by simpa [P, B] using hExit)
  simpa [P, A]

/-- Live Phase-3 decision lower bound from the expectation-to-`decision ∨ exit`
lemma plus finite-window union-bound subtraction.

This is the propagation-ready version: the left target retains the
`MedianTimerAtLeast 1` hypothesis.  Any decision hit without the timer-live
condition is charged to the exit event, so the same union subtraction applies. -/
theorem PEM_phase3_live_decision_hit_lower_bound_of_exit_le_quarter_from_expected
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (hExit :
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * n * (n - 1)) ≤ (4 : ENNReal)⁻¹) :
    (4 : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D)
        (2 * n * (n - 1)) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let A : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
  let B : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => (InSswap D ∧ MedianAnswerCorrect D) ∨ B D
  have hGoalEq :
      Goal = (fun D => A D ∨ B D) := by
    funext D
    apply propext
    constructor
    · intro h
      rcases h with hdec | hexit
      · by_cases htimer : MedianTimerAtLeast 1 D
        · exact Or.inl ⟨hdec.1, hdec.2, htimer⟩
        · exact Or.inr (fun hLive => htimer hLive.2)
      · exact Or.inr hexit
    · intro h
      rcases h with hdec | hexit
      · exact Or.inl ⟨hdec.1, hdec.2.1⟩
      · exact Or.inr hexit
  have hE₀ :
      Probability.expectedHittingTime P hn2 C Goal ≤
        (((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ := by
    simpa [P, Goal, B] using
      (PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le_live
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC h_med_timer)
  have hE :
      Probability.expectedHittingTime P hn2 C Goal ≤
        ((n * (n - 1) : ℕ) : ENNReal) := by
    simpa using hE₀
  have hWindow : 2 * (n * (n - 1)) ≤ 2 * n * (n - 1) + 1 := by
    nlinarith
  have hor :
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C Goal (2 * n * (n - 1)) :=
    Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
      P hn2 C Goal hE hWindow
  have hA :
      ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C A (2 * n * (n - 1)) :=
    ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4
      P hn2 C A B (2 * n * (n - 1))
      (by simpa [hGoalEq] using hor)
      (by simpa [P, B] using hExit)
  simpa [P, A]

/-- Conditional Phase-C composition.

Once the exit probability from the live swap region is bounded by `1/4`, the
decision lemma above gives a `1/4` chance to hit a live correct median.  Any
uniform propagation window lower bound from such live decision states then
composes by strong Markov. -/
theorem PEM_consensus_ProbHitWithin_from_decision_exit_and_propagation
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (IsConsensusConfig :
      Config (AgentState n) Opinion n → Prop)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (hExit :
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * n * (n - 1)) ≤ (4 : ENNReal)⁻¹)
    (hPropagation :
      ∀ D : Config (AgentState n) Opinion n,
        InSswap D →
        MedianAnswerCorrect D →
        MedianTimerAtLeast 1 D →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 D
              IsConsensusConfig (20 * Rmax * n * n)) :
    ((4 : ENNReal)⁻¹) * ((1280 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        IsConsensusConfig ((2 * n * (n - 1)) + (20 * Rmax * n * n)) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let DecLive : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
  have hDecision :
      ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C DecLive (2 * n * (n - 1)) := by
    simpa [P, DecLive] using
      (PEM_phase3_live_decision_hit_lower_bound_of_exit_le_quarter_from_expected
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC h_med_timer hExit)
  have hProp : ∀ D : Config (AgentState n) Opinion n, DecLive D →
      ((1280 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 D IsConsensusConfig
          (20 * Rmax * n * n) := by
    intro D hD
    exact hPropagation D hD.1 hD.2.1 hD.2.2
  simpa [P, DecLive] using
    (Probability.ProbHitWithin_add_ge_mul P hn2 C
      DecLive IsConsensusConfig
      (2 * n * (n - 1)) (20 * Rmax * n * n)
      ((4 : ENNReal)⁻¹) ((1280 : ENNReal)⁻¹)
      hDecision hProp)

/-- Reservoir-aware median-wrong probability bound: under `ResAns`, a
median-wrong decision step gives a one-step scheduler lower bound for
returning to `InSswap ∧ ResAns` with strictly smaller `phiCount`. -/
theorem PEM_median_wrong_resAns_phi_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (hRes : ResAns (majorityAnswer C) C)
    (h_med_timer : ∀ μ : Fin n,
      (C μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (C μ).1.timer)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D =>
          InSswap D ∧
          ResAns (majorityAnswer D) D ∧
          phiCount D < phiCount C) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  obtain ⟨p, hSwap', hRes', _hTimer', hWrongDec⟩ :=
    median_wrong_step_resAns_decrease_tieaware
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
      hn4 hC hRes h_med_timer h_med_wrong
  have hp_ne : p.1 ≠ p.2 := by
    intro hp_eq
    have hstep_eq :
        C.step P p.1 p.2 = C := by
      rcases p with ⟨u, v⟩
      dsimp at hp_eq
      subst v
      simp [Config.step]
    have hWrongDecP :
        wrongAnswerCount (C.step P p.1 p.2) < wrongAnswerCount C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hWrongDec
    rw [hstep_eq] at hWrongDecP
    exact (Nat.lt_irrefl (wrongAnswerCount C)) hWrongDecP
  have hPhiDec :
      phiCount (C.step P p.1 p.2) < phiCount C := by
    have hResP :
        ResAns (majorityAnswer (C.step P p.1 p.2)) (C.step P p.1 p.2) := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hRes'
    have hWrongDecP :
        wrongAnswerCount (C.step P p.1 p.2) < wrongAnswerCount C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hWrongDec
    rw [phiCount_eq_wrongAnswerCount_of_resAns hResP,
      phiCount_eq_wrongAnswerCount_of_resAns hRes]
    exact hWrongDecP
  apply Probability.ProbHitWithin_one_lower_bound_of_step
    (P := P) hn2 C
    (fun D =>
      InSswap D ∧
      ResAns (majorityAnswer D) D ∧
      phiCount D < phiCount C)
  · intro hGoal
    exact (Nat.lt_irrefl (phiCount C)) hGoal.2.2
  · exact hp_ne
  · have hSwapP : InSswap (C.step P p.1 p.2) := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hSwap'
    have hResP :
        ResAns (majorityAnswer (C.step P p.1 p.2)) (C.step P p.1 p.2) := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hRes'
    exact ⟨hSwapP, hResP, hPhiDec⟩

/-- Marginal one-step form of
`PEM_median_wrong_resAns_phi_descent_prob_lower_bound`. -/
theorem PEM_median_wrong_resAns_phi_descent_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (hRes : ResAns (majorityAnswer C) C)
    (h_med_timer : ∀ μ : Fin n,
      (C μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (C μ).1.timer)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by classical exact inferInstance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D =>
          InSswap D ∧
          ResAns (majorityAnswer D) D ∧
          phiCount D < phiCount C)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      InSswap D ∧
      ResAns (majorityAnswer D) D ∧
      phiCount D < phiCount C
  have hGoal : ¬ Goal C := by
    intro h
    exact (Nat.lt_irrefl (phiCount C)) h.2.2
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_median_wrong_resAns_phi_descent_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC hRes h_med_timer h_med_wrong)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

end SSEM
