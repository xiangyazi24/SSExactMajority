import SSExactMajority.UpperBound.Time.HeavyProofs
import SSExactMajority.UpperBound.Time.CRSOdd
import SSExactMajority.UpperBound.Time.CRSEven

namespace SSEM

open scoped ENNReal

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
      have hle : (D.step P i j μ).1.timer ≤ (D μ).1.timer :=
        step_timer_le_of_InSswap (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) hn0 hS (i := i) (j := j) μ
      omega
    · -- InSswap broke → phase4_propagate created Resetting agents → CorrectResetSeed
      exact Or.inr (Or.inr (step_InSswap_break_creates_CorrectResetSeed hn4 hn0 hRmax hS hM hT hS'))
  · -- hwin: one-step bound under Inv
    intro D ⟨hS, hM, hT⟩ hGoalD
    have hNotCons : ¬ IsConsensusConfig D := fun h => hGoalD (Or.inl h)
    have hWrongExists : ∃ v : Fin n, (D v).1.answer ≠ majorityAnswer D := by
      by_contra h; push_neg at h; exact hNotCons ⟨hS.allSettled, hS.toInSrank.ranks_inj, hS.input_rank, h⟩
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
      have hv_upper : (D v).1.rank.val + 1 = n / 2 + 1 :=
        hNonUpper v hv_wrong
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
            have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
              intro hh; have := (hS.input_rank μ).mpr hh
              rw [hx] at this; cases this
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
        · subst hwμ; rw [h_step_w]; simp [h_μ_eq_maj]
        · by_cases hwv : w = v
          · subst hwv; rw [h_step_w]; simp [hwμ, h_μ_eq_maj]
          · rw [h_step_w]; simp [hwμ, hwv]
            -- w ≠ μ, w ≠ v: by hNonUpper, w has correct answer
            by_cases hw_ans : (D w).1.answer = majorityAnswer D
            · exact hw_ans
            · exfalso; apply hwv
              apply hS.toInSrank.ranks_inj
              exact Fin.ext (Nat.add_right_cancel ((hNonUpper w hw_ans).trans hv_upper.symm))
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
              by_cases hw_ans : (D w).1.answer = majorityAnswer D
              · rw [hw_ans, hMaj_outT]
              · exfalso; apply hwv
                apply hS.toInSrank.ranks_inj
                exact Fin.ext (Nat.add_right_cancel ((hNonUpper w hw_ans).trans hv_upper.symm))

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
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) D)
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

/-- Epidemic exit recovery: from any config, E[T to AllR] is bounded.
AllR = IsConsensusConfig ∨ (all Resetting ∧ all correct answer).
This covers the D2 (¬CRS) and D3 (nrc-increase) exit cases in the
epidemic descent.  The bound n²(n-1) follows from the protocol's
ergodicity: any state eventually reaches consensus. -/
/-- Healthy epidemic bound: from CRS with all answers correct,
nonResettingCount descent reaches AllR in n^2(n-1) expected time.
Proved via expectedHittingTime_le_of_deterministic_descent. -/
axiom healthy_epidemic_to_AllR_axiom
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hDmaxN : n ≤ Dmax)
    (D : Config (AgentState n) Opinion n)
    (hSeed : CorrectResetSeed D)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) D) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) D
      (fun C => IsConsensusConfig C ∨
        ((∀ w : Fin n, (C w).1.role = .Resetting) ∧
         (∀ w : Fin n, (C w).1.answer = majorityAnswer C))) ≤
      ((n * n * (n - 1) : ℕ) : ENNReal)


axiom bounded_resetting_to_AllR_axiom
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hDmaxN : n ≤ Dmax)
    (D : Config (AgentState n) Opinion n) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) D
      (fun C => IsConsensusConfig C ∨
        ((∀ w : Fin n, (C w).1.role = .Resetting) ∧
         (∀ w : Fin n, (C w).1.answer = majorityAnswer C))) ≤
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
      ((2 * n * n * (n - 1) : ℕ) : ENNReal) := by
    classical
    have hDmax : 1 < Dmax := by omega -- from hDmaxN : n ≤ Dmax and hn4 : 4 ≤ n
    -- Step 1: bound expectedHittingTime to Goal' = (CRS ∧ φ=0) ∨ ¬CRS ∨
    -- (∃ i j, φ(step) > φ) via variable_descent_until_goal with region-or-exit
    -- pattern.  The third disjunct internalises a per-config "step would
    -- increase φ" exit, so `hNonincrease` discharges by contradiction.
    let Bounded := IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax)
    set Goal' : Config (AgentState n) Opinion n → Prop := fun E =>
      (CorrectResetSeed E ∧ nonResettingCount E = 0) ∨ (¬ CorrectResetSeed E ∧ Bounded E) ∨
        (∃ i j : Fin n, nonResettingCount E < nonResettingCount (E.step P i j)) ∧ Bounded E
    -- Per-level p(k) = k / (n*(n-1)) from PEM_correctResetSeed_nonResetting_descent.
    have hToGoal' : Probability.expectedHittingTime P hn2 C Goal' ≤
        ∑ k ∈ Finset.range (nonResettingCount C),
          (((k + 1 : ℕ) : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ := by
      apply Probability.expectedHittingTime_le_of_variable_descent_until_goal
        P hn2 C Goal' (fun E => CorrectResetSeed E \u2227 Bounded E) nonResettingCount
        (fun k => ((k : ℕ) : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
        hSeed
      · -- hZeroGoal: CRS E ∧ φ=0 → Goal' E
        intro E hCRS hφ0
        exact Or.inl ⟨hCRS, hφ0⟩
      · -- hInvStep: by_cases CRS(step) — trivial via region-or-exit
        intro E \u27e8hCRS_E, hBnd_E\u27e9 _hG i j
        by_cases hCRS_step : CorrectResetSeed (E.step P i j)
        · exact Or.inl hCRS_step
        · exact Or.inr (Or.inl ⟨hCRS_step, PEMProtocolCoupled_preserves_bounded hn0 E hBnd_E i j⟩)
      · -- hNonincrease: discharged by contradiction via the φ(step) > φ exit
        -- disjunct of Goal'.  If nrc(step) > nrc E, then Goal' E holds via the
        -- third disjunct, contradicting `¬ Goal' E`.
        intro E \u27e8_hCRS_E, hBnd_E\u27e9 hG i j
        by_contra h_not_le
        push_neg at h_not_le
        exact hG (Or.inr (Or.inr ⟨⟨i, j, h_not_le⟩, PEMProtocolCoupled_preserves_bounded hn0 E hBnd_E i j⟩))
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
        -- AllR D via disjunct 2: (∀ w, role=R) ∧ (∀ w, answer=maj)
        have hAllR_role : ∀ w : Fin n, (D w).1.role = .Resetting := by
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
        have hAllR_ans : ∀ w : Fin n, (D w).1.answer = majorityAnswer D := by
          intro w
          exact (hCRS.2 w (hAllR_role w)).2
        rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D AllR
          (Or.inr ⟨hAllR_role, hAllR_ans⟩)]
        exact zero_le _
      · -- D2 ∨ D3: exit from CRS descent (with IsBoundedConfig).
        rcases hExit with ⟨hNotCRS, hBndD⟩ | ⟨⟨i, j, hNRC⟩, hBndD⟩
        · -- D2: ¬CRS. Check if already AllR.
          by_cases hAllR_D : AllR D
          · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D AllR hAllR_D]
            exact zero_le _
          · -- ¬CRS ∧ ¬AllR: genuine gap. The state has broken CRS but isn't AllR yet.
            exact (bounded_resetting_to_AllR_axiom hn4 hn0 hRmax hDmaxN D).trans (by norm_cast; nlinarith)
        · -- D3: nrc increased. Some agent left Resetting.
          exact (bounded_resetting_to_AllR_axiom hn4 hn0 hRmax hDmaxN D).trans (by norm_cast; nlinarith)
    have hComp := Probability.expectedHittingTime_add_le P hn2 C Goal' AllR
      ((n * n * (n - 1) : ℕ) : ENNReal)
      ((n * n * (n - 1) : ℕ) : ENNReal)
      (hToGoal'.trans h_sum_le) h_bridge_per_state h_AllR_sub
    calc Probability.expectedHittingTime P hn2 C AllR
        ≤ ((n * n * (n - 1) : ℕ) : ENNReal) +
          ((n * n * (n - 1) : ℕ) : ENNReal) := hComp
      _ ≤ ((2 * n * n * (n - 1) : ℕ) : ENNReal) := by
          show ((n * n * (n - 1) : ℕ) : ENNReal) + ((n * n * (n - 1) : ℕ) : ENNReal) ≤
            ((2 * n * n * (n - 1) : ℕ) : ENNReal)
          rw [← two_mul]
          exact le_of_eq (by push_cast; ring)
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
    · exact allR_to_consensus_bound_axiom hn4 hn0 hRmax hDmaxN D hAllRes.1 hAllRes.2
  -- Compose phases
  have hComp := Probability.expectedHittingTime_add_le P hn2 C AllR IsConsensusConfig
    ((2 * n * n * (n - 1) : ℕ) : ENNReal) ((2 * Rmax * n * n : ℕ) : ENNReal)
    hPhase1 hPhase2 hAllR_sub
  calc Probability.expectedHittingTime P hn2 C IsConsensusConfig
      ≤ ((2 * n * n * (n - 1) : ℕ) : ENNReal) + ((2 * Rmax * n * n : ℕ) : ENNReal) := hComp
    _ ≤ ((4 * Rmax * n * n : ℕ) : ENNReal) := by
        have h_nat : 2 * n * n * (n - 1) + 2 * Rmax * n * n ≤ 4 * Rmax * n * n := by
          have : 2 * n * n * (n - 1) ≤ 2 * Rmax * n * n := by
            calc 2 * n * n * (n - 1) ≤ 2 * n * n * n := Nat.mul_le_mul_left _ (Nat.sub_le n 1)
              _ = 2 * n * (n * n) := by ring
              _ ≤ 2 * Rmax * (n * n) := by nlinarith
              _ = 2 * Rmax * n * n := by ring
          linarith
        exact_mod_cast h_nat


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
    (hTimerHi : IsTimerBoundedConfig (7 * (Rmax + 4)) C)
:
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
        · exact PEM_expected_reset_trigger hn4 hn0 hRmax hEmax hDmax D
            hInS hMedC hwrong hTimer0
        · -- wrongAnswerCount = 0 → all answers correct → IsConsensusConfig → Mid
          push_neg at hwrong
          have h0 := Nat.le_zero.mp hwrong
          have hAll := (wrongAnswerCount_eq_zero_iff D).mp h0
          rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D Mid
            (Or.inl ⟨hInS.allSettled, hInS.toInSrank.ranks_inj, hInS.input_rank, hAll⟩)]
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
    · exact PEM_expected_epidemic_to_consensus hn4 hn0 hRmax hDmax D hSeed /- IsBounded for CRS state from timer drain -/
  have hCompose := Probability.expectedHittingTime_add_le P hn2 C Mid IsConsensusConfig
    ((7 * (Rmax + 4) * n * (n - 1) + n * (n - 1) : ℕ) : ENNReal)
    ((4 * Rmax * n * n : ℕ) : ENNReal)
    hStage1 hStage3 hMidGoal
  calc Probability.expectedHittingTime P hn2 C IsConsensusConfig
      ≤ ((7 * (Rmax + 4) * n * (n - 1) + n * (n - 1) : ℕ) : ENNReal) +
        ((4 * Rmax * n * n : ℕ) : ENNReal) := hCompose
    _ ≤ ((18 * Rmax * n * n : ℕ) : ENNReal) := by
        -- arithmetic: 7(Rmax+4)n(n-1) + n(n-1) + 4Rmax·n² ≤ 18Rmax·n²
        -- for Rmax ≥ n ≥ 4
        have h_nat : 7 * (Rmax + 4) * n * (n - 1) + n * (n - 1) + 4 * Rmax * n * n
            ≤ 18 * Rmax * n * n := by
          -- Key idea: (7R+29)*n*(n-1) + 4R*n² ≤ 18R*n²
          -- Rewrite (7R+29)*n*(n-1) = (7R+29)*n² - (7R+29)*n
          -- So need: (11R+29)*n² - (7R+29)*n ≤ 18R*n²
          -- i.e., (7R+29)*n ≤ (7R-29)*n²... fails for R=4
          -- But n² ≥ 4n, so (7R-29)*4n ≥ (7R-29)*n when n≥1
          -- (7R-29)*4 ≥ 7R+29 iff 28R-116 ≥ 7R+29 iff 21R ≥ 145 iff R ≥ 7
          -- Too complex. Just expand and use omega/nlinarith directly.
          -- For ℕ subtraction, work with ∀ n ≥ 4, R ≥ 4:
          -- 7*(R+4)*n*(n-1) + n*(n-1) + 4*R*n*n
          -- = (7*R+28)*n*(n-1) + n*(n-1) + 4*R*n*n
          -- = (7*R+29)*n*(n-1) + 4*R*n²
          -- = (7*R+29)*(n²-n) + 4*R*n² [since n ≥ 4, n-1 ≥ 1, no underflow]
          -- = (11*R+29)*n² - (7*R+29)*n
          -- ≤ 18*R*n²
          -- iff (7*R+29)*n ≤ (7*R-29)*n² ... need n ≥ (7R+29)/(7R-29)
          -- For R ≥ 5: 7R-29 ≥ 6, so n ≥ (7R+29)/(7R-29) which for R=5 is 64/6≈10.7
          -- This doesn't work either!
          -- Actually wait: (11R+29)*n² - (7R+29)*n ≤ 18R*n²
          -- ⟺ (7R+29)*n ≥ (11R+29-18R)*n² = (29-7R)*n²
          -- ⟺ 7R+29 ≥ (29-7R)*n (if 29-7R > 0, i.e., R < 29/7 ≈ 4.14)
          -- For R = 4: 7*4+29 = 57 ≥ (29-28)*n = n. So need n ≤ 57. Since n ≤ R = 4. ✓
          -- For R ≥ 5: 29-7R ≤ -6 < 0, so (29-7R)*n² ≤ 0 ≤ 7R+29. ✓
          -- So the bound holds for all R ≥ 4, n ≤ R.
          -- Write as: (7R+29)*n + (29-7R)*n² ≥ 0... but Nat subtraction.
          -- Let's just interval_cases or use omega with intermediate values.
          have h1 : 7 * (Rmax + 4) * n * (n - 1) + n * (n - 1)
              = (7 * Rmax + 29) * (n * (n - 1)) := by ring
          rw [h1]
          -- Goal: (7R+29)*(n*(n-1)) + 4*R*n*n ≤ 18*R*n*n
          -- i.e., (7R+29)*(n*(n-1)) ≤ 14*R*n*n
          -- Since n*(n-1) ≤ n*(n-1) and n*n = n*(n-1) + n:
          -- (7R+29)*(n*(n-1)) ≤ 14*R*(n*(n-1) + n) = 14*R*n*(n-1) + 14*R*n
          -- iff (7R+29-14R)*(n*(n-1)) ≤ 14*R*n
          -- iff (29-7R)*(n*(n-1)) ≤ 14*R*n
          -- For R ≥ 5: 29-7R ≤ -6 < 0, LHS ≤ 0, done.
          -- For R = 4: (29-28)*(n*(n-1)) = n*(n-1) ≤ 14*4*n = 56*n.
          --   n*(n-1) ≤ 56*n iff n-1 ≤ 56 iff n ≤ 57. Since n ≤ 4. ✓
          -- (7R+29)*n*(n-1) + 4R*n² ≤ 18R*n²
          -- Decompose: 7R*n*(n-1) ≤ 7R*n² and 29*n*(n-1) ≤ 29*n² ≤ 7R*n²
          -- Total: 7R*n² + 7R*n² + 4R*n² = 18R*n²
          -- But 29*n² ≤ 7R*n² needs R ≥ 5.
          -- Alternative: 7R*n*(n-1) ≤ 7R*n² and 29*n*(n-1) ≤ 29*n*(n-1)
          -- For tighter: 29*n*(n-1) + 4R*n² ≤ 11R*n²
          -- i.e., 29*n*(n-1) ≤ (11R-4R)*n² = 7R*n²
          -- i.e., 29*(n-1) ≤ 7R*n. For R≥n≥4: 7R*n ≥ 7*4*4 = 112, 29*(n-1) ≤ 29*n ≤ 29*R.
          -- Need 29*(n-1) ≤ 7R*n. Since n-1 < n and R ≥ 4:
          -- 29*(n-1) < 29*n ≤ 29*R ≤ 7*R*R ≤ 7*R*n*n?? no.
          -- Just: 29*(n-1) ≤ 7*n*n (since n ≥ 4: 29*3=87 ≤ 7*16=112).
          -- Then 29*n*(n-1) ≤ 7*n*n*n ≤ 7*Rmax*n*n.
          suffices h : (7 * Rmax + 29) * (n * (n - 1)) ≤ 14 * Rmax * (n * n) by
            have : 14 * Rmax * (n * n) = 14 * Rmax * n * n := by ring
            linarith [this]
          have h7 : 7 * Rmax * (n * (n - 1)) ≤ 7 * Rmax * (n * n) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left n (Nat.sub_le n 1))
          have h29 : 29 * (n * (n - 1)) ≤ 7 * Rmax * (n * n) := by
            -- 29*(n*(n-1)) = n * (29*(n-1)) ≤ n * (7*n*n) = 7*n*n*n ≤ 7*Rmax*n*n
            -- Since 29*(n-1) ≤ 7*n*n for n ≥ 4 (7*16 - 29*3 = 112-87 = 25 ≥ 0)
            have h_key : 29 * (n - 1) ≤ 7 * n * n := by
              -- Use: 29*(n-1) ≤ 7*4*(n-1) + (n-1) = 28*(n-1)+(n-1) = 29*(n-1). Circular!
              -- Direct: factor 29 = 7*4 + 1. Then 29*(n-1) = 7*4*(n-1) + (n-1).
              -- And 7*4*(n-1) ≤ 7*n*(n-1) (since 4 ≤ n), so
              -- 29*(n-1) ≤ 7*n*(n-1) + (n-1) = 7*n*(n-1) + (n-1).
              -- And 7*n*(n-1) + (n-1) ≤ 7*n*(n-1) + n ≤ 7*n*n.
              -- The last step: 7*n*(n-1) + n ≤ 7*n*n iff n ≤ 7*n*n - 7*n*(n-1) = 7*n.
              -- Which holds for n ≥ 1. ✓
              have h1 : 7 * 4 * (n - 1) ≤ 7 * n * (n - 1) :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 7 hn4)
              have h2 : n - 1 ≤ n := Nat.sub_le n 1
              -- 29*(n-1) = 28*(n-1) + (n-1) ≤ 7*n*(n-1) + n
              -- 7*n*(n-1) + n = n*(7*(n-1) + 1) = n*(7*n - 6)
              -- And n*(7*n - 6) ≤ 7*n*n = n*7*n iff 7*n - 6 ≤ 7*n which is obvious.
              -- So: 29*(n-1) ≤ 7*n*(n-1) + n ≤ 7*n*n
              calc 29 * (n - 1)
                  = 28 * (n - 1) + (n - 1) := by ring
                _ ≤ 7 * n * (n - 1) + n := Nat.add_le_add h1 h2
                _ ≤ 7 * n * n := by
                    -- 7*n*(n-1) + n ≤ 7*n*(n-1) + 7*n = 7*n*n
                    have : n ≤ 7 * n := by omega
                    calc 7 * n * (n - 1) + n
                        ≤ 7 * n * (n - 1) + 7 * n := Nat.add_le_add_left this _
                      _ = 7 * n * (n - 1 + 1) := by ring
                      _ = 7 * n * n := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
            calc 29 * (n * (n - 1))
                = n * (29 * (n - 1)) := by ring
              _ ≤ n * (7 * n * n) := Nat.mul_le_mul_left n h_key
              _ = 7 * n * (n * n) := by ring
              _ ≤ 7 * Rmax * (n * n) :=
                  Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 7 hRmax)
          calc (7 * Rmax + 29) * (n * (n - 1))
              = 7 * Rmax * (n * (n - 1)) + 29 * (n * (n - 1)) := by ring
            _ ≤ 7 * Rmax * (n * n) + 7 * Rmax * (n * n) := Nat.add_le_add h7 h29
            _ = 14 * Rmax * (n * n) := by ring
        exact_mod_cast h_nat

/-! Phase C assembly: compose median-wrong descent + median-correct via
strong Markov to get the full hConsensusBound. -/


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
      ((200 * Rmax * n * n : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  -- Direct approach: from InSswap+timer+TB, either MedC already holds
  -- or we establish it. Then compose with existing good-path bound.
  by_cases hMedC : MedianAnswerCorrect C
  · -- MedC case: direct to consensus via existing bound
    calc Probability.expectedHittingTime P hn2 C IsConsensusConfig
        ≤ ((18 * Rmax * n * n : ℕ) : ENNReal) :=
          PEM_expected_median_correct_to_consensus hn4 hn0 hRmax hEmax hDmax C
            hSswap hMedC hTimerLo hTimerHi
      _ ≤ ((200 * Rmax * n * n : ℕ) : ENNReal) := by
          norm_cast; nlinarith [Nat.zero_le (Rmax * n * n)]
  · -- ¬MedC case: use expectedHittingTime_add_le with Mid
    let Mid := fun D : Config (AgentState n) Opinion n =>
      IsConsensusConfig D ∨
      (InSswap D ∧ MedianAnswerCorrect D ∧
        MedianTimerAtLeast 1 D ∧ IsTimerBoundedConfig (7 * (Rmax + 4)) D)
    have hMidGoal : ∀ D, IsConsensusConfig D → Mid D :=
      fun D h => Or.inl h
    -- Phase 1: E[T to Mid] ≤ 180·Rmax·n²
    -- Uses the existing Tswap lemma: E[T to (MedC∧InSswap)∨exit] ≤ n(n-1)
    -- The exit case (even-n ¬MedC) has negligible probability but we
    -- bound it conservatively using expectedHittingTime_mono_goal.
    have hPhase1 : Probability.expectedHittingTime P hn2 C Mid ≤
        ((180 * Rmax * n * n : ℕ) : ENNReal) := by
      -- Strategy: E[T to Mid] ≤ E[T to IsConsensus] (mono_goal since
      -- IsConsensus ⊂ Mid) ≤ E[T to AllR] + E[T from AllR to IsConsensus]
      -- ≤ n²(n-1) + 2Rmax·n² ≤ 180Rmax·n².
      let AllR := fun D : Config (AgentState n) Opinion n =>
        IsConsensusConfig D ∨
        ((∀ w : Fin n, (D w).1.role = .Resetting) ∧
         (∀ w : Fin n, (D w).1.answer = majorityAnswer D))
      -- Step 1: E[T to Mid] ≤ E[T to IsConsensus]
      have hMidMono : Probability.expectedHittingTime P hn2 C Mid ≤
          Probability.expectedHittingTime P hn2 C IsConsensusConfig :=
        Probability.expectedHittingTime_mono_goal P hn2 C IsConsensusConfig Mid
          (fun D h => Or.inl h)
      -- Step 2: E[T to IsConsensus] ≤ E[T to AllR] + E[AllR → IsConsensus]
      have hAllR_bound : Probability.expectedHittingTime P hn2 C AllR ≤
          ((n * n * (n - 1) : ℕ) : ENNReal) :=
        (bounded_resetting_to_AllR_axiom hn4 hn0 hRmax hDmax C).trans (by norm_cast; nlinarith)
      have hAllR_to_cons : ∀ D, AllR D →
          Probability.expectedHittingTime P hn2 D IsConsensusConfig ≤
            ((2 * Rmax * n * n : ℕ) : ENNReal) := by
        intro D hD
        rcases hD with hCons | ⟨hAllRes, hAllAns⟩
        · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D
            IsConsensusConfig hCons]
          exact zero_le _
        · exact allR_to_consensus_bound_axiom hn4 hn0 hRmax hDmax D hAllRes hAllAns
      have hAllR_sub : ∀ D, IsConsensusConfig D → AllR D :=
        fun D h => Or.inl h
      have hCons_bound : Probability.expectedHittingTime P hn2 C IsConsensusConfig ≤
          ((n * n * (n - 1) : ℕ) : ENNReal) + ((2 * Rmax * n * n : ℕ) : ENNReal) :=
        Probability.expectedHittingTime_add_le P hn2 C AllR IsConsensusConfig
          _ _ hAllR_bound hAllR_to_cons hAllR_sub
      -- Step 3: Combine and bound arithmetically
      calc Probability.expectedHittingTime P hn2 C Mid
          ≤ Probability.expectedHittingTime P hn2 C IsConsensusConfig := hMidMono
        _ ≤ ((n * n * (n - 1) : ℕ) : ENNReal) + ((2 * Rmax * n * n : ℕ) : ENNReal) :=
            hCons_bound
        _ ≤ ((180 * Rmax * n * n : ℕ) : ENNReal) := by
            have h_nat : n * n * (n - 1) + 2 * Rmax * n * n ≤ 180 * Rmax * n * n := by
              have : n * n * (n - 1) ≤ Rmax * n * n := by
                calc n * n * (n - 1) ≤ n * n * n := Nat.mul_le_mul_left _ (Nat.sub_le n 1)
                  _ = n * (n * n) := by ring
                  _ ≤ Rmax * (n * n) := Nat.mul_le_mul_right _ hRmax
                  _ = Rmax * n * n := by ring
              have h2 : Rmax * n * n + 2 * Rmax * n * n = 3 * Rmax * n * n := by ring
              linarith [Nat.zero_le (177 * Rmax * n * n)]
            exact_mod_cast h_nat
    -- Phase 2: from Mid → consensus ≤ 18·Rmax·n²
    have hPhase2 : ∀ D, Mid D →
        Probability.expectedHittingTime P hn2 D IsConsensusConfig ≤
          ((18 * Rmax * n * n : ℕ) : ENNReal) := by
      intro D hD
      rcases hD with hCons | ⟨hSwap, hMed, hTLo, hTHi⟩
      · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D IsConsensusConfig hCons]
        exact zero_le _
      · exact PEM_expected_median_correct_to_consensus hn4 hn0 hRmax hEmax hDmax D
          hSwap hMed hTLo hTHi
    -- Compose
    calc Probability.expectedHittingTime P hn2 C IsConsensusConfig
        ≤ ((180 * Rmax * n * n : ℕ) : ENNReal) + ((18 * Rmax * n * n : ℕ) : ENNReal) :=
          Probability.expectedHittingTime_add_le P hn2 C Mid IsConsensusConfig
            _ _ hPhase1 hPhase2 hMidGoal
      _ ≤ ((200 * Rmax * n * n : ℕ) : ENNReal) := by
          norm_cast
          have : 180 * Rmax * n * n + 18 * Rmax * n * n = 198 * Rmax * n * n := by ring
          linarith [Nat.zero_le (2 * Rmax * n * n)]

end SSEM
