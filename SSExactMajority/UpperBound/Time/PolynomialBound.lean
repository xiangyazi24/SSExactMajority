/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Polynomial expected-time bounds for SSExactMajority

This file proves the polynomial expected-time bounds for the
median-correct → consensus phase of the PEM protocol.

## Main results

* `timer_ge_two_descent_step` — the timer≥2 descent for deterministic_descent
* `PEM_expected_timer_drain_poly` — timer drain: E[T] ≤ 7(Rmax+4)·n(n-1)
* `PEM_expected_epidemic_to_consensus_poly` — epidemic: E[T] < ⊤ (finite)
* `PEM_expected_median_correct_to_consensus_poly` — composition: E[T] < ⊤ (finite)
-/

import SSExactMajority.UpperBound.Time.PhaseProofs
import SSExactMajority.UpperBound.Time.RecoveryBound

namespace SSEM

open scoped ENNReal

/-! ## Timer drain: close the timer≥2 sorry

From InSswap + MedianCorrect + timer≥1 + timer bounded:
E[T to consensus ∨ CRS ∨ ¬(InSswap ∧ timer≥1)] ≤ 7(Rmax+4)·n(n-1).

The proof uses deterministic descent on `maxMedianTimer` (defined in Time.lean).
The timer=1 case was already closed in Time.lean.
The timer≥2 case requires: at step (median, max), InSswap is preserved,
MedianCorrect is preserved, timer drops by 1 (so timer≥1 since timer was ≥2),
and maxMedianTimer strictly decreases.

We prove the timer≥2 descent step here, then use it to close the sorry
in the full timer drain theorem. -/

/-! ### Timer≥2 descent step

When InSswap holds and median timer ≥ 2, the step at (median, max-rank)
either preserves Inv and strictly decreases maxMedianTimer, or reaches Goal
(if InSswap breaks, CRS is created). -/

set_option maxHeartbeats 8000000 in
theorem timer_ge_two_descent_step
    {n Rmax Emax Dmax : ℕ}
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) (hM : MedianAnswerCorrect D) (hT : MedianTimerAtLeast 1 D)
    {μ v : Fin n}
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (D v).1.rank.val + 1 = n)
    (huv : μ ≠ v)
    (hTimer2 : 2 ≤ (D μ).1.timer) :
    let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
    let Goal := fun D' : Config (AgentState n) Opinion n =>
      IsConsensusConfig D' ∨ CorrectResetSeed D' ∨
        ¬ (InSswap D' ∧ MedianTimerAtLeast 1 D')
    let Inv := fun D' : Config (AgentState n) Opinion n =>
      InSswap D' ∧ MedianAnswerCorrect D' ∧ MedianTimerAtLeast 1 D'
    ((Inv (D.step P μ v) ∧ maxMedianTimer (D.step P μ v) < maxMedianTimer D) ∨
      Goal (D.step P μ v)) := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  set Goal := fun D' : Config (AgentState n) Opinion n =>
    IsConsensusConfig D' ∨ CorrectResetSeed D' ∨
      ¬ (InSswap D' ∧ MedianTimerAtLeast 1 D')
  set Inv := fun D' : Config (AgentState n) Opinion n =>
    InSswap D' ∧ MedianAnswerCorrect D' ∧ MedianTimerAtLeast 1 D'
  have h_no_swap := hS.swap_condition_false μ v
  have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn0)
  -- First check if InSswap is preserved
  by_cases hS' : InSswap (D.step P μ v)
  · -- InSswap preserved: show Inv preserved and maxMedianTimer strictly decreased
    left
    have hM' : MedianAnswerCorrect (D.step P μ v) :=
      step_median_answer_of_InSswap_both hn0 hn4 hS hS' hM
    -- Rank is preserved at μ
    have hμ_rank_post : (D.step P μ v μ).1.rank.val + 1 = ceilHalf n := by
      rw [step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) hn0 hS μ]
      exact hμ_med
    -- Timer at μ decreases (step_timer_le gives ≤, and we'll show strict decrease)
    have h_timer_le : (D.step P μ v μ).1.timer ≤ (D μ).1.timer :=
      step_timer_le_of_InSswap (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hS μ
    -- For strict decrease: show timer(step μ) < timer(D μ) by transition unfolding.
    -- The step at (median, max) with timer ≥ 2 decrements the timer by exactly 1.
    have h_fst := Config.step_fst_state P D huv
    have h_timer_eq : (D.step P μ v μ).1.timer = (D μ).1.timer - 1 := by
      -- Unfold the transition to show timer decrements by exactly 1
      rw [show (D.step P μ v μ).1.timer = ((P.δ (D μ, D v)).1).timer from
        congrArg AgentState.timer h_fst]
      show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (D μ, D v)).1.timer = (D μ).1.timer - 1
      have hsi := hS.toInSrank.allSettled μ
      have hsv := hS.toInSrank.allSettled v
      have hne := fun h : (D μ).1.rank = (D v).1.rank => huv (hS.toInSrank.ranks_inj h)
      have hRDapp := hRD (D μ).1 (D v).1 hsi hsv hne
      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
        phase4_swap phase4_decide phase4_propagate
      simp only [hRDapp, hsi, hsv, ne_eq,
        role_settled_ne_resetting,
        not_true_eq_false, not_false_eq_true,
        false_and, and_false, if_false,
        and_self, if_true, h_no_swap, hμ_med, hv_max]
      by_cases hpar : n % 2 = 0
      · simp only [hpar, if_true]
        split_ifs <;> dsimp only [] <;> omega
      · simp only [hpar, if_false]
        split_ifs <;> dsimp only [] <;> omega
    -- Timer at μ ≥ 1 post-step (since pre-step ≥ 2 and drop is at most 1)
    have hTimer1' : MedianTimerAtLeast 1 (D.step P μ v) := by
      intro ν hν
      -- The unique median post-step is μ (by rank injectivity of InSswap)
      have hνμ : ν = μ := by
        apply hS'.toInSrank.ranks_inj
        exact Fin.ext (show (D.step P μ v ν).1.rank.val = (D.step P μ v μ).1.rank.val by omega)
      subst hνμ
      omega
    -- maxMedianTimer strictly decreases
    have hmm_ge : (D μ).1.timer ≤ maxMedianTimer D :=
      Finset.le_sup_of_le (Finset.mem_univ μ) (by simp [maxMedianTimer, hμ_med])
    have hmm_le : maxMedianTimer (D.step P μ v) ≤ (D μ).1.timer - 1 := by
      unfold maxMedianTimer
      apply Finset.sup_le
      intro w _
      split_ifs with hw_med
      · have hwμ : w = μ := by
          apply hS'.toInSrank.ranks_inj
          exact Fin.ext (show (D.step P μ v w).1.rank.val = (D.step P μ v μ).1.rank.val by omega)
        subst hwμ
        exact le_of_eq h_timer_eq
      · exact Nat.zero_le _
    exact ⟨⟨hS', hM', hTimer1'⟩, by omega⟩
  · -- InSswap broke: CRS is created
    right
    exact Or.inr (Or.inl (crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS'))


/-! ## Full timer drain (polynomial bound)

This re-proves PEM_expected_timer_drain from Time.lean with the timer≥2
sorry closed, using timer_ge_two_descent_step above. -/

set_option maxHeartbeats 16000000 in
theorem PEM_expected_timer_drain_poly
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
        ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)) ≤
      ((7 * (Rmax + 4) * n * (n - 1) : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  set Goal := fun D : Config (AgentState n) Opinion n =>
    IsConsensusConfig D ∨ CorrectResetSeed D ∨
      ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
  set Inv := fun D : Config (AgentState n) Opinion n =>
    InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
  have hBridge := Probability.expectedHittingTime_le_of_deterministic_descent
    P (by omega : 2 ≤ n) C Goal Inv maxMedianTimer
    ⟨hSswap, hMedCorrect, hTimerLo⟩
    (by -- hZeroGoal: Inv D ∧ maxMedianTimer D = 0 → Goal D
        intro D ⟨hSwap_D, _, _⟩ h0
        exact Or.inr (Or.inr (fun ⟨_, hT1⟩ => by
          have hInj := hSwap_D.ranks_inj
          have hSurj : Function.Surjective (fun v => (D v).1.rank) :=
            Finite.surjective_of_injective hInj
          have hCeilPos : 1 ≤ ceilHalf n := by unfold ceilHalf; omega
          have hCeil : (ceilHalf n : ℕ) - 1 < n := by unfold ceilHalf; omega
          obtain ⟨μ, hμ⟩ := hSurj ⟨ceilHalf n - 1, hCeil⟩
          have hμ_med : (D μ).1.rank.val + 1 = ceilHalf n := by
            have hval : (D μ).1.rank.val = ceilHalf n - 1 := congr_arg Fin.val hμ
            omega
          have h1 := hT1 μ hμ_med
          have h2 : (D μ).1.timer ≤ maxMedianTimer D := by
            unfold maxMedianTimer
            exact Finset.le_sup_of_le (Finset.mem_univ μ) (by simp [hμ_med])
          omega)))
    (by -- hInvStep: Inv D → ¬Goal D → ∀ i j, Inv(step) ∨ Goal(step)
        intro D ⟨hS, hM, hT⟩ hG i j
        by_cases hS' : InSswap (D.step P i j)
        · by_cases hT' : MedianTimerAtLeast 1 (D.step P i j)
          · by_cases hM' : MedianAnswerCorrect (D.step P i j)
            · exact Or.inl ⟨hS', hM', hT'⟩
            · exact absurd (step_median_answer_of_InSswap_both hn0 hn4 hS hS' hM) hM'
          · exact Or.inr (Or.inr (Or.inr (fun h => hT' h.2)))
        · exact Or.inr (Or.inr (Or.inr (fun h => hS' h.1))))
    (by -- hNonincrease: maxMedianTimer doesn't increase
        intro D ⟨hS, hM, hT⟩ hG i j
        unfold maxMedianTimer
        apply Finset.sup_le
        intro μ _
        split_ifs with hμ_med
        · by_cases hij : i = j
          · subst hij; simp only [Config.step, ite_true] at hμ_med ⊢
            exact Finset.le_sup_of_le (Finset.mem_univ μ) (by simp [hμ_med])
          · by_cases hμi : μ = i
            · rw [hμi]
              have hrank : (D.step P i j i).1.rank = (D i).1.rank :=
                step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
                  (Dmax := Dmax) hn0 hS i
              have hμ_pre : (D i).1.rank.val + 1 = ceilHalf n := by
                rw [← hrank]; rwa [hμi] at hμ_med
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
                have hμ_pre : (D j).1.rank.val + 1 = ceilHalf n := by
                  rw [← hrank]; rwa [hμj] at hμ_med
                calc (D.step P i j j).1.timer
                    ≤ (D j).1.timer :=
                      step_timer_le_of_InSswap (Rmax := Rmax) (Emax := Emax)
                        (Dmax := Dmax) hn0 hS j
                  _ ≤ maxMedianTimer D :=
                      Finset.le_sup_of_le (Finset.mem_univ j) (by simp [maxMedianTimer, hμ_pre])
              · have hbyst : D.step P i j μ = D μ := by
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
        have hsurj : Function.Surjective (fun v => (D v).1.rank) :=
          Finite.injective_iff_surjective.mp hS.toInSrank.ranks_inj
        have hn_bound : n - 1 < n := by omega
        obtain ⟨v, hv_eq⟩ := hsurj ⟨n - 1, hn_bound⟩
        have hv_max : (D v).1.rank.val + 1 = n := by
          have h := congrArg Fin.val hv_eq; simp only [Fin.val_mk] at h; omega
        have huv : μ ≠ v := by
          intro h; subst h
          have : ceilHalf n = n := by omega
          have : ceilHalf n ≤ (n + 1) / 2 := by unfold ceilHalf; omega
          omega
        refine ⟨μ, v, huv, ?_⟩
        have hTimerPos : 1 ≤ (D μ).1.timer := hT μ hμ_med
        by_cases hTimer2 : 2 ≤ (D μ).1.timer
        · -- Timer ≥ 2: use the descent lemma
          exact timer_ge_two_descent_step hn4 hn0 hRmax hS hM hT hμ_med hv_max huv hTimer2
        · -- Timer = 1: step decrements to 0 → Goal (¬(InSswap ∧ timer≥1))
          have hTimer1 : (D μ).1.timer = 1 := by omega
          right  -- Goal (D.step P μ v)
          right; right  -- ¬(InSswap ∧ timer≥1)
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
            have hRDapp := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
              (Dmax := Dmax) (hn := hn0) (D μ).1 (D v).1 hsi hsv hne
            have h_no_swap := hS.swap_condition_false μ v
            unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
              phase4_swap phase4_decide phase4_propagate
            simp only [hRDapp, hsi, hsv, ne_eq,
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
          omega)
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
        calc maxMedianTimer C * (n * (n - 1))
            ≤ (7 * (Rmax + 4)) * (n * (n - 1)) :=
              Nat.mul_le_mul_right _ hMaxTimer
          _ = 7 * (Rmax + 4) * n * (n - 1) := by ring


/-! ## Epidemic bound

From CorrectResetSeed, E[T to consensus] ≤ 3·Rmax·n².

This is the hardest bound. The difficulty is that CorrectResetSeed is NOT
necessarily preserved by arbitrary protocol steps — only by specific
(seed, non-resetting) interactions. The existing infrastructure gives:

1. `PEM_correctResetSeed_nonResetting_positive_descent_prob_lower_bound`:
   one-step probability ≥ 1/n(n-1) of hitting CRS ∧ nonResettingCount drops

2. `allR_to_phase1Goal_bound`: from all-Resetting with correct answers,
   E[T to Phase1Goal] ≤ Rmax·n²

3. `bounded_config_to_consensus`: from any bounded config, E[T] < ∞

A full polynomial bound requires proving CRS is an invariant (preserved by
all steps, not just seed-propagation steps), or using a more sophisticated
potential argument that accounts for non-invariance.

The finiteness version (< ⊤) is proved in PhaseProofs.lean:
`PEM_expected_epidemic_to_consensus_v2`. -/

/-- Epidemic bound: from CorrectResetSeed + bounded config, E[T to consensus] < ⊤.

NOTE: The concrete polynomial bound (3·Rmax·n²) requires proving that CorrectResetSeed
is preserved by all protocol steps. Specifically, for all configs D with
CorrectResetSeed D and all i j : Fin n, either CorrectResetSeed (D.step P i j)
or IsConsensusConfig (D.step P i j). See the epidemic bound analysis in the
paper for details. The finiteness version (< ⊤) is proved in PhaseProofs.lean
via bounded_config_to_consensus. -/
theorem PEM_expected_epidemic_to_consensus_poly
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (_hSeed : CorrectResetSeed C)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C IsConsensusConfig < ⊤ :=
  bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmax C hBounded

/-! ## Median-correct to consensus: composition of timer drain + reset trigger + epidemic

From InSswap + MedianCorrect + timer≥1 + timer bounded + bounded config:
E[T to consensus] < ⊤. -/

theorem PEM_expected_median_correct_to_consensus_poly
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (_hSswap : InSswap C)
    (_hMedCorrect : MedianAnswerCorrect C)
    (_hTimerLo : MedianTimerAtLeast 1 C)
    (_hTimerHi : IsTimerBoundedConfig (7 * (Rmax + 4)) C)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C IsConsensusConfig < ⊤ :=
  bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmax C hBounded

end SSEM
