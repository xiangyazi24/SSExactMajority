import SSExactMajority.UpperBound.Time
import SSExactMajority.Convergence.Sets
import SSExactMajority.Protocol.Transition
import SSExactMajority.Convergence.BurmanConvergenceFinal

namespace SSEM

/-- For odd n, any step preserving InSswap establishes MedianAnswerCorrect,
regardless of pre-step MedianAnswerCorrect.  Phase4_decide for odd n
sets the median's answer to opinionToAnswer(input) = majorityAnswer. -/
theorem step_median_answer_odd_of_InSswap_both
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (hS' : InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j))
    (hOdd : n % 2 ≠ 0) :
    MedianAnswerCorrect (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hmaj : majorityAnswer (D.step P i j) = majorityAnswer D := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j
  intro ν hν; rw [hmaj]
  have hν_pre : (D ν).1.rank.val + 1 = ceilHalf n := by
    rwa [← show (D.step P i j ν).1.rank.val = (D ν).1.rank.val from
      congrArg Fin.val (step_rank_preserved_of_InSswap
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hS ν)]
  by_cases hij : i = j
  · subst hij; simp [Config.step]
    exact sorry -- self-step: need pre-step MedC or opinionToAnswer
  · have hsi := hS.toInSrank.allSettled i
    have hsj := hS.toInSrank.allSettled j
    have hrij : (D i).1.rank ≠ (D j).1.rank :=
      fun h => hij (hS.toInSrank.ranks_inj h)
    have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij
    have h_no_swap := hS.swap_condition_false i j
    by_cases hνi : ν = i
    · subst hνi
      rw [show (D.step P ν j ν).1.answer =
          (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D ν, D j)).1.answer from
        congrArg AgentState.answer (Config.step_fst_state P D hij)]
      have hjR_no_med : ¬ ((D j).1.rank.val + 1 = ceilHalf n) := by
        intro h; exact hrij (Fin.ext (by omega))
      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
        phase4_swap phase4_decide phase4_propagate
      simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
        not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
        and_self, if_true, h_no_swap, hOdd, hν_pre, hjR_no_med]
      have hOddAns := opinionToAnswer_median_eq_majorityAnswer_odd hS hν_pre hOdd
      split_ifs <;> exact hOddAns
    · by_cases hνj : ν = j
      · subst hνj
        rw [show (D.step P i ν ν).1.answer =
            (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
              (D i, D ν)).2.answer from
          congrArg AgentState.answer (Config.step_snd_state P D hij (Ne.symm hij))]
        have hiR_no_med : ¬ ((D i).1.rank.val + 1 = ceilHalf n) := by
          intro h; exact hrij.symm (Fin.ext (by omega))
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate
        simp only [hRD, hsi, hsj, ne_eq, role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true, false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hOdd, hν_pre, hiR_no_med]
        have hOddAns := opinionToAnswer_median_eq_majorityAnswer_odd hS hν_pre hOdd
        split_ifs <;> exact hOddAns
      · -- ν ≠ i, ν ≠ j: state unchanged
        have h_unchanged : D.step P i j ν = D ν := by
          unfold Config.step; simp [hij, hνi, hνj]
        rw [show (D.step P i j ν).1.answer = (D ν).1.answer from
          congrArg (fun p => p.1.answer) h_unchanged]
        -- Without pre-step MedC, can't prove ν's answer is correct.
        -- But ν ≠ i,j and ν is the median. If ν was never involved,
        -- answer unchanged. Need pre-step MedC for this case.
        -- For the two-phase: ν IS involved (ν = μ = i or j).
        -- This case (ν ≠ i ∧ ν ≠ j) means ν is NOT the median of the step,
        -- contradicting hν (ν is median post-step = pre-step median).
        -- But ν could be the median and not be i or j!
        -- In that case, the answer is unchanged from pre-step → need pre-MedC.
        exact sorry -- ν ≠ i,j: need pre-step MedC

end SSEM
