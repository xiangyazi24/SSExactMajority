import SSExactMajority.UpperBound.Time
import SSExactMajority.Convergence.BurmanProof

namespace SSEM
open Probability

/- Quantitative bridges missing from the imported time-bound layer.

`Time.lean` exposes the structural ranking/swap facts and the Phase-C
expected-time bound, but not the deterministic-prefix expected-time estimate
or the timer upper bound for the all-resetting swap endpoint.  Keeping these
two assumptions here lets `allR_to_consensus_bound` do the requested
composition without modifying `Time.lean`. -/
axiom expectedHittingTime_le_of_det_trace
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (D : Config (AgentState n) Opinion n)
    (hAllR : ∀ w : Fin n, (D w).1.role = .Resetting)
    (hAllCorrect : ∀ w : Fin n, (D w).1.answer = majorityAnswer D)
    (Target : Config (AgentState n) Opinion n → Prop)
    [DecidablePred Target]
    (hReach : ∃ γ t,
      Target
        (execution (PEMProtocolCoupled n Rmax Emax Dmax hn0) D γ t)) :
    expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) D Target ≤
      ((2 * Rmax * n * n : ℕ) : ENNReal)

axiom all_resetting_swap_endpoint_timer_bounded
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (D : Config (AgentState n) Opinion n)
    (hAllR : ∀ w : Fin n, (D w).1.role = .Resetting)
    (hAllCorrect : ∀ w : Fin n, (D w).1.answer = majorityAnswer D)
    (γ₁ : DetScheduler n) (t₁ : ℕ)
    (hRank :
      InSrank
        (execution (PEMProtocolCoupled n Rmax Emax Dmax hn0) D γ₁ t₁))
    (hTimer :
      ∀ μ : Fin n,
        (execution (PEMProtocolCoupled n Rmax Emax Dmax hn0) D γ₁ t₁ μ).1.rank.val + 1 =
            ceilHalf n →
          2 ≤
            (execution (PEMProtocolCoupled n Rmax Emax Dmax hn0) D γ₁ t₁ μ).1.timer)
    (γ₂ : DetScheduler n) (t₂ : ℕ)
    (hSswap :
      InSswap
        (execution (PEMProtocolCoupled n Rmax Emax Dmax hn0)
          (execution (PEMProtocolCoupled n Rmax Emax Dmax hn0) D γ₁ t₁)
          γ₂ t₂)) :
    IsTimerBoundedConfig (7 * (Rmax + 4))
      (execution (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (execution (PEMProtocolCoupled n Rmax Emax Dmax hn0) D γ₁ t₁)
        γ₂ t₂)

theorem allR_to_consensus_bound
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (D : Config (AgentState n) Opinion n)
    (hAllR : ∀ w : Fin n, (D w).1.role = .Resetting)
    (hAllCorrect : ∀ w : Fin n, (D w).1.answer = majorityAnswer D) :
    expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) D IsConsensusConfig ≤
      ((22 * Rmax * n * n : ℕ) : ENNReal) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Target : Config (AgentState n) Opinion n → Prop :=
    fun C =>
      IsConsensusConfig C ∨
        (InSswap C ∧ MedianTimerAtLeast 1 C ∧
          IsTimerBoundedConfig (7 * (Rmax + 4)) C)
  obtain ⟨γ₁, t₁, hRank₁, hDisj₁⟩ :=
    ranking_from_all_resetting
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
      hn4 hEmax hDmax hRmax D hAllR
  have hReachTarget : ∃ γ t, Target (execution P D γ t) := by
    rcases hDisj₁ with hTimer₁ | hCons₁
    · let E₁ : Config (AgentState n) Opinion n := execution P D γ₁ t₁
      obtain ⟨γ₂, t₂, hSswap₂, hTimer₂⟩ :=
        swap_reaches_Sswap_from_timer_bound_with_timer
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
          rankDeltaOSSR_satisfies_fix hn4
          (C₀ := E₁)
          (by simpa [E₁, P, PEMProtocolCoupled, PEMProtocol] using hRank₁)
          (by
            intro μ hμ
            exact hTimer₁ μ (by simpa [E₁, P, PEMProtocolCoupled, PEMProtocol] using hμ))
      refine ⟨concatScheduler γ₁ t₁ γ₂, t₁ + t₂, ?_⟩
      have hsplit :
          execution P D (concatScheduler γ₁ t₁ γ₂) (t₁ + t₂) =
            execution P E₁ γ₂ t₂ := by
        rw [execution_concat]
      rw [hsplit]
      have hTimerHi :
          IsTimerBoundedConfig (7 * (Rmax + 4)) (execution P E₁ γ₂ t₂) := by
        simpa [E₁, P, PEMProtocolCoupled, PEMProtocol] using
          all_resetting_swap_endpoint_timer_bounded
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 hn0 hRmax hEmax hDmax D hAllR hAllCorrect γ₁ t₁
            (by simpa [P, PEMProtocolCoupled, PEMProtocol] using hRank₁)
            (by
              intro μ hμ
              exact hTimer₁ μ
                (by simpa [P, PEMProtocolCoupled, PEMProtocol] using hμ))
            γ₂ t₂
            (by simpa [E₁, P, PEMProtocolCoupled, PEMProtocol] using hSswap₂)
      exact Or.inr ⟨hSswap₂, hTimer₂, hTimerHi⟩
    · exact ⟨γ₁, t₁, Or.inl (by simpa [P, PEMProtocolCoupled, PEMProtocol] using hCons₁)⟩
  have hTargetBound :
      expectedHittingTime P (by omega : 2 ≤ n) D Target ≤
        ((2 * Rmax * n * n : ℕ) : ENNReal) := by
    simpa [P, Target] using
      expectedHittingTime_le_of_det_trace
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hn0 hRmax D hAllR hAllCorrect Target
        (by simpa [P, Target] using hReachTarget)
  have hFromTarget :
      ∀ C : Config (AgentState n) Opinion n, Target C →
        expectedHittingTime P (by omega : 2 ≤ n) C IsConsensusConfig ≤
          ((20 * Rmax * n * n : ℕ) : ENNReal) := by
    intro C hC
    rcases hC with hCons | ⟨hSswap, hTimerLo, hTimerHi⟩
    · rw [expectedHittingTime_eq_zero_of_goal P (by omega : 2 ≤ n) C
        IsConsensusConfig hCons]
      exact zero_le _
    · simpa [P] using
        PEM_hConsensusBound_from_bridge
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn4 hn0 hRmax hEmax hDmax C hSswap hTimerLo hTimerHi
  have hGoalTarget : ∀ C : Config (AgentState n) Opinion n,
      IsConsensusConfig C → Target C := by
    intro C hC
    exact Or.inl hC
  have hCompose :
      expectedHittingTime P (by omega : 2 ≤ n) D IsConsensusConfig ≤
        ((2 * Rmax * n * n : ℕ) : ENNReal) +
          ((20 * Rmax * n * n : ℕ) : ENNReal) :=
    expectedHittingTime_add_le P (by omega : 2 ≤ n) D Target IsConsensusConfig
      ((2 * Rmax * n * n : ℕ) : ENNReal)
      ((20 * Rmax * n * n : ℕ) : ENNReal)
      hTargetBound hFromTarget hGoalTarget
  calc
    expectedHittingTime P (by omega : 2 ≤ n) D IsConsensusConfig
        ≤ ((2 * Rmax * n * n : ℕ) : ENNReal) +
          ((20 * Rmax * n * n : ℕ) : ENNReal) := hCompose
    _ = ((22 * Rmax * n * n : ℕ) : ENNReal) := by
      norm_num
      ring

end SSEM
