import SSExactMajority.UpperBound.Time.Defs
import SSExactMajority.UpperBound.Time.SwapPhase

namespace SSEM

open scoped ENNReal

/-! ### Timer-drain one-step probability witnesses -/

/-- Odd-population median/max no-swap timer descent as a one-step scheduler
probability lower bound. -/
theorem PEM_odd_median_max_timer_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : 2 ≤ (C μ).1.timer) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ (D μ).1.timer + 1 = (C μ).1.timer) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hstep :=
    step_at_median_max_no_swap_odd_explicit
      (n := n) (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hC hn2 hμv hμ_med hv_max hpar h_no_swap h_timer
  have hSwap' : InSswap (C.step P μ v) := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      (step_at_median_max_no_swap_odd_explicit_preserves_InSswap
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (rankDeltaOSSR_satisfies_fix
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
        hC hn2 hμv hμ_med hv_max hpar h_no_swap h_timer)
  have hTimer' : (C.step P μ v μ).1.timer + 1 = (C μ).1.timer := by
    have htimer_eq : (C.step P μ v μ).1.timer = (C μ).1.timer - 1 := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hstep.1
    rw [htimer_eq]
    omega
  apply Probability.ProbHitWithin_one_lower_bound_of_step
    (P := P) hn2 C
    (fun D => InSswap D ∧ (D μ).1.timer + 1 = (C μ).1.timer)
  · intro hGoal
    omega
  · exact hμv
  · exact ⟨hSwap', hTimer'⟩

/-- Even-population lower-median/max no-reset timer descent as a one-step
scheduler probability lower bound. -/
theorem PEM_even_lower_median_max_timer_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : 2 ≤ (C μ).1.timer) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ (D μ).1.timer + 1 = (C μ).1.timer) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hstep :=
    step_at_even_lower_max_timer_ge_two
      (n := n) (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hC hn4 hμv hpar hμ_lower hv_max h_no_swap h_timer
  have hSwap' : InSswap (C.step P μ v) := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      (step_at_even_lower_max_timer_ge_two_preserves_InSswap
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (rankDeltaOSSR_satisfies_fix
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
        hC hn4 hμv hpar hμ_lower hv_max h_no_swap h_timer)
  have hTimer' : (C.step P μ v μ).1.timer + 1 = (C μ).1.timer := by
    have htimer_eq : (C.step P μ v μ).1.timer = (C μ).1.timer - 1 := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hstep.1
    rw [htimer_eq]
    omega
  apply Probability.ProbHitWithin_one_lower_bound_of_step
    (P := P) hn2 C
    (fun D => InSswap D ∧ (D μ).1.timer + 1 = (C μ).1.timer)
  · intro hGoal
    omega
  · exact hμv
  · exact ⟨hSwap', hTimer'⟩

/-- Parity-unified median/max no-swap timer descent lower bound.  This is
the one-step probability interface used by the timer-drain part of the
`Sdec -> Stim` window. -/
theorem PEM_median_max_timer_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : 2 ≤ (C μ).1.timer) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ (D μ).1.timer + 1 = (C μ).1.timer) 1 := by
  by_cases hpar : n % 2 = 0
  · have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
    exact PEM_even_lower_median_max_timer_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC hμv hpar (by simpa [hceil] using hμ_med)
      hv_max h_no_swap h_timer
  · exact PEM_odd_median_max_timer_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hC hμv hpar hμ_med hv_max h_no_swap h_timer

/-- Marginal one-step form of
`PEM_median_max_timer_descent_prob_lower_bound`. -/
theorem PEM_median_max_timer_descent_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : 2 ≤ (C μ).1.timer) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by classical exact inferInstance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ (D μ).1.timer + 1 = (C μ).1.timer)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ (D μ).1.timer + 1 = (C μ).1.timer
  have hGoal : ¬ Goal C := by
    intro h
    omega
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_median_max_timer_descent_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC hμv hμ_med hv_max h_no_swap h_timer)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-- Odd-population median/max timer-one no-reset step exits the live-timer
swap region with the mass of one ordered scheduler pair. -/
theorem PEM_odd_median_max_timer_one_no_reset_exit_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_live : MedianTimerAtLeast 1 C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : (C μ).1.timer = 1)
    (h_post_same : opinionToAnswer (C μ).2 = (C v).1.answer) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ ¬ MedianTimerAtLeast 1 D) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hstep :
      InSswap (C.step P μ v) ∧
        (C.step P μ v μ).1.timer = 0 ∧
        (C.step P μ v μ).1.answer = opinionToAnswer (C μ).2 ∧
        (C.step P μ v μ).1.rank.val + 1 = ceilHalf n ∧
        (C.step P μ v v).1.rank.val + 1 = n ∧
        (∀ w : Fin n, w ≠ μ → w ≠ v → C.step P μ v w = C w) ∧
        (∀ w : Fin n, (C.step P μ v w).2 = (C w).2) := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      (step_at_median_max_timer_one_no_reset_explicit
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (rankDeltaOSSR_satisfies_fix
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
        hC hn4 hμv hμ_med hv_max hpar h_no_swap h_timer h_post_same)
  have hGoal :
      InSswap (C.step P μ v) ∧
        ¬ MedianTimerAtLeast 1 (C.step P μ v) := by
    refine ⟨hstep.1, ?_⟩
    intro hLive'
    have htimer_ge : 1 ≤ (C.step P μ v μ).1.timer :=
      hLive' μ hstep.2.2.2.1
    omega
  apply Probability.ProbHitWithin_one_lower_bound_of_step
    (P := P) hn2 C
    (fun D => InSswap D ∧ ¬ MedianTimerAtLeast 1 D)
  · intro hTarget
    exact hTarget.2 h_live
  · exact hμv
  · exact hGoal

/-- Marginal one-step form of
`PEM_odd_median_max_timer_one_no_reset_exit_prob_lower_bound`. -/
theorem PEM_odd_median_max_timer_one_no_reset_exit_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_live : MedianTimerAtLeast 1 C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : (C μ).1.timer = 1)
    (h_post_same : opinionToAnswer (C μ).2 = (C v).1.answer) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by classical exact inferInstance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ ¬ MedianTimerAtLeast 1 D)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ ¬ MedianTimerAtLeast 1 D
  have hGoal : ¬ Goal C := by
    intro h
    exact h.2 h_live
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_odd_median_max_timer_one_no_reset_exit_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC h_live hμv hpar hμ_med hv_max h_no_swap
        h_timer h_post_same)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-- Even-population lower-median/max timer-one no-reset step exits the
live-timer swap region with the mass of one ordered scheduler pair. -/
theorem PEM_even_lower_median_max_timer_one_no_reset_exit_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_live : MedianTimerAtLeast 1 C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : (C μ).1.timer = 1)
    (h_post_same : (C μ).1.answer = (C v).1.answer) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ ¬ MedianTimerAtLeast 1 D) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hstep :
      InSswap (C.step P μ v) ∧
        (C.step P μ v μ).1.timer = 0 ∧
        (C.step P μ v μ).1.answer = (C μ).1.answer ∧
        (C.step P μ v μ).1.rank.val + 1 = n / 2 := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      (no_reset_even_lower_max_timer_one_step_InSswap
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hC hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_post_same)
  have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
  have hGoal :
      InSswap (C.step P μ v) ∧
        ¬ MedianTimerAtLeast 1 (C.step P μ v) := by
    refine ⟨hstep.1, ?_⟩
    intro hLive'
    have hμ_med' : (C.step P μ v μ).1.rank.val + 1 = ceilHalf n := by
      simpa [hceil] using hstep.2.2.2
    have htimer_ge : 1 ≤ (C.step P μ v μ).1.timer :=
      hLive' μ hμ_med'
    omega
  apply Probability.ProbHitWithin_one_lower_bound_of_step
    (P := P) hn2 C
    (fun D => InSswap D ∧ ¬ MedianTimerAtLeast 1 D)
  · intro hTarget
    exact hTarget.2 h_live
  · exact hμv
  · exact hGoal

/-- Marginal one-step form of
`PEM_even_lower_median_max_timer_one_no_reset_exit_prob_lower_bound`. -/
theorem PEM_even_lower_median_max_timer_one_no_reset_exit_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_live : MedianTimerAtLeast 1 C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : (C μ).1.timer = 1)
    (h_post_same : (C μ).1.answer = (C v).1.answer) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by classical exact inferInstance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ ¬ MedianTimerAtLeast 1 D)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ ¬ MedianTimerAtLeast 1 D
  have hGoal : ¬ Goal C := by
    intro h
    exact h.2 h_live
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_even_lower_median_max_timer_one_no_reset_exit_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC h_live hμv hpar hμ_lower hv_max h_no_swap
        h_timer h_post_same)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-- Odd-population timer-one median/max reset-firing step creates a
`CorrectResetSeed` with the mass of one ordered scheduler pair. -/
theorem PEM_odd_median_max_timer_one_reset_seed_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hμ_input_A : (C μ).2 = Opinion.A)
    (h_timer : (C μ).1.timer = 1)
    (h_max_wrong : (C v).1.answer ≠ opinionToAnswer (C μ).2) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        CorrectResetSeed 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
    rintro ⟨_, hB, _⟩
    rw [hμ_input_A] at hB
    cases hB
  have h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer := by
    intro h
    exact h_max_wrong h.symm
  have hsnap :
      (C' μ).1.role = .Resetting ∧ (C' μ).1.resetcount = Rmax ∧
        (C' μ).1.leader = .L ∧
      (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
        (C' v).1.leader = .L ∧
      ∀ y : Fin n, (C' y).1.role = .Resetting →
        (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
    simpa [C', P, PEMProtocolCoupled, PEMProtocol] using
      (trigger_reset_from_InSrank_timer_one_max_no_swap_with_snapshot
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        (C := C) hC.toInSrank hn4 hμv hμ_med hv_max h_timer
        h_no_swap hpar h_post_diff)
  have hstep :
      (C' μ).1.role = .Resetting ∧
      (C' v).1.role = .Resetting ∧
      (C' μ).1.answer = opinionToAnswer (C μ).2 ∧
      (C' v).1.answer = opinionToAnswer (C μ).2 ∧
      (C' μ).1.resetcount = Rmax ∧
      (C' v).1.resetcount = Rmax ∧
      (∀ w : Fin n, w ≠ μ → w ≠ v → C' w = C w) ∧
      (∀ w : Fin n, (C' w).2 = (C w).2) := by
    simpa [C', P, PEMProtocolCoupled, PEMProtocol] using
      (step_at_median_max_timer_one_reset_fires_odd
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (rankDeltaOSSR_satisfies_fix
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
        hC hn2 hμv hμ_med hv_max hpar hμ_input_A h_timer h_max_wrong)
  have hmaj : majorityAnswer C' = majorityAnswer C := by
    simpa [C', P, PEMProtocolCoupled, PEMProtocol] using
      (majorityAnswer_step_eq
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C μ v)
  have hμ_majority : opinionToAnswer (C μ).2 = majorityAnswer C :=
    opinionToAnswer_median_eq_majorityAnswer_odd hC hμ_med hpar
  have hN_bound : nonResettingCount C' < Rmax := by
    have hcard_le : nonResettingCount C' ≤ n - 1 := by
      set S := Finset.univ.filter
        (fun w : Fin n => (C' w).1.role ≠ .Resetting) with hS
      have hsub : S ⊆ Finset.univ.erase μ := by
        intro x hx
        have hx_ne : x ≠ μ := by
          intro hxμ
          subst x
          have hx_not : (C' μ).1.role ≠ .Resetting := by
            rw [hS] at hx
            exact (Finset.mem_filter.mp hx).2
          rw [hstep.1] at hx_not
          exact hx_not rfl
        exact Finset.mem_erase.mpr ⟨hx_ne, Finset.mem_univ x⟩
      have hle := Finset.card_le_card hsub
      have herase : (Finset.univ.erase μ).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ μ)]
        simp
      unfold nonResettingCount
      rw [← hS]
      omega
    have hn_pos : 0 < n := by omega
    have hRmax_pos : 0 < Rmax := Nat.lt_of_lt_of_le hn_pos hRmax
    omega
  have hRmax_pos : 0 < Rmax := by
    have hn_pos : 0 < n := by omega
    exact Nat.lt_of_lt_of_le hn_pos hRmax
  have hSeed : CorrectResetSeed C' := by
    refine ⟨⟨μ, hsnap.1, ?_, hsnap.2.2.1, ?_⟩, ?_⟩
    · rw [hsnap.2.1]
      exact hN_bound
    · rw [hstep.2.2.1, hmaj, hμ_majority]
    · intro w hw
      by_cases hwμ : w = μ
      · subst w
        refine ⟨?_, ?_⟩
        · rw [hsnap.2.1]
          exact hRmax_pos
        · rw [hstep.2.2.1, hmaj, hμ_majority]
      · by_cases hwv : w = v
        · subst w
          refine ⟨?_, ?_⟩
          · rw [hsnap.2.2.2.2.1]
            exact hRmax_pos
          · rw [hstep.2.2.2.1, hmaj, hμ_majority]
        · have hOldSettled : (C' w).1.role = .Settled := by
            rw [hstep.2.2.2.2.2.2.1 w hwμ hwv]
            exact hC.allSettled w
          rw [hOldSettled] at hw
          cases hw
  apply Probability.ProbHitWithin_one_lower_bound_of_step
    (P := P) hn2 C CorrectResetSeed
  · intro hSeedC
    obtain ⟨⟨r, hr, _⟩, _⟩ := hSeedC
    rw [hC.allSettled r] at hr
    cases hr
  · exact hμv
  · simpa [C'] using hSeed

/-- Even-population lower-median/max timer-one reset-firing step creates a
`CorrectResetSeed` with the mass of one ordered scheduler pair. -/
theorem PEM_even_lower_median_max_timer_one_reset_seed_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hv_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        CorrectResetSeed 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hC.swap_condition_false μ v
  have h_post_diff : (C μ).1.answer ≠ (C v).1.answer := by
    intro hsame
    exact hv_wrong (by rw [← hsame, hμ_correct])
  have hsnap :
      (C' μ).1.role = .Resetting ∧ (C' μ).1.resetcount = Rmax ∧
        (C' μ).1.leader = .L ∧
      (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
        (C' v).1.leader = .L ∧
      ∀ y : Fin n, (C' y).1.role = .Resetting →
        (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
    simpa [C', P, PEMProtocolCoupled, PEMProtocol] using
      (trigger_reset_from_InSrank_even_lower_timer_one_max_no_swap_with_snapshot
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hC.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer
        h_no_swap h_post_diff)
  have htr :
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C μ, C v) =
        ({ (C μ).1 with
            answer := (C μ).1.answer,
            timer := 0,
            role := .Resetting,
            leader := .L,
            resetcount := Rmax },
         { (C v).1 with
            answer := (C μ).1.answer,
            role := .Resetting,
            leader := .L,
            resetcount := Rmax }) := by
    simpa using
      (propagation_reset_fires_even_lower_timer_one_max_no_swap_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (hRank := rankDeltaOSSR_satisfies_fix)
        (C := C) hC.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer
        h_no_swap h_post_diff)
  have hmaj : majorityAnswer C' = majorityAnswer C := by
    simpa [C', P, PEMProtocolCoupled, PEMProtocol] using
      (majorityAnswer_step_eq
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C μ v)
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_ans' : (C' μ).1.answer = majorityAnswer C' := by
    rw [hmaj]
    dsimp [C', P, PEMProtocolCoupled, PEMProtocol]
    rw [congrArg AgentState.answer hfst]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C μ, C v)).1.answer = majorityAnswer C
    rw [htr, hμ_correct]
  have hv_ans' : (C' v).1.answer = majorityAnswer C' := by
    rw [hmaj]
    dsimp [C', P, PEMProtocolCoupled, PEMProtocol]
    rw [congrArg AgentState.answer hsnd]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C μ, C v)).2.answer = majorityAnswer C
    rw [htr, hμ_correct]
  have hN_bound : nonResettingCount C' < Rmax := by
    have hcard_le : nonResettingCount C' ≤ n - 1 := by
      set S := Finset.univ.filter
        (fun w : Fin n => (C' w).1.role ≠ .Resetting) with hS
      have hsub : S ⊆ Finset.univ.erase μ := by
        intro x hx
        have hx_ne : x ≠ μ := by
          intro hxμ
          subst x
          have hx_not : (C' μ).1.role ≠ .Resetting := by
            rw [hS] at hx
            exact (Finset.mem_filter.mp hx).2
          rw [hsnap.1] at hx_not
          exact hx_not rfl
        exact Finset.mem_erase.mpr ⟨hx_ne, Finset.mem_univ x⟩
      have hle := Finset.card_le_card hsub
      have herase : (Finset.univ.erase μ).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ μ)]
        simp
      unfold nonResettingCount
      rw [← hS]
      omega
    have hn_pos : 0 < n := by omega
    have hRmax_pos : 0 < Rmax := Nat.lt_of_lt_of_le hn_pos hRmax
    omega
  have hRmax_pos : 0 < Rmax := by
    have hn_pos : 0 < n := by omega
    exact Nat.lt_of_lt_of_le hn_pos hRmax
  have hSeed : CorrectResetSeed C' := by
    refine ⟨⟨μ, hsnap.1, ?_, hsnap.2.2.1, hμ_ans'⟩, ?_⟩
    · rw [hsnap.2.1]
      exact hN_bound
    · intro w hw
      by_cases hwμ : w = μ
      · subst w
        refine ⟨?_, hμ_ans'⟩
        · rw [hsnap.2.1]
          exact hRmax_pos
      · by_cases hwv : w = v
        · subst w
          refine ⟨?_, hv_ans'⟩
          · rw [hsnap.2.2.2.2.1]
            exact hRmax_pos
        · have hOldSettled : (C' w).1.role = .Settled := by
            dsimp [C', P]
            simp [Config.step, hμv, hwμ, hwv, hC.allSettled w]
          rw [hOldSettled] at hw
          cases hw
  apply Probability.ProbHitWithin_one_lower_bound_of_step
    (P := P) hn2 C CorrectResetSeed
  · intro hSeedC
    obtain ⟨⟨r, hr, _⟩, _⟩ := hSeedC
    rw [hC.allSettled r] at hr
    cases hr
  · exact hμv
  · simpa [C'] using hSeed

/-- Marginal one-step form of
`PEM_odd_median_max_timer_one_reset_seed_prob_lower_bound`. -/
theorem PEM_odd_median_max_timer_one_reset_seed_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hμ_input_A : (C μ).2 = Opinion.A)
    (h_timer : (C μ).1.timer = 1)
    (h_max_wrong : (C v).1.answer ≠ opinionToAnswer (C μ).2) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by classical exact inferInstance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C CorrectResetSeed
        (by classical exact inferInstance) 1 := by
  classical
  have hGoal : ¬ CorrectResetSeed C := by
    intro hSeedC
    obtain ⟨⟨r, hr, _⟩, _⟩ := hSeedC
    rw [hC.allSettled r] at hr
    cases hr
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C CorrectResetSeed 1 :=
    PEM_odd_median_max_timer_one_reset_seed_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hRmax hC hμv hpar hμ_med hv_max hμ_input_A
      h_timer h_max_wrong
  simpa using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := CorrectResetSeed) hGoal hhit)

/-- Marginal one-step form of
`PEM_even_lower_median_max_timer_one_reset_seed_prob_lower_bound`. -/
theorem PEM_even_lower_median_max_timer_one_reset_seed_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hv_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by classical exact inferInstance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C CorrectResetSeed
        (by classical exact inferInstance) 1 := by
  classical
  have hGoal : ¬ CorrectResetSeed C := by
    intro hSeedC
    obtain ⟨⟨r, hr, _⟩, _⟩ := hSeedC
    rw [hC.allSettled r] at hr
    cases hr
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C CorrectResetSeed 1 :=
    PEM_even_lower_median_max_timer_one_reset_seed_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hRmax hC hμv hpar hμ_lower hv_max h_timer
      hμ_correct hv_wrong
  simpa using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := CorrectResetSeed) hGoal hhit)

/-- Resetting agents that can safely spread the correct reset seed without
exhausting their reset fuel. -/
def richResetSeedSet (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter fun r : Fin n =>
    (C r).1.role = .Resetting ∧
    nonResettingCount C < (C r).1.resetcount ∧
    (C r).1.answer = majorityAnswer C

def richResetSeedCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (richResetSeedSet C).card

theorem richResetSeedCount_pos_of_CorrectResetSeed
    {C : Config (AgentState n) Opinion n} (hSeed : CorrectResetSeed C) :
    0 < richResetSeedCount C := by
  classical
  obtain ⟨⟨r, hr_role, hr_count, _hr_leader, hr_answer⟩, _⟩ := hSeed
  unfold richResetSeedCount richResetSeedSet
  apply Finset.card_pos.mpr
  exact ⟨r, Finset.mem_filter.mpr
    ⟨Finset.mem_univ r, hr_role, hr_count, hr_answer⟩⟩

theorem richResetSeedCount_le_n
    (C : Config (AgentState n) Opinion n) :
    richResetSeedCount C ≤ n := by
  classical
  unfold richResetSeedCount richResetSeedSet
  calc
    (Finset.univ.filter fun r : Fin n =>
        (C r).1.role = .Resetting ∧
        nonResettingCount C < (C r).1.resetcount ∧
        (C r).1.answer = majorityAnswer C).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

theorem propagate_reset_step_nonResettingCount_eq_sub_one
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {r v : Fin n} (hrv : r ≠ v)
    (hr_res : (C r).1.role = .Resetting)
    (hr_rc : 0 < (C r).1.resetcount)
    (hv_not : (C v).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    nonResettingCount (C.step P r v) + 1 = nonResettingCount C := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  set C₁ : Config (AgentState n) Opinion n := C.step P r v with hC₁
  have hstep :=
    propagate_reset_step_nonResettingCount_lt
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax C hrv hr_res hr_rc hv_not
  have hr_reset : (C₁ r).1.role = .Resetting := by
    simpa [C₁, P] using hstep.1
  have hv_reset : (C₁ v).1.role = .Resetting := by
    simpa [C₁, P] using hstep.2.2.1
  set S := Finset.univ.filter fun w : Fin n => (C w).1.role ≠ .Resetting with hS
  set S' := Finset.univ.filter fun w : Fin n => (C₁ w).1.role ≠ .Resetting with hS'
  have hv_mem : v ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ v, hv_not⟩
  have hS'_eq : S' = S.erase v := by
    ext x
    constructor
    · intro hx
      have hx_not : (C₁ x).1.role ≠ .Resetting := by
        rw [hS'] at hx
        exact (Finset.mem_filter.mp hx).2
      have hx_ne_v : x ≠ v := by
        intro hxv
        subst x
        exact hx_not hv_reset
      have hx_ne_r : x ≠ r := by
        intro hxr
        subst x
        exact hx_not hr_reset
      have hx_state : C₁ x = C x := by
        rw [hC₁]
        dsimp [P]
        simp [Config.step, hrv, hx_ne_r, hx_ne_v]
      have hx_old : (C x).1.role ≠ .Resetting := by
        intro hreset
        exact hx_not (by rw [hx_state]; exact hreset)
      rw [Finset.mem_erase, hS, Finset.mem_filter]
      exact ⟨hx_ne_v, Finset.mem_univ x, hx_old⟩
    · intro hx
      have hx_ne_v : x ≠ v := (Finset.mem_erase.mp hx).1
      have hx_old : (C x).1.role ≠ .Resetting :=
        (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).2
      have hx_ne_r : x ≠ r := by
        intro hxr
        subst x
        exact hx_old hr_res
      have hx_state : C₁ x = C x := by
        rw [hC₁]
        dsimp [P]
        simp [Config.step, hrv, hx_ne_r, hx_ne_v]
      rw [hS', Finset.mem_filter]
      refine ⟨Finset.mem_univ x, ?_⟩
      rw [hx_state]
      exact hx_old
  have hcard : S'.card + 1 = S.card := by
    rw [hS'_eq, Finset.card_erase_of_mem hv_mem]
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨v, hv_mem⟩))
  dsimp [nonResettingCount]
  change (Finset.univ.filter (fun w : Fin n => (C₁ w).1.role ≠ .Resetting)).card + 1 =
    (Finset.univ.filter (fun w : Fin n => (C w).1.role ≠ .Resetting)).card
  rw [← hS, ← hS']
  exact hcard

/-- Once a correct reset seed exists, every interaction from the seed to a
non-`Resetting` agent keeps the correct-seed invariant and strictly decreases
`nonResettingCount`.  This is the stochastic companion to the deterministic
seed-propagation induction: it counts all currently non-resetting partners,
not just one chosen schedule edge. -/
theorem PEM_correctResetSeed_nonResetting_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C) (hpos : 0 < nonResettingCount C) :
    (((nonResettingCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D < nonResettingCount C) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  obtain ⟨⟨r, hr_role, hr_count, hr_leader, hr_answer⟩, hAllResetting⟩ := hSeed
  let NR : Finset (Fin n) :=
    Finset.univ.filter fun v : Fin n => (C v).1.role ≠ .Resetting
  let S : Finset (Fin n × Fin n) := NR.image fun v => (r, v)
  have hr_count_pos : 0 < (C r).1.resetcount :=
    (hAllResetting r hr_role).1
  have hNR_card : NR.card = nonResettingCount C := by
    rfl
  have hS_card : S.card = nonResettingCount C := by
    dsimp [S]
    rw [Finset.card_image_of_injective]
    · exact hNR_card
    · intro a b h
      exact congrArg Prod.snd h
  have hS_sub : S ⊆ Probability.OffDiagonalPairs n := by
    intro p hp
    dsimp [S, NR] at hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨v, hv, hpv⟩
    rw [Probability.mem_offDiagonalPairs]
    rw [← hpv]
    intro hrv
    have hv_not : (C v).1.role ≠ .Resetting :=
      (Finset.mem_filter.mp hv).2
    have hrv' : r = v := by
      simpa using hrv
    subst v
    exact hv_not hr_role
  have hstep : ∀ p ∈ S,
      CorrectResetSeed (C.step P p.1 p.2) ∧
        nonResettingCount (C.step P p.1 p.2) < nonResettingCount C := by
    intro p hp
    dsimp [S, NR] at hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨v, hv, hpv⟩
    rw [← hpv]
    have hv_not : (C v).1.role ≠ .Resetting :=
      (Finset.mem_filter.mp hv).2
    have hrv : r ≠ v := by
      intro h
      subst v
      exact hv_not hr_role
    have hdrop :=
      propagate_reset_step_nonResettingCount_lt
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hrv hr_role hr_count_pos hv_not
    have hsender :=
      propagate_reset_spreader_state
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hrv hr_role hr_count_pos hv_not
    have hpartner :=
      propagate_reset_step_partner_rc
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hrv hr_role hr_count_pos hv_not
    have hans :=
      propagate_reset_step_answer_trace
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hrv hr_role hr_count_pos hv_not hr_answer
    have hmaj :
        majorityAnswer (C.step P r v) = majorityAnswer C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C r v)
    have hothers : ∀ w : Fin n, w ≠ r → w ≠ v →
        C.step P r v w = C w := by
      intro w hwr hwv
      dsimp [P, PEMProtocolCoupled, PEMProtocol]
      simp [Config.step, hrv, hwr, hwv]
    have hSeed' : CorrectResetSeed (C.step P r v) := by
      refine ⟨⟨r, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.1
      · have hdrop_count :
            nonResettingCount (C.step P r v) < nonResettingCount C := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.2.2
        have hrc :
            (C.step P r v r).1.resetcount = (C r).1.resetcount - 1 := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.1
        rw [hrc]
        omega
      · have hleader :
            (C.step P r v r).1.leader = (C r).1.leader := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using hsender.2.2
        rw [hleader, hr_leader]
      · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.1
      · intro w hw
        by_cases hwr : w = r
        · subst w
          constructor
          · have hrc :
                (C.step P r v r).1.resetcount =
                  (C r).1.resetcount - 1 := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.1
            rw [hrc]
            omega
          · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.1
        · by_cases hwv : w = v
          · subst w
            constructor
            · have hrc :
                (C.step P r v v).1.resetcount =
                  (C r).1.resetcount - 1 := by
                simpa [P, PEMProtocolCoupled, PEMProtocol] using hpartner.2
              rw [hrc]
              omega
            · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.2
          · have hw_state : C.step P r v w = C w := hothers w hwr hwv
            have hw_old_role : (C w).1.role = .Resetting := by
              rw [← hw_state]
              exact hw
            have hw_old := hAllResetting w hw_old_role
            constructor
            · rw [hw_state]
              exact hw_old.1
            · rw [hw_state, hmaj]
              exact hw_old.2
    exact ⟨hSeed', by simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.2.2⟩
  have hGoal_not :
      ¬ (CorrectResetSeed C ∧ nonResettingCount C < nonResettingCount C) := by
    intro h
    exact Nat.lt_irrefl _ h.2
  have hmass :
      Probability.pairSetMass n hn2 S =
        (((nonResettingCount C : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
    rw [Probability.pairSetMass_eq_card_mul_inv_of_subset n hn2 S hS_sub,
      hS_card]
  calc
    (((nonResettingCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
        = Probability.pairSetMass n hn2 S := hmass.symm
    _ ≤ Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D < nonResettingCount C) 1 :=
          Probability.ProbHitWithin_one_lower_bound_of_pairSet
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
            (fun D => CorrectResetSeed D ∧
              nonResettingCount D < nonResettingCount C)
            hGoal_not S hS_sub hstep

/-- Epidemic version of the correct-seed propagation bound.  Every rich reset
seed can recruit every non-`Resetting` agent; after such a step the
`CorrectResetSeed` invariant is still true and `nonResettingCount` strictly
drops. -/
theorem PEM_richResetSeed_nonResetting_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C) (hpos : 0 < nonResettingCount C) :
    (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D < nonResettingCount C) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  obtain ⟨⟨r₀, hr₀_role, hr₀_count, hr₀_leader, hr₀_answer⟩,
    hAllResetting⟩ := hSeed
  let NR : Finset (Fin n) :=
    Finset.univ.filter fun v : Fin n => (C v).1.role ≠ .Resetting
  let S : Finset (Fin n × Fin n) := (richResetSeedSet C).product NR
  have hNR_card : NR.card = nonResettingCount C := by
    rfl
  have hS_card : S.card = richResetSeedCount C * nonResettingCount C := by
    dsimp [S, richResetSeedCount]
    rw [Finset.card_product, hNR_card]
  have hS_sub : S ⊆ Probability.OffDiagonalPairs n := by
    intro p hp
    dsimp [S, NR] at hp
    obtain ⟨hq_mem, hv_mem⟩ := Finset.mem_product.mp hp
    have hq_role : (C p.1).1.role = .Resetting :=
      (Finset.mem_filter.mp hq_mem).2.1
    have hv_not : (C p.2).1.role ≠ .Resetting :=
      (Finset.mem_filter.mp hv_mem).2
    rw [Probability.mem_offDiagonalPairs]
    intro hp_eq
    exact hv_not (by rw [← hp_eq]; exact hq_role)
  have hstep : ∀ p ∈ S,
      CorrectResetSeed (C.step P p.1 p.2) ∧
        nonResettingCount (C.step P p.1 p.2) < nonResettingCount C := by
    intro p hp
    dsimp [S, NR] at hp
    obtain ⟨hq_mem, hv_mem⟩ := Finset.mem_product.mp hp
    have hq_rich := (Finset.mem_filter.mp hq_mem).2
    have hq_role : (C p.1).1.role = .Resetting := hq_rich.1
    have hq_count : nonResettingCount C < (C p.1).1.resetcount :=
      hq_rich.2.1
    have hq_answer : (C p.1).1.answer = majorityAnswer C :=
      hq_rich.2.2
    have hv_not : (C p.2).1.role ≠ .Resetting :=
      (Finset.mem_filter.mp hv_mem).2
    have hp_ne : p.1 ≠ p.2 := by
      intro h
      exact hv_not (by rw [← h]; exact hq_role)
    have hq_count_pos : 0 < (C p.1).1.resetcount := by
      omega
    have hdrop :=
      propagate_reset_step_nonResettingCount_lt
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hp_ne hq_role hq_count_pos hv_not
    have hsender :=
      propagate_reset_spreader_state
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hp_ne hq_role hq_count_pos hv_not
    have hpartner :=
      propagate_reset_step_partner_rc
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hp_ne hq_role hq_count_pos hv_not
    have hans :=
      propagate_reset_step_answer_trace
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hp_ne hq_role hq_count_pos hv_not hq_answer
    have hmaj :
        majorityAnswer (C.step P p.1 p.2) = majorityAnswer C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C p.1 p.2)
    have hothers : ∀ w : Fin n, w ≠ p.1 → w ≠ p.2 →
        C.step P p.1 p.2 w = C w := by
      intro w hwq hwv
      dsimp [P, PEMProtocolCoupled, PEMProtocol]
      simp [Config.step, hp_ne, hwq, hwv]
    have hSeed' : CorrectResetSeed (C.step P p.1 p.2) := by
      refine ⟨?_, ?_⟩
      · by_cases hqr₀ : p.1 = r₀
        · refine ⟨p.1, ?_, ?_, ?_, ?_⟩
          · simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.1
          · have hrc :
                (C.step P p.1 p.2 p.1).1.resetcount =
                  (C p.1).1.resetcount - 1 := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.1
            have hN_drop :
                nonResettingCount (C.step P p.1 p.2) <
                  nonResettingCount C := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.2.2
            rw [hrc]
            omega
          · have hleader :
                (C.step P p.1 p.2 p.1).1.leader = (C p.1).1.leader := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hsender.2.2
            rw [hleader, hqr₀, hr₀_leader]
          · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.1
        · have hr₀_ne_v : r₀ ≠ p.2 := by
            intro h
            subst h
            exact hv_not hr₀_role
          have hr₀_state : C.step P p.1 p.2 r₀ = C r₀ :=
            hothers r₀ (by intro h; exact hqr₀ h.symm) hr₀_ne_v
          refine ⟨r₀, ?_, ?_, ?_, ?_⟩
          · rw [hr₀_state]
            exact hr₀_role
          · rw [hr₀_state]
            have hN_drop :
                nonResettingCount (C.step P p.1 p.2) <
                  nonResettingCount C := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.2.2
            omega
          · rw [hr₀_state]
            exact hr₀_leader
          · rw [hr₀_state, hmaj]
            exact hr₀_answer
      · intro w hw
        by_cases hwq : w = p.1
        · subst w
          constructor
          · have hrc :
                (C.step P p.1 p.2 p.1).1.resetcount =
                  (C p.1).1.resetcount - 1 := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.1
            rw [hrc]
            omega
          · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.1
        · by_cases hwv : w = p.2
          · subst w
            constructor
            · have hrc :
                (C.step P p.1 p.2 p.2).1.resetcount =
                  (C p.1).1.resetcount - 1 := by
                simpa [P, PEMProtocolCoupled, PEMProtocol] using hpartner.2
              rw [hrc]
              omega
            · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.2
          · have hw_state : C.step P p.1 p.2 w = C w := hothers w hwq hwv
            have hw_old_role : (C w).1.role = .Resetting := by
              rw [← hw_state]
              exact hw
            have hw_old := hAllResetting w hw_old_role
            constructor
            · rw [hw_state]
              exact hw_old.1
            · rw [hw_state, hmaj]
              exact hw_old.2
    exact ⟨hSeed', by simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.2.2⟩
  have hGoal_not :
      ¬ (CorrectResetSeed C ∧ nonResettingCount C < nonResettingCount C) := by
    intro h
    exact Nat.lt_irrefl _ h.2
  have hmass :
      Probability.pairSetMass n hn2 S =
        (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
    rw [Probability.pairSetMass_eq_card_mul_inv_of_subset n hn2 S hS_sub,
      hS_card]
  calc
    (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
        = Probability.pairSetMass n hn2 S := hmass.symm
    _ ≤ Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D < nonResettingCount C) 1 :=
          Probability.ProbHitWithin_one_lower_bound_of_pairSet
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
            (fun D => CorrectResetSeed D ∧
              nonResettingCount D < nonResettingCount C)
            hGoal_not S hS_sub hstep

/-- Uniform one-step descent form of the rich-seed epidemic bound.  Since
`CorrectResetSeed` guarantees at least one rich seed and the phase is live
when `nonResettingCount > 0`, the one-step descent probability is at least
one ordered scheduler edge. -/
theorem PEM_correctResetSeed_nonResetting_positive_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C) (hpos : 0 < nonResettingCount C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D < nonResettingCount C) 1 := by
  classical
  have hrich_pos : 0 < richResetSeedCount C :=
    richResetSeedCount_pos_of_CorrectResetSeed hSeed
  have hnat :
      1 ≤ richResetSeedCount C * nonResettingCount C := by
    exact Nat.succ_le_of_lt (Nat.mul_pos hrich_pos hpos)
  have hcoef :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
    calc
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹
          = (1 : ENNReal) *
              ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by simp
      _ ≤ ((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
            have hcast :
                (1 : ENNReal) ≤
                  ((richResetSeedCount C * nonResettingCount C : ℕ) :
                    ENNReal) := by
              exact_mod_cast hnat
            exact mul_le_mul_left hcast _
  exact le_trans hcoef
    (PEM_richResetSeed_nonResetting_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hDmax hSeed hpos)

/-- Marginal one-step version of
`PEM_correctResetSeed_nonResetting_positive_descent_prob_lower_bound`, for
reset-epidemic phase composition. -/
theorem PEM_correctResetSeed_nonResetting_positive_descent_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C) (hpos : 0 < nonResettingCount C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by infer_instance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D < nonResettingCount C)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => CorrectResetSeed D ∧
      nonResettingCount D < nonResettingCount C
  have hGoal : ¬ Goal C := by
    intro h
    exact Nat.lt_irrefl _ h.2
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_correctResetSeed_nonResetting_positive_descent_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hDmax hSeed hpos)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-- Successful rich-seed propagation is not only a descent in
`nonResettingCount`; it also strictly increases the number of rich reset
seeds.  This is the local epidemic-growth statement needed for the real
Kanaya-style propagation window. -/
theorem PEM_richResetSeed_growth_exact_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C) (hpos : 0 < nonResettingCount C) :
    (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D + 1 = nonResettingCount C ∧
          richResetSeedCount C < richResetSeedCount D) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  obtain ⟨⟨r₀, hr₀_role, hr₀_count, hr₀_leader, hr₀_answer⟩,
    hAllResetting⟩ := hSeed
  let NR : Finset (Fin n) :=
    Finset.univ.filter fun v : Fin n => (C v).1.role ≠ .Resetting
  let S : Finset (Fin n × Fin n) := (richResetSeedSet C).product NR
  have hNR_card : NR.card = nonResettingCount C := by
    rfl
  have hS_card : S.card = richResetSeedCount C * nonResettingCount C := by
    dsimp [S, richResetSeedCount]
    rw [Finset.card_product, hNR_card]
  have hS_sub : S ⊆ Probability.OffDiagonalPairs n := by
    intro p hp
    dsimp [S, NR] at hp
    obtain ⟨hq_mem, hv_mem⟩ := Finset.mem_product.mp hp
    have hq_role : (C p.1).1.role = .Resetting :=
      (Finset.mem_filter.mp hq_mem).2.1
    have hv_not : (C p.2).1.role ≠ .Resetting :=
      (Finset.mem_filter.mp hv_mem).2
    rw [Probability.mem_offDiagonalPairs]
    intro hp_eq
    exact hv_not (by rw [← hp_eq]; exact hq_role)
  have hstep : ∀ p ∈ S,
      CorrectResetSeed (C.step P p.1 p.2) ∧
        nonResettingCount (C.step P p.1 p.2) + 1 = nonResettingCount C ∧
        richResetSeedCount C < richResetSeedCount (C.step P p.1 p.2) := by
    intro p hp
    dsimp [S, NR] at hp
    obtain ⟨hq_mem, hv_mem⟩ := Finset.mem_product.mp hp
    have hq_rich := (Finset.mem_filter.mp hq_mem).2
    have hq_role : (C p.1).1.role = .Resetting := hq_rich.1
    have hq_count : nonResettingCount C < (C p.1).1.resetcount :=
      hq_rich.2.1
    have hq_answer : (C p.1).1.answer = majorityAnswer C :=
      hq_rich.2.2
    have hv_not : (C p.2).1.role ≠ .Resetting :=
      (Finset.mem_filter.mp hv_mem).2
    have hp_ne : p.1 ≠ p.2 := by
      intro h
      exact hv_not (by rw [← h]; exact hq_role)
    have hq_count_pos : 0 < (C p.1).1.resetcount := by omega
    have hdrop :=
      propagate_reset_step_nonResettingCount_lt
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hp_ne hq_role hq_count_pos hv_not
    have hsender :=
      propagate_reset_spreader_state
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hp_ne hq_role hq_count_pos hv_not
    have hpartner :=
      propagate_reset_step_partner_rc
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hp_ne hq_role hq_count_pos hv_not
    have hans :=
      propagate_reset_step_answer_trace
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hp_ne hq_role hq_count_pos hv_not hq_answer
    have hmaj :
        majorityAnswer (C.step P p.1 p.2) = majorityAnswer C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C p.1 p.2)
    have hN_drop :
        nonResettingCount (C.step P p.1 p.2) < nonResettingCount C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.2.2
    have hN_exact :
        nonResettingCount (C.step P p.1 p.2) + 1 =
          nonResettingCount C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        (propagate_reset_step_nonResettingCount_eq_sub_one
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
          hDmax C hp_ne hq_role hq_count_pos hv_not)
    have hothers : ∀ w : Fin n, w ≠ p.1 → w ≠ p.2 →
        C.step P p.1 p.2 w = C w := by
      intro w hwq hwv
      dsimp [P, PEMProtocolCoupled, PEMProtocol]
      simp [Config.step, hp_ne, hwq, hwv]
    have hSeed' : CorrectResetSeed (C.step P p.1 p.2) := by
      refine ⟨?_, ?_⟩
      · by_cases hqr₀ : p.1 = r₀
        · refine ⟨p.1, ?_, ?_, ?_, ?_⟩
          · simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.1
          · have hrc :
                (C.step P p.1 p.2 p.1).1.resetcount =
                  (C p.1).1.resetcount - 1 := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.1
            rw [hrc]
            omega
          · have hleader :
                (C.step P p.1 p.2 p.1).1.leader = (C p.1).1.leader := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hsender.2.2
            rw [hleader, hqr₀, hr₀_leader]
          · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.1
        · have hr₀_ne_v : r₀ ≠ p.2 := by
            intro h
            subst h
            exact hv_not hr₀_role
          have hr₀_state : C.step P p.1 p.2 r₀ = C r₀ :=
            hothers r₀ (by intro h; exact hqr₀ h.symm) hr₀_ne_v
          refine ⟨r₀, ?_, ?_, ?_, ?_⟩
          · rw [hr₀_state]
            exact hr₀_role
          · rw [hr₀_state]
            omega
          · rw [hr₀_state]
            exact hr₀_leader
          · rw [hr₀_state, hmaj]
            exact hr₀_answer
      · intro w hw
        by_cases hwq : w = p.1
        · subst w
          constructor
          · have hrc :
                (C.step P p.1 p.2 p.1).1.resetcount =
                  (C p.1).1.resetcount - 1 := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.1
            rw [hrc]
            omega
          · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.1
        · by_cases hwv : w = p.2
          · subst w
            constructor
            · have hrc :
                (C.step P p.1 p.2 p.2).1.resetcount =
                  (C p.1).1.resetcount - 1 := by
                simpa [P, PEMProtocolCoupled, PEMProtocol] using hpartner.2
              rw [hrc]
              omega
            · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.2
          · have hw_state : C.step P p.1 p.2 w = C w := hothers w hwq hwv
            have hw_old_role : (C w).1.role = .Resetting := by
              rw [← hw_state]
              exact hw
            have hw_old := hAllResetting w hw_old_role
            constructor
            · rw [hw_state]
              exact hw_old.1
            · rw [hw_state, hmaj]
              exact hw_old.2
    have hp2_not_old : p.2 ∉ richResetSeedSet C := by
      intro hp2_old
      have hp2_role : (C p.2).1.role = .Resetting :=
        (Finset.mem_filter.mp hp2_old).2.1
      exact hv_not hp2_role
    have hsub_insert :
        insert p.2 (richResetSeedSet C) ⊆
          richResetSeedSet (C.step P p.1 p.2) := by
      intro w hw
      rw [Finset.mem_insert] at hw
      rcases hw with hwv | hwold
      · subst w
        unfold richResetSeedSet
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ p.2, ?_, ?_, ?_⟩
        · simpa [P, PEMProtocolCoupled, PEMProtocol] using hpartner.1
        · have hrc :
              (C.step P p.1 p.2 p.2).1.resetcount =
                (C p.1).1.resetcount - 1 := by
            simpa [P, PEMProtocolCoupled, PEMProtocol] using hpartner.2
          rw [hrc]
          omega
        · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.2
      · have hw_rich := (Finset.mem_filter.mp hwold).2
        have hrole_new : (C.step P p.1 p.2 w).1.role = .Resetting := by
          by_cases hwq : w = p.1
          · subst w
            simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.1
          · have hwv_ne : w ≠ p.2 := by
              intro h
              subst w
              exact hp2_not_old hwold
            have hw_state : C.step P p.1 p.2 w = C w :=
              hothers w hwq hwv_ne
            rw [hw_state]
            exact hw_rich.1
        have hcount_new :
            nonResettingCount (C.step P p.1 p.2) <
              (C.step P p.1 p.2 w).1.resetcount := by
          by_cases hwq : w = p.1
          · subst w
            have hrc :
                (C.step P p.1 p.2 p.1).1.resetcount =
                  (C p.1).1.resetcount - 1 := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.1
            rw [hrc]
            omega
          · have hwv_ne : w ≠ p.2 := by
              intro h
              subst w
              exact hp2_not_old hwold
            have hw_state : C.step P p.1 p.2 w = C w :=
              hothers w hwq hwv_ne
            rw [hw_state]
            omega
        have hanswer_new :
            (C.step P p.1 p.2 w).1.answer =
              majorityAnswer (C.step P p.1 p.2) := by
          by_cases hwq : w = p.1
          · subst w
            simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.1
          · have hwv_ne : w ≠ p.2 := by
              intro h
              subst w
              exact hp2_not_old hwold
            have hw_state : C.step P p.1 p.2 w = C w :=
              hothers w hwq hwv_ne
            rw [hw_state, hmaj]
            exact hw_rich.2.2
        unfold richResetSeedSet
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ w, hrole_new, hcount_new, hanswer_new⟩
    have hcard_insert :
        (insert p.2 (richResetSeedSet C)).card =
          richResetSeedCount C + 1 := by
      unfold richResetSeedCount
      rw [Finset.card_insert_of_notMem hp2_not_old]
    have hgrowth : richResetSeedCount C <
        richResetSeedCount (C.step P p.1 p.2) := by
      have hle := Finset.card_le_card hsub_insert
      have hle' :
          richResetSeedCount C + 1 ≤
            richResetSeedCount (C.step P p.1 p.2) := by
        rw [← hcard_insert]
        unfold richResetSeedCount
        exact hle
      omega
    exact ⟨hSeed', hN_exact, hgrowth⟩
  have hGoal_not :
      ¬ (CorrectResetSeed C ∧ nonResettingCount C + 1 = nonResettingCount C ∧
          richResetSeedCount C < richResetSeedCount C) := by
    intro h
    omega
  have hmass :
      Probability.pairSetMass n hn2 S =
        (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
    rw [Probability.pairSetMass_eq_card_mul_inv_of_subset n hn2 S hS_sub,
      hS_card]
  calc
    (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
        = Probability.pairSetMass n hn2 S := hmass.symm
    _ ≤ Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D + 1 = nonResettingCount C ∧
          richResetSeedCount C < richResetSeedCount D) 1 :=
          Probability.ProbHitWithin_one_lower_bound_of_pairSet
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
            (fun D => CorrectResetSeed D ∧
              nonResettingCount D + 1 = nonResettingCount C ∧
              richResetSeedCount C < richResetSeedCount D)
            hGoal_not S hS_sub hstep

theorem PEM_richResetSeed_growth_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C) (hpos : 0 < nonResettingCount C) :
    (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D < nonResettingCount C ∧
          richResetSeedCount C < richResetSeedCount D) 1 := by
  classical
  have hexact :=
    PEM_richResetSeed_growth_exact_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hDmax hSeed hpos
  have hGoalExact :
      ¬ (CorrectResetSeed C ∧
          nonResettingCount C + 1 = nonResettingCount C ∧
          richResetSeedCount C < richResetSeedCount C) := by
    intro h
    omega
  have hGoalWeak :
      ¬ (CorrectResetSeed C ∧ nonResettingCount C < nonResettingCount C ∧
          richResetSeedCount C < richResetSeedCount C) := by
    intro h
    exact Nat.lt_irrefl _ h.2.1
  have hmono :
      Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
          (fun D => CorrectResetSeed D ∧
            nonResettingCount D + 1 = nonResettingCount C ∧
            richResetSeedCount C < richResetSeedCount D) 1 ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
          (fun D => CorrectResetSeed D ∧
            nonResettingCount D < nonResettingCount C ∧
            richResetSeedCount C < richResetSeedCount D) 1 :=
    Probability.ProbHitWithin_one_mono_goal
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal₁ := fun D => CorrectResetSeed D ∧
        nonResettingCount D + 1 = nonResettingCount C ∧
        richResetSeedCount C < richResetSeedCount D)
      (Goal₂ := fun D => CorrectResetSeed D ∧
        nonResettingCount D < nonResettingCount C ∧
        richResetSeedCount C < richResetSeedCount D)
      hGoalExact hGoalWeak
      (by
        intro D hD
        refine ⟨hD.1, ?_, hD.2.2⟩
        omega)
  exact le_trans hexact hmono

/-- Marginal one-step version of
`PEM_richResetSeed_growth_exact_prob_lower_bound`, for phase composition.
From the current state the exact-growth target is false, so one-step hitting
and one-step endpoint reachability coincide. -/
theorem PEM_richResetSeed_growth_exact_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C) (hpos : 0 < nonResettingCount C) :
    (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by infer_instance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D + 1 = nonResettingCount C ∧
          richResetSeedCount C < richResetSeedCount D)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => CorrectResetSeed D ∧
      nonResettingCount D + 1 = nonResettingCount C ∧
      richResetSeedCount C < richResetSeedCount D
  have hGoal : ¬ Goal C := by
    intro h
    dsimp [Goal] at h
    omega
  have hhit :
      (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_richResetSeed_growth_exact_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hDmax hSeed hpos)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-- Endpoint form of the reset-seed epidemic: once no non-`Resetting` agent
remains, `CorrectResetSeed` gives exactly the all-resetting positive-leader
uniform-answer shape consumed by the deterministic Phase-A normalizer. -/
theorem allResetting_pos_leader_uniform_answer_of_CorrectResetSeed_nonResetting_zero
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C) (hzero : nonResettingCount C = 0) :
    (∀ w : Fin n, (C w).1.role = .Resetting) ∧
    (∀ w : Fin n, 0 < (C w).1.resetcount) ∧
    (∃ ℓ : Fin n, (C ℓ).1.leader = .L) ∧
    (∀ w : Fin n, (C w).1.answer = majorityAnswer C) := by
  classical
  obtain ⟨⟨r, hr_role, _hr_count, hr_leader, _hr_answer⟩, hAll⟩ := hSeed
  have hAllRole : ∀ w : Fin n, (C w).1.role = .Resetting := by
    intro w
    by_contra hw
    have hpos : 0 < nonResettingCount C := by
      unfold nonResettingCount
      apply Finset.card_pos.mpr
      exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩⟩
    omega
  refine ⟨hAllRole, ?_, ?_, ?_⟩
  · intro w
    exact (hAll w (hAllRole w)).1
  · exact ⟨r, hr_leader⟩
  · intro w
    exact (hAll w (hAllRole w)).2

/-- Qualitative deterministic consensus reachability for the coupled protocol
family used by the existing time-bound lemmas.  This is the deterministic
input that the stochastic layer must quantify by counting scheduler windows. -/
theorem PEM_consensus_reachable
    {n Rmax Emax Dmax : ℕ} {hn0 : 0 < n}
    [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig
          (execution (PEMProtocolCoupled n Rmax Emax Dmax hn0) C₀ γ t) := by
  simpa [PEMProtocolCoupled, PEMProtocol] using
    (P_EM_consensus_reachable_from_BurmanConvergence_only
      (n := n) (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hn4
      (burmanConvergence_concrete
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hn4 hEmax hDmax hRmax))

end SSEM
