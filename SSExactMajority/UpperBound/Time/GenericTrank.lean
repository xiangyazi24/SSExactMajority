import SSExactMajority.UpperBound.Time
import SSExactMajority.UpperBound.Time.TransitionLemmas
import SSExactMajority.UpperBound.Time.DecisionTiming
import SSExactMajority.UpperBound.Time.PhaseProofs

/-!
# Generic `trank` time-window restatements

This file keeps the legacy `PEMProtocolCoupled` window stack intact and adds
generic-`trank` wrappers for the paper's constant-timer regime.
-/

namespace SSEM

open scoped ENNReal

attribute [local instance] Classical.propDecidable

section TimerPreservation

private def GenericAgentTimerBounded (K : ℕ) (s : AgentState n) : Prop :=
  s.timer ≤ K

private def GenericPairTimerBounded (K : ℕ) (p : AgentState n × AgentState n) : Prop :=
  GenericAgentTimerBounded K p.1 ∧ GenericAgentTimerBounded K p.2

private theorem generic_resetOSSR_preserves_timer_bound
    {n Emax K : ℕ} {hn : 0 < n} {s : AgentState n}
    (hs : GenericAgentTimerBounded K s) :
    GenericAgentTimerBounded K (resetOSSR Emax hn s) := by
  rcases s with ⟨role, rank, leader, resetcount, answer, timer, children,
    errorcount, delaytimer⟩
  cases leader <;> simpa [GenericAgentTimerBounded, resetOSSR] using hs

private theorem generic_processAgent_preserves_timer_bound
    {n Emax Dmax K : ℕ} {hn : 0 < n} {s : AgentState n}
    {oldRc : ℕ} {partnerResetting : Bool}
    (hs : GenericAgentTimerBounded K s) :
    GenericAgentTimerBounded K
      (processAgent Emax Dmax hn s oldRc partnerResetting) := by
  unfold processAgent
  by_cases hmain : s.role = .Resetting ∧ s.resetcount = 0
  · rw [if_pos hmain]
    by_cases hold : 0 < oldRc
    · rw [if_pos hold]
      by_cases hfire :
          ({s with delaytimer := Dmax} : AgentState n).delaytimer = 0 ∨
            !partnerResetting
      · rw [if_pos hfire]
        exact generic_resetOSSR_preserves_timer_bound (s := {s with delaytimer := Dmax}) hs
      · rw [if_neg hfire]
        exact hs
    · rw [if_neg hold]
      by_cases hfire :
          ({s with delaytimer := s.delaytimer - 1} : AgentState n).delaytimer = 0 ∨
            !partnerResetting
      · rw [if_pos hfire]
        exact generic_resetOSSR_preserves_timer_bound
          (s := {s with delaytimer := s.delaytimer - 1}) hs
      · rw [if_neg hfire]
        exact hs
  · rw [if_neg hmain]
    exact hs

private theorem generic_propagateReset_recruit_preserves_timer_bound
    {n Emax Dmax K : ℕ} {a b : AgentState n}
    (ha : GenericAgentTimerBounded K a) (hb : GenericAgentTimerBounded K b) :
    GenericPairTimerBounded K
      (if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
        (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
      else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
        ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
      else (a, b)) := by
  unfold GenericPairTimerBounded
  split_ifs <;> simp_all [GenericAgentTimerBounded]

private theorem generic_propagateReset_sync_preserves_timer_bound
    {n K : ℕ} {a b : AgentState n}
    (ha : GenericAgentTimerBounded K a) (hb : GenericAgentTimerBounded K b) :
    GenericPairTimerBounded K
      (if a.role = .Resetting ∧ b.role = .Resetting then
        let newRc := max (a.resetcount - 1) (b.resetcount - 1)
        ({ a with resetcount := newRc }, { b with resetcount := newRc })
      else (a, b)) := by
  unfold GenericPairTimerBounded
  split_ifs <;> simp_all [GenericAgentTimerBounded]

private theorem generic_propagateReset_preserves_timer_bound
    {n Emax Dmax K : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : GenericAgentTimerBounded K a) (hb : GenericAgentTimerBounded K b) :
    GenericAgentTimerBounded K (propagateReset Emax Dmax hn a b).1 ∧
    GenericAgentTimerBounded K (propagateReset Emax Dmax hn a b).2 := by
  unfold propagateReset
  let p₁ :=
    if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
      (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
    else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
      ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
    else (a, b)
  have hp₁ : GenericPairTimerBounded K p₁ := by
    simpa [p₁] using
      generic_propagateReset_recruit_preserves_timer_bound
        (Emax := Emax) (Dmax := Dmax) ha hb
  let oldRcA := p₁.1.resetcount
  let oldRcB := p₁.2.resetcount
  let p₂ :=
    if p₁.1.role = .Resetting ∧ p₁.2.role = .Resetting then
      let newRc := max (p₁.1.resetcount - 1) (p₁.2.resetcount - 1)
      ({ p₁.1 with resetcount := newRc }, { p₁.2 with resetcount := newRc })
    else p₁
  have hp₂ : GenericPairTimerBounded K p₂ := by
    exact generic_propagateReset_sync_preserves_timer_bound hp₁.1 hp₁.2
  simpa [p₁, oldRcA, oldRcB, p₂, GenericPairTimerBounded] using
    And.intro
      (generic_processAgent_preserves_timer_bound
        (Emax := Emax) (Dmax := Dmax) (hn := hn) hp₂.1)
      (generic_processAgent_preserves_timer_bound
        (Emax := Emax) (Dmax := Dmax) (hn := hn) hp₂.2)

set_option maxHeartbeats 800000 in
private theorem generic_rankDeltaOSSR_preserves_timer_bound
    {n Rmax Emax Dmax K : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : GenericAgentTimerBounded K a) (hb : GenericAgentTimerBounded K b) :
    GenericAgentTimerBounded K (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1 ∧
    GenericAgentTimerBounded K (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2 := by
  unfold rankDeltaOSSR
  by_cases hReset : a.role = .Resetting ∨ b.role = .Resetting
  · simp [hReset]
    have hpr :=
      generic_propagateReset_preserves_timer_bound
        (Emax := Emax) (Dmax := Dmax) (hn := hn) ha hb
    split_ifs <;> simp_all [GenericAgentTimerBounded]
  · simp [hReset]
    repeat' split_ifs <;> simp_all [GenericAgentTimerBounded]

set_option maxHeartbeats 800000 in
private theorem generic_transitionPEM_prePhase4_preserves_timer_bound
    {n trank K : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hK : 7 * (trank + 4) ≤ K)
    (hRankDelta :
      GenericAgentTimerBounded K (rankDelta (s₀, s₁)).1 ∧
      GenericAgentTimerBounded K (rankDelta (s₀, s₁)).2) :
    GenericAgentTimerBounded K
        (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).1 ∧
      GenericAgentTimerBounded K
        (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).2 := by
  unfold transitionPEM_prePhase4
  rcases hrd : rankDelta (s₀, s₁) with ⟨r₀, r₁⟩
  simp [hrd] at hRankDelta ⊢
  repeat' split_ifs <;> simp_all [GenericAgentTimerBounded] <;> omega

private theorem generic_phase4_swap_preserves_timer_bound
    {n K : ℕ} {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : GenericAgentTimerBounded K a) (hb : GenericAgentTimerBounded K b) :
    GenericAgentTimerBounded K (phase4_swap a b x₀ x₁).1 ∧
    GenericAgentTimerBounded K (phase4_swap a b x₀ x₁).2 := by
  unfold phase4_swap
  split_ifs <;> simp_all [GenericAgentTimerBounded]

private theorem generic_phase4_decide_preserves_timer_bound
    {n K : ℕ} {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : GenericAgentTimerBounded K a) (hb : GenericAgentTimerBounded K b) :
    GenericAgentTimerBounded K (phase4_decide n a b x₀ x₁).1 ∧
    GenericAgentTimerBounded K (phase4_decide n a b x₀ x₁).2 := by
  unfold phase4_decide
  repeat' split_ifs <;> simp_all [GenericAgentTimerBounded]

set_option maxHeartbeats 800000 in
private theorem generic_phase4_propagate_preserves_timer_bound
    {n Rmax K : ℕ} {a b : AgentState n}
    (ha : GenericAgentTimerBounded K a) (hb : GenericAgentTimerBounded K b) :
    GenericAgentTimerBounded K (phase4_propagate n Rmax a b).1 ∧
    GenericAgentTimerBounded K (phase4_propagate n Rmax a b).2 := by
  unfold phase4_propagate
  by_cases haMed : a.rank.val + 1 = ceilHalf n
  · by_cases hbLast : b.rank.val + 1 = n
    · by_cases hReset :
        ({ a with timer := a.timer - 1 } : AgentState n).timer = 0 ∧
          ({ a with timer := a.timer - 1 } : AgentState n).answer ≠ b.answer
      · simp [haMed, hbLast, hReset, GenericAgentTimerBounded] at * <;> omega
      · simp [haMed, hbLast, hReset, GenericAgentTimerBounded] at * <;> omega
    · by_cases hReset : a.timer = 0 ∧ a.answer ≠ b.answer
      · simp [haMed, hbLast, hReset, GenericAgentTimerBounded] at * <;> omega
      · simp [haMed, hbLast, hReset, GenericAgentTimerBounded] at * <;> omega
  · by_cases hbMed : b.rank.val + 1 = ceilHalf n
    · by_cases haLast : a.rank.val + 1 = n
      · by_cases hReset :
          ({ b with timer := b.timer - 1 } : AgentState n).timer = 0 ∧
            ({ b with timer := b.timer - 1 } : AgentState n).answer ≠ a.answer
        · have hn_ne_ceil : n ≠ ceilHalf n := by
            intro h
            exact haMed (by omega)
          simp [hn_ne_ceil, hbMed, haLast, hReset, GenericAgentTimerBounded] at * <;>
            omega
        · have hn_ne_ceil : n ≠ ceilHalf n := by
            intro h
            exact haMed (by omega)
          simp [hn_ne_ceil, hbMed, haLast, hReset, GenericAgentTimerBounded] at * <;>
            omega
      · by_cases hReset : b.timer = 0 ∧ b.answer ≠ a.answer
        · simp [haMed, hbMed, haLast, hReset, GenericAgentTimerBounded] at * <;> omega
        · simp [haMed, hbMed, haLast, hReset, GenericAgentTimerBounded] at * <;> omega
    · simp [haMed, hbMed, GenericAgentTimerBounded] at * <;> omega

private theorem generic_transitionPEM_phase4_preserves_timer_bound
    {n Rmax K : ℕ} {a : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (ha : GenericAgentTimerBounded K a.1) (hb : GenericAgentTimerBounded K a.2) :
    GenericAgentTimerBounded K (transitionPEM_phase4 n Rmax a x₀ x₁).1 ∧
    GenericAgentTimerBounded K (transitionPEM_phase4 n Rmax a x₀ x₁).2 := by
  by_cases hSettled : a.1.role = .Settled ∧ a.2.role = .Settled
  · let sw := phase4_swap a.1 a.2 x₀ x₁
    have hsw : GenericAgentTimerBounded K sw.1 ∧ GenericAgentTimerBounded K sw.2 :=
      generic_phase4_swap_preserves_timer_bound (x₀ := x₀) (x₁ := x₁) ha hb
    let dec := phase4_decide n sw.1 sw.2 x₀ x₁
    have hdec : GenericAgentTimerBounded K dec.1 ∧ GenericAgentTimerBounded K dec.2 :=
      generic_phase4_decide_preserves_timer_bound (x₀ := x₀) (x₁ := x₁) hsw.1 hsw.2
    have hprop :
        GenericAgentTimerBounded K (phase4_propagate n Rmax dec.1 dec.2).1 ∧
        GenericAgentTimerBounded K (phase4_propagate n Rmax dec.1 dec.2).2 :=
      generic_phase4_propagate_preserves_timer_bound hdec.1 hdec.2
    simpa [transitionPEM_phase4, hSettled, sw, dec] using hprop
  · simpa [transitionPEM_phase4, hSettled] using And.intro ha hb

private theorem generic_transitionPEM_preserves_timer_bound
    {n trank Rmax Emax Dmax K : ℕ} {hn : 0 < n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hK : 7 * (trank + 4) ≤ K)
    (hs₀ : GenericAgentTimerBounded K s₀)
    (hs₁ : GenericAgentTimerBounded K s₁) :
      GenericAgentTimerBounded K
          ((PEMProtocol n trank Rmax Emax Dmax hn).δ ((s₀, x₀), (s₁, x₁))).1 ∧
        GenericAgentTimerBounded K
          ((PEMProtocol n trank Rmax Emax Dmax hn).δ ((s₀, x₀), (s₁, x₁))).2 := by
  have hrd :=
    generic_rankDeltaOSSR_preserves_timer_bound (hn := hn)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hs₀ hs₁
  have hpre :=
    generic_transitionPEM_prePhase4_preserves_timer_bound
      (trank := trank) (K := K) (x₀ := x₀) (x₁ := x₁) hK hrd
  simpa [PEMProtocol, protocolPEM, transitionPEM] using
    generic_transitionPEM_phase4_preserves_timer_bound
      (x₀ := x₀) (x₁ := x₁) hpre.1 hpre.2

theorem generic_timer_preservation
    {n trank Rmax Emax Dmax K : ℕ} (hn : 0 < n)
    (hK : 7 * (trank + 4) ≤ K) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig K C →
      ∀ i j : Fin n,
        IsTimerBoundedConfig K
          (C.step (PEMProtocol n trank Rmax Emax Dmax hn) i j) := by
  intro C hC i j μ
  have hi : GenericAgentTimerBounded K (C i).1 := hC i
  have hj : GenericAgentTimerBounded K (C j).1 := hC j
  by_cases hij : i = j
  · subst j
    simpa [Config.step, GenericAgentTimerBounded, IsTimerBoundedConfig] using hC μ
  · by_cases hμi : μ = i
    · subst μ
      have hpair :=
        generic_transitionPEM_preserves_timer_bound
          (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          (hn := hn) (K := K) (x₀ := (C i).2) (x₁ := (C j).2) hK hi hj
      simpa [Config.step, hij, GenericAgentTimerBounded, IsTimerBoundedConfig]
        using hpair.1
    · by_cases hμj : μ = j
      · subst μ
        have hpair :=
          generic_transitionPEM_preserves_timer_bound
            (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (hn := hn) (K := K) (x₀ := (C i).2) (x₁ := (C j).2) hK hi hj
        simpa [Config.step, hij, hμi, GenericAgentTimerBounded, IsTimerBoundedConfig]
          using hpair.2
      · simpa [Config.step, hij, hμi, hμj, GenericAgentTimerBounded, IsTimerBoundedConfig]
          using hC μ

end TimerPreservation

section CoupledTransfer

variable {n trank Rmax Emax Dmax : ℕ}

private theorem generic_transition_eq_coupled_of_settled_distinct
    (hn0 : 0 < n) {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank) :
    transitionPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        ((s₀, x₀), (s₁, x₁)) =
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        ((s₀, x₀), (s₁, x₁)) := by
  have hFix := rankDeltaOSSR_satisfies_fix
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
  simp only [transitionPEM_eq]
  rw [transitionPEM_prePhase4_eq_of_settled_distinct
      (trank := trank) hFix hs₀ hs₁ hne]
  rw [transitionPEM_prePhase4_eq_of_settled_distinct
      (trank := Rmax) hFix hs₀ hs₁ hne]

theorem generic_step_eq_coupled_of_InSrank
    (hn0 : 0 < n) {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (i j : Fin n) :
    C.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j =
      C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j := by
  funext w
  by_cases hij : i = j
  · subst j
    simp [Config.step]
  · have hsi : (C i).1.role = .Settled := hSrank.allSettled i
    have hsj : (C j).1.role = .Settled := hSrank.allSettled j
    have hne : (C i).1.rank ≠ (C j).1.rank := by
      intro h
      exact hij (hSrank.ranks_inj h)
    have hδ :=
      generic_transition_eq_coupled_of_settled_distinct
        (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (x₀ := (C i).2) (x₁ := (C j).2)
        hn0 hsi hsj hne
    by_cases hwi : w = i
    · subst w
      unfold Config.step
      simp only [PEMProtocolCoupled, PEMProtocol, hij, ↓reduceIte]
      exact congrArg (fun p => (p.1, (C i).2)) hδ
    · by_cases hwj : w = j
      · subst w
        unfold Config.step
        simp only [PEMProtocolCoupled, PEMProtocol, hij, hwi, ↓reduceIte]
        exact congrArg (fun p => (p.2, (C j).2)) hδ
      · unfold Config.step
        simp [PEMProtocolCoupled, PEMProtocol, hij, hwi, hwj]

private theorem generic_step_eq_coupled_of_not_bad
    (hn0 : 0 < n)
    {Bad : Config (AgentState n) Opinion n → Prop}
    (hBad : ∀ C : Config (AgentState n) Opinion n, ¬ Bad C → InSrank C)
    {C : Config (AgentState n) Opinion n} (hC : ¬ Bad C) (i j : Fin n) :
    C.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j =
      C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j :=
  generic_step_eq_coupled_of_InSrank
    (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn0 (hBad C hC) i j

private theorem generic_probHitBy_succ_eq_tsum_step_of_not_goal
    {Q X Y : Type*} {n : ℕ} [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal] (hGoal : ¬ Goal C₀) (t : ℕ) :
    Probability.probHitBy P hn C₀ Goal (t + 1) =
      ∑' C : Config Q X n,
        Probability.stepDist P hn C₀ C *
          Probability.probHitBy P hn C Goal t := by
  classical
  rw [Probability.probHitBy_eq_hitFlagDist_toOuterMeasure]
  rw [Probability.hitFlagDist_eq_hitFlagDistFrom]
  simp only [hGoal, decide_false]
  rw [show t + 1 = 1 + t by omega]
  rw [Probability.hitFlagDistFrom_add]
  simp only [Probability.hitFlagDistFrom, PMF.pure_bind]
  rw [Probability.hitFlagStepDist, PMF.bind_map]
  simp only [Bool.false_or]
  rw [PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro C
  simp only [Function.comp_apply]
  have hdec :
      @decide (Goal C) (Classical.propDecidable (Goal C)) =
        @decide (Goal C) (inferInstance : Decidable (Goal C)) := by
    by_cases h : Goal C <;> simp [h]
  rw [hdec]
  have hhit :
      (Probability.hitFlagDistFrom P hn Goal (C, decide (Goal C)) t).toOuterMeasure
          {T : Config Q X n × Bool | T.2 = true} =
        Probability.probHitBy P hn C Goal t := by
    rw [Probability.probHitBy_eq_hitFlagDist_toOuterMeasure,
      Probability.hitFlagDist_eq_hitFlagDistFrom P hn C Goal t]
  exact congrArg (fun x => Probability.stepDist P hn C₀ C * x) hhit

private theorem generic_ProbHitWithin_eq_of_step_eq_until
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (Bad : Config (AgentState n) Opinion n → Prop) [DecidablePred Bad]
    (hstep :
      ∀ C : Config (AgentState n) Opinion n, ¬ Bad C →
        ∀ i j : Fin n,
          C.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j =
            C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)
    (C : Config (AgentState n) Opinion n) (t : ℕ) :
    Probability.ProbHitWithin
        (PEMProtocol n trank Rmax Emax Dmax hn0) hn2 C Bad t =
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Bad t := by
  classical
  let Pg := PEMProtocol n trank Rmax Emax Dmax hn0
  let Pc := PEMProtocolCoupled n Rmax Emax Dmax hn0
  induction t generalizing C with
  | zero =>
      by_cases hC : Bad C
      · rw [Probability.ProbHitWithin, Probability.ProbHitWithin,
          Probability.probHitBy_zero_of_goal Pg hn2 C Bad hC,
          Probability.probHitBy_zero_of_goal Pc hn2 C Bad hC]
      · rw [Probability.ProbHitWithin, Probability.ProbHitWithin,
          Probability.probHitBy_zero_of_not_goal Pg hn2 C Bad hC,
          Probability.probHitBy_zero_of_not_goal Pc hn2 C Bad hC]
  | succ t ih =>
      by_cases hC : Bad C
      · have hg0 :
            Probability.ProbHitWithin Pg hn2 C Bad 0 = 1 := by
          exact Probability.probHitBy_zero_of_goal Pg hn2 C Bad hC
        have hc0 :
            Probability.ProbHitWithin Pc hn2 C Bad 0 = 1 := by
          exact Probability.probHitBy_zero_of_goal Pc hn2 C Bad hC
        have hg_le :
            (1 : ENNReal) ≤ Probability.ProbHitWithin Pg hn2 C Bad (t + 1) := by
          rw [← hg0]
          exact Probability.ProbHitWithin_mono_time Pg hn2 C Bad (Nat.zero_le _)
        have hc_le :
            (1 : ENNReal) ≤ Probability.ProbHitWithin Pc hn2 C Bad (t + 1) := by
          rw [← hc0]
          exact Probability.ProbHitWithin_mono_time Pc hn2 C Bad (Nat.zero_le _)
        have hg :
            Probability.ProbHitWithin Pg hn2 C Bad (t + 1) = 1 :=
          le_antisymm (Probability.ProbHitWithin_le_one Pg hn2 C Bad (t + 1)) hg_le
        have hc :
            Probability.ProbHitWithin Pc hn2 C Bad (t + 1) = 1 :=
          le_antisymm (Probability.ProbHitWithin_le_one Pc hn2 C Bad (t + 1)) hc_le
        rw [hg, hc]
      · have hstepDist :
            Probability.stepDist Pg hn2 C = Probability.stepDist Pc hn2 C := by
          unfold Probability.stepDist
          congr 1
          funext p
          exact hstep C hC p.1 p.2
        rw [Probability.ProbHitWithin, Probability.ProbHitWithin,
          generic_probHitBy_succ_eq_tsum_step_of_not_goal Pg hn2 C Bad hC t,
          generic_probHitBy_succ_eq_tsum_step_of_not_goal Pc hn2 C Bad hC t]
        apply tsum_congr
        intro D
        have hih := ih D
        change Probability.probHitBy Pg hn2 D Bad t =
          Probability.probHitBy Pc hn2 D Bad t at hih
        rw [hstepDist, hih]

end CoupledTransfer

section GenericStepHelpers

variable {n trank Rmax Emax Dmax : ℕ}

theorem generic_step_rank_preserved_of_InSswap
    (hn0 : 0 < n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (w : Fin n) :
    (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j w).1.rank =
      (D w).1.rank := by
  have hEq :=
    generic_step_eq_coupled_of_InSrank
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn0 hS.toInSrank i j
  rw [hEq]
  exact
    step_rank_preserved_of_InSswap
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hS w

theorem generic_step_timer_le_of_InSswap
    (hn0 : 0 < n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (w : Fin n) :
    (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j w).1.timer ≤
      (D w).1.timer := by
  have hEq :=
    generic_step_eq_coupled_of_InSrank
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn0 hS.toInSrank i j
  rw [hEq]
  exact
    step_timer_le_of_InSswap
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hS w

theorem generic_crs_of_InSswap_break_with_MedC
    [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) (hM : MedianAnswerCorrect D)
    {i j : Fin n}
    (hS' : ¬ InSswap
      (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j)) :
    CorrectResetSeed
      (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j) := by
  have hEq :=
    generic_step_eq_coupled_of_InSrank
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn0 hS.toInSrank i j
  have hBreakCoupled :
      ¬ InSswap
        (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
    intro hCoupled
    exact hS' (by simpa [hEq] using hCoupled)
  have hSeedCoupled :
      CorrectResetSeed
        (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) :=
    crs_of_InSswap_break_with_MedC
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax hS hM hBreakCoupled
  simpa [hEq] using hSeedCoupled

private theorem generic_step_InSswap_of_InSswap_of_post_InSrank
    (hn0 : 0 < n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (hRank' :
      InSrank
        (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j)) :
    InSswap
      (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j) := by
  classical
  let P := PEMProtocol n trank Rmax Emax Dmax hn0
  have hInput :
      ∀ w : Fin n, (D.step P i j w).2 = (D w).2 := by
    intro w
    exact step_input_preserved P D i j w
  have hRank :
      ∀ w : Fin n, (D.step P i j w).1.rank = (D w).1.rank := by
    intro w
    simpa [P] using
      generic_step_rank_preserved_of_InSswap
        (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn0 hS w
  have hnA : nAOf (D.step P i j) = nAOf D := by
    simpa [P, PEMProtocol] using
      (nAOf_step_eq (trank := trank) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j)
  refine { toInSrank := hRank', input_rank := ?_ }
  intro w
  constructor
  · intro hA
    have hA_old : (D w).2 = Opinion.A := by
      rw [hInput w] at hA
      exact hA
    have hlt_old : (D w).1.rank.val < nAOf D :=
      (hS.input_rank w).mp hA_old
    rw [hRank w, hnA]
    exact hlt_old
  · intro hlt
    have hlt_old : (D w).1.rank.val < nAOf D := by
      rw [hRank w, hnA] at hlt
      exact hlt
    have hA_old : (D w).2 = Opinion.A :=
      (hS.input_rank w).mpr hlt_old
    rw [hInput w]
    exact hA_old

end GenericStepHelpers

section GenericExitWindow

variable {n trank Rmax Emax Dmax : ℕ}

theorem generic_PEM_srank_or_timer_failure_prob_le_quarter_short35
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast 35 C) :
    Probability.ProbHitWithin
      (PEMProtocol n trank Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D)
      (4 * n * (n - 1)) ≤ ((4 : ENNReal)⁻¹) := by
  classical
  let Bad : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D
  have hstep :
      ∀ D : Config (AgentState n) Opinion n, ¬ Bad D →
        ∀ i j : Fin n,
          D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j =
            D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j := by
    intro D hD i j
    have hRank : InSrank D := by
      by_contra hNot
      exact hD (Or.inl hNot)
    exact
      generic_step_eq_coupled_of_InSrank
        (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn0 hRank i j
  have hn2 : 2 ≤ n := by omega
  have hEq :=
    generic_ProbHitWithin_eq_of_step_eq_until
      (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 Bad hstep C (4 * n * (n - 1))
  have hCoupled :
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        hn2 C Bad (4 * n * (n - 1)) ≤ ((4 : ENNReal)⁻¹) := by
    simpa [Bad] using
      (PEM_srank_or_timer_failure_prob_le_quarter_short35
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hn0 hRmax hEmax hDmax C hSrank hTimer)
  simpa [Bad] using (le_of_eq_of_le hEq hCoupled)

end GenericExitWindow

private theorem generic_card_Fin_filter_val_lt {n k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
  classical
  let toFin : Fin k → Fin n := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
  have hinj : Function.Injective toFin := by
    intro i j h
    have : i.val = j.val := congrArg (fun x : Fin n => x.val) h
    exact Fin.ext this
  have himg : (Finset.univ : Finset (Fin k)).image toFin
            = Finset.univ.filter (fun i : Fin n => i.val < k) := by
    ext i
    rw [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨j, _, hfj⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      have : (toFin j).val = i.val := congrArg Fin.val hfj
      have hj : j.val < k := j.isLt
      exact this ▸ hj
    · rintro ⟨_, hi⟩
      refine ⟨⟨i.val, hi⟩, Finset.mem_univ _, ?_⟩
      apply Fin.eq_of_val_eq
      rfl
  rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]

private theorem generic_card_filter_rank_lt {C : Config (AgentState n) Opinion n}
    (hRank : InSrank C) {k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter (fun u : Fin n => (C u).1.rank.val < k)).card = k := by
  classical
  have hinj : Function.Injective (fun u : Fin n => (C u).1.rank) := hRank.ranks_inj
  have hsurj : Function.Surjective (fun u : Fin n => (C u).1.rank) :=
    Finite.injective_iff_surjective.mp hinj
  have himg : (Finset.univ.filter (fun u : Fin n => (C u).1.rank.val < k)).image
                (fun u => (C u).1.rank)
            = Finset.univ.filter (fun i : Fin n => i.val < k) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hi
      obtain ⟨u, hu⟩ := hsurj i
      refine ⟨u, ?_, hu⟩
      rw [show (C u).1.rank.val = i.val from congrArg Fin.val hu]
      exact hi
  rw [← Finset.card_image_of_injective _ hinj, himg, generic_card_Fin_filter_val_lt hk]

section DecisionWindow

variable {n trank Rmax Emax Dmax : ℕ}

theorem generic_PEM_even_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
    (hn2 : 2 ≤ n) (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hpar : n % 2 = 0)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocol n trank Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 := by
  classical
  let P := PEMProtocol n trank Rmax Emax Dmax hn0
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
    obtain ⟨h_u, _h_v, _h_others, _h_inputs⟩ :=
      step_at_median_pair_even_disagreed_inputs
        (trank := trank) (Rmax := Rmax)
        hRankFix huv hsu hsv hpar hu_med hv_upper h_disagree h_no_swap hn4
    have hSwap' : InSswap (C.step P u v) := by
      have hdec := decision_step_at_median_pair_even_tie_decreases
        (n := n) (trank := trank) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        hRankFix hC huv hpar hu_med hv_upper h_disagree hTie hn4 h_wrong
      simpa [P, PEMProtocol] using hdec.1
    have hmaj : majorityAnswer (C.step P u v) = majorityAnswer C := by
      simpa [P, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := trank) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C u v)
    have h_u_correct : (C.step P u v u).1.answer = majorityAnswer (C.step P u v) := by
      have h_outT : majorityAnswer C = .outT := majorityAnswer_eq_outT_of_tie hTie
      have hu_state : (C.step P u v u).1 = {(C u).1 with answer := .outT} := by
        simpa [P, PEMProtocol] using h_u
      rw [hmaj, h_outT, hu_state]
    have h_u_med' : (C.step P u v u).1.rank.val + 1 = ceilHalf n := by
      have hu_state : (C.step P u v u).1 = {(C u).1 with answer := .outT} := by
        simpa [P, PEMProtocol] using h_u
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
      (n := n) (trank := trank) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      hRankFix huv hsu hsv hpar hu_med hv_upper h_agree hn4
    have hSwap' : InSswap (C.step P u v) := by
      have hdec := decision_step_at_median_pair_even_decreases
        (n := n) (trank := trank) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        hRankFix hC huv hpar hu_med hv_upper h_agree hTie hn4 h_wrong
      simpa [P, PEMProtocol] using hdec.1
    have hmaj : majorityAnswer (C.step P u v) = majorityAnswer C := by
      simpa [P, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := trank) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C u v)
    have h_correct : opinionToAnswer (C u).2 = majorityAnswer C :=
      opinionToAnswer_lower_median_eq_majorityAnswer_even hC hu_med hpar hTie
    have h_u_correct : (C.step P u v u).1.answer = majorityAnswer (C.step P u v) := by
      rw [hmaj]
      have hval := congrFun hC'_eq u
      rw [show (C.step P u v u) =
          (if u = u then ({(C u).1 with answer := opinionToAnswer (C u).2}, (C u).2)
            else if u = v then ({(C v).1 with answer := opinionToAnswer (C u).2}, (C v).2)
            else C u) by simpa [P, PEMProtocol] using hval]
      simp [h_correct]
    have h_u_med' : (C.step P u v u).1.rank.val + 1 = ceilHalf n := by
      have hval := congrFun hC'_eq u
      rw [show (C.step P u v u) =
          (if u = u then ({(C u).1 with answer := opinionToAnswer (C u).2}, (C u).2)
            else if u = v then ({(C v).1 with answer := opinionToAnswer (C u).2}, (C v).2)
            else C u) by simpa [P, PEMProtocol] using hval]
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

theorem generic_PEM_odd_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ : Fin n}
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : 1 ≤ (C μ).1.timer)
    (h_μ_wrong : (C μ).1.answer ≠ majorityAnswer C) :
    (((ceilHalf n - 1 : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocol n trank Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 := by
  classical
  let P := PEMProtocol n trank Rmax Emax Dmax hn0
  let lowerSet : Finset (Fin n) :=
    Finset.univ.filter fun v : Fin n => (C v).1.rank.val < (C μ).1.rank.val
  let S : Finset (Fin n × Fin n) := lowerSet.image fun v => (μ, v)
  have hμ_rank : (C μ).1.rank.val = ceilHalf n - 1 := by omega
  have hcardLower : lowerSet.card = ceilHalf n - 1 := by
    have hk : (C μ).1.rank.val ≤ n := Nat.le_of_lt (C μ).1.rank.isLt
    have hcard := generic_card_filter_rank_lt hC.toInSrank (k := (C μ).1.rank.val) hk
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
      InSswap (C.step P p.1 p.2) ∧ MedianAnswerCorrect (C.step P p.1 p.2) := by
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
    have hSwap' : InSswap (C.step P μ v) := by
      simpa [P, PEMProtocol] using
        (step_at_median_no_swap_odd_preserves_InSswap
          (n := n) (trank := trank) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
          hRankFix hC hμv hpar hμ_med hv_no_med hv_no_max
          h_rank_gt h_timer)
    have hC'_eq :
        C.step P μ v =
          fun w =>
            if w = μ then
              ({(C μ).1 with answer := opinionToAnswer (C μ).2}, (C μ).2)
            else if w = v then
              ((C v).1, (C v).2)
            else C w := by
      simpa [P, PEMProtocol] using
        (step_at_median_no_swap_odd_v_not_max
          (n := n) (trank := trank) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
          hRankFix hμv (hC.allSettled μ) (hC.allSettled v) hpar
          hμ_med hv_no_med hv_no_max h_rank_gt h_timer)
    have hmaj :
        majorityAnswer (C.step P μ v) = majorityAnswer C := by
      simpa [P, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := trank) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C μ v)
    have hμ_correct :
        (C.step P μ v μ).1.answer = majorityAnswer (C.step P μ v) := by
      rw [hmaj, hC'_eq]
      simp [opinionToAnswer_median_eq_majorityAnswer_odd hC hμ_med hpar]
    have hμ_med' :
        (C.step P μ v μ).1.rank.val + 1 = ceilHalf n := by
      rw [hC'_eq]
      simp [hμ_med]
    refine ⟨hSwap', ?_⟩
    intro η hη
    have hημ : η = μ := by
      apply hSwap'.ranks_inj
      apply Fin.eq_of_val_eq
      have hη_med' :
          (C.step P μ v η).1.rank.val + 1 = ceilHalf n := by
        simpa using hη
      have hηval :
          (C.step P μ v η).1.rank.val = ceilHalf n - 1 := by omega
      have hμval :
          (C.step P μ v μ).1.rank.val = ceilHalf n - 1 := by omega
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
    _ ≤ Probability.ProbHitWithin P hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 :=
          Probability.ProbHitWithin_one_lower_bound_of_pairSet
            P hn2 C
            (fun D => InSswap D ∧ MedianAnswerCorrect D)
            (by
              intro hGoal
              exact h_μ_wrong (hGoal.2 μ hμ_med))
            S hS_sub hstep

theorem generic_PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
    (hn2 : 2 ≤ n) (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocol n trank Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 := by
  by_cases hpar : n % 2 = 0
  · exact generic_PEM_even_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC hpar h_med_wrong
  · obtain ⟨μ, hμ_med, hμ_wrong⟩ := h_med_wrong
    have hodd :=
      generic_PEM_odd_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
        (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
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
          (PEMProtocol n trank Rmax Emax Dmax hn0) hn2 C
          (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 := hodd

theorem generic_PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le
    (hn2 : 2 ≤ n) (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (h_not_dec : ¬ MedianAnswerCorrect C) :
    Probability.expectedHittingTime
      (PEMProtocol n trank Rmax Emax Dmax hn0) hn2 C
      (fun D =>
        (InSswap D ∧ MedianAnswerCorrect D) ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)) ≤
      (((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ := by
  classical
  let P := PEMProtocol n trank Rmax Emax Dmax hn0
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
        (generic_PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
          (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
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

theorem generic_decision_window
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n) (hC : InSswap C)
    (hT : MedianTimerAtLeast 1 C) (hND : ¬ MedianAnswerCorrect C) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocol n trank Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => (InSswap D ∧ MedianAnswerCorrect D) ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * (n * (n - 1))) := by
  have hM := generic_PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le
    (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (by omega : 2 ≤ n) hn0 hn4 hC hT hND
  rw [inv_inv] at hM
  exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
    (PEMProtocol n trank Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C _ hM (by omega)

end DecisionWindow

end SSEM
