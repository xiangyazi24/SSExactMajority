import SSExactMajority.UpperBound.Time.Composition

namespace SSEM

open scoped ENNReal

/-! ### ProbHitWithin-chain composition (brainstorm Round 3 design)

This alternative composition uses `ProbHitWithin_add_ge_mul` (proved!) instead
of `probReached_add_ge_mul`. Each phase only needs a ProbHitWithin lower
bound (not probReached), bypassing the non-absorbing joint-event problem.

Structure: 3 phases with ProbHitWithin ≥ 1/2 each (from Markov on E[T]):
- Phase A: any config → InSrank (ranking)
- Phase B: InSrank → InSswap (swap)
- Phase C: InSswap → IsConsensusConfig (decision+propagation)

Product: (1/2)³ = 1/8 ≥ 1/4096000 = pemTable2SuccessProb. -/

theorem PEM_consensus_ProbHitWithin_from_phases
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hPhaseA : ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin
            (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C InSrank (2 * Rmax * n * n))
    (hPhaseB : ∀ C : Config (AgentState n) Opinion n, InSrank C →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin
            (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C InSswap (4 * n * n))
    (hPhaseC : ∀ C : Config (AgentState n) Opinion n, InSswap C →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin
            (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n)) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ((8 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin
            (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C IsConsensusConfig
              ((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n) := by
  classical
  intro C hTimerBd
  set P := PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n) with hP_def
  have hn2 : 2 ≤ n := by omega
  -- Chain A → B → C via ProbHitWithin_add_ge_mul
  have hAB : ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C InSswap
        (2 * Rmax * n * n + 4 * n * n) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C InSrank InSswap
      (2 * Rmax * n * n) (4 * n * n)
      ((2 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹)
      (hPhaseA C hTimerBd) (fun D hD => hPhaseB D hD)
  have hABC : ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C IsConsensusConfig
        ((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C InSswap IsConsensusConfig
      (2 * Rmax * n * n + 4 * n * n) (20 * Rmax * n * n)
      (((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹)) ((2 : ENNReal)⁻¹)
      hAB (fun D hD => hPhaseC D hD)
  calc ((8 : ENNReal)⁻¹)
      = ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) := by
        have h8 : ((8 : ENNReal)⁻¹) ≠ ⊤ := by
          rw [ENNReal.inv_ne_top]
          norm_num
        have h2 : ((2 : ENNReal)⁻¹) ≠ ⊤ := by
          rw [ENNReal.inv_ne_top]
          norm_num
        have hprod : (((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
            ((2 : ENNReal)⁻¹)) ≠ ⊤ := by
          exact ENNReal.mul_ne_top (ENNReal.mul_ne_top h2 h2) h2
        rw [← ENNReal.toReal_eq_toReal_iff' h8 hprod]
        simp [ENNReal.toReal_inv, ENNReal.toReal_mul]
        norm_num
    _ ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig
          ((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n) := hABC

/-! ### End-to-end expected parallel time (phase-bound interface)

The pipeline below is the `ProbHitWithin` composition interface.  It keeps
the two phase expected-time estimates as explicit hypotheses rather than
pretending the remaining paper-level probabilistic arguments have already
been formalized:

1. Prove 3 expected hitting time bounds (Phases A, B, C)
2. PEM_consensus_ProbHitWithin_from_expected_phases → ProbHitWithin ≥ 1/8
3. pem_table2_window_to_expectedParallelTime → E[T_parallel] ≤ O(Rmax·n) -/

private theorem real_sum_range_inv_sq_le_two (m : ℕ) :
    (∑ k ∈ Finset.range m, ((((k : ℝ) + 1) ^ 2)⁻¹)) ≤ 2 := by
  classical
  have hseries := (sum_Ioo_inv_sq_le (α := ℝ) 0 (m + 1))
  have hset :
      (Finset.range m).image (fun k : ℕ => k + 1) =
        Finset.Ioo 0 (m + 1) := by
    ext i
    simp [Finset.mem_Ioo]
    constructor
    · intro h
      omega
    · intro h
      refine ⟨i - 1, by omega, by omega⟩
  have hsum :
      (∑ k ∈ Finset.range m, ((((k : ℝ) + 1) ^ 2)⁻¹)) =
        ∑ i ∈ Finset.Ioo 0 (m + 1), (((i : ℝ) ^ 2)⁻¹) := by
    rw [← hset]
    rw [Finset.sum_image]
    · simp [Nat.cast_add]
    · intro a _ b _ h
      exact Nat.succ.inj h
  calc
    (∑ k ∈ Finset.range m, ((((k : ℝ) + 1) ^ 2)⁻¹))
        = ∑ i ∈ Finset.Ioo 0 (m + 1), (((i : ℝ) ^ 2)⁻¹) := hsum
    _ ≤ 2 / ((0 : ℝ) + 1) := by simpa using hseries
    _ = 2 := by norm_num

private theorem ennreal_sum_inv_sq_le_two_mul_pred {n : ℕ} (hn2 : 2 ≤ n) (m : ℕ) :
    ∑ k ∈ Finset.range m,
      ((((k + 1) * (k + 1) : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ ≤
      ((2 * n * (n - 1) : ℕ) : ENNReal) := by
  classical
  have hterm_ne_top : ∀ k ∈ Finset.range m,
      ((((k + 1) * (k + 1) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ ≠ ⊤ := by
    intro k _hk
    rw [ENNReal.inv_ne_top]
    exact ne_of_gt (ENNReal.mul_pos
      (by
        exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero k) (Nat.succ_ne_zero k))
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)))
  have hleft_ne_top :
      ∑ k ∈ Finset.range m,
        ((((k + 1) * (k + 1) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ ≠ ⊤ :=
    ENNReal.sum_ne_top.2 hterm_ne_top
  have hright_ne_top : ((2 * n * (n - 1) : ℕ) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [← ENNReal.toReal_le_toReal hleft_ne_top hright_ne_top]
  rw [ENNReal.toReal_sum hterm_ne_top]
  have hsum := real_sum_range_inv_sq_le_two m
  have hterm_real : ∀ k ∈ Finset.range m,
      ENNReal.toReal
        (((((k + 1) * (k + 1) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹) =
        (((n * (n - 1) : ℕ) : ℝ) * ((((k : ℝ) + 1) ^ 2)⁻¹)) := by
    intro k _hk
    let A : ENNReal := (((k + 1) * (k + 1) : ℕ) : ENNReal)
    let B : ENNReal := ((n * (n - 1) : ℕ) : ENNReal)
    have hA0 : A ≠ 0 := by
      dsimp [A]
      exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero k) (Nat.succ_ne_zero k)
    have hAtop : A ≠ ⊤ := by
      dsimp [A]
      exact ENNReal.natCast_ne_top _
    change ENNReal.toReal ((A * B⁻¹)⁻¹) =
      (((n * (n - 1) : ℕ) : ℝ) * ((((k : ℝ) + 1) ^ 2)⁻¹))
    rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAtop), inv_inv]
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
    have hAreal : A.toReal = (((k : ℝ) + 1) ^ 2) := by
      have hnat : A.toReal = (((k + 1) * (k + 1) : ℕ) : ℝ) := by
        dsimp [A]
        exact ENNReal.toReal_natCast _
      rw [hnat]
      norm_num [pow_two, Nat.cast_mul, Nat.cast_add]
    have hBreal : B.toReal = ((n * (n - 1) : ℕ) : ℝ) := by
      dsimp [B]
      exact ENNReal.toReal_natCast _
    rw [hAreal, hBreal]
    ring
  calc
    (∑ k ∈ Finset.range m,
        ENNReal.toReal
          (((((k + 1) * (k + 1) : ℕ) : ENNReal) *
            ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹))
        = ∑ k ∈ Finset.range m, (((n * (n - 1) : ℕ) : ℝ) *
            ((((k : ℝ) + 1) ^ 2)⁻¹)) := by
          apply Finset.sum_congr rfl
          exact hterm_real
    _ = ((n * (n - 1) : ℕ) : ℝ) *
        (∑ k ∈ Finset.range m, ((((k : ℝ) + 1) ^ 2)⁻¹)) := by
          rw [Finset.mul_sum]
    _ ≤ ((n * (n - 1) : ℕ) : ℝ) * 2 := by
          gcongr
    _ = ENNReal.toReal ((2 * n * (n - 1) : ℕ) : ENNReal) := by
          rw [ENNReal.toReal_natCast]
          norm_num [pow_two, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm]

theorem PEM_swap_ProbHitWithin_or_exit_short
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (_hRmax : n ≤ Rmax) (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => InSswap D ∨ ¬ InSrank D) (4 * n * (n - 1)) := by
  have hSum := PEM_swap_phase_expected_until_swap_or_exit_le_sum
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (by omega : 2 ≤ n) hn0 hSrank
  have hBound : ∑ k ∈ Finset.range (wrongLowBCount C),
      ((((k + 1) * (k + 1) : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ ≤
      ((2 * n * (n - 1) : ℕ) : ENNReal) :=
    ennreal_sum_inv_sq_le_two_mul_pred (by omega : 2 ≤ n) (wrongLowBCount C)
  have hE : Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C
      (fun D => InSswap D ∨ ¬ InSrank D) ≤
        ((2 * n * (n - 1) : ℕ) : ENNReal) :=
    hSum.trans hBound
  have hW : 2 * (2 * n * (n - 1)) ≤ (4 * n * (n - 1)) + 1 := by
    calc
      2 * (2 * n * (n - 1)) = 4 * n * (n - 1) := by ring
      _ ≤ 4 * n * (n - 1) + 1 := Nat.le_succ _
  exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C
    (fun D => InSswap D ∨ ¬ InSrank D) hE hW

theorem PEM_swap_ProbHitWithin_or_exit
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => InSswap D ∨ ¬ InSrank D) (4 * n * n) := by
  have hshort :=
    PEM_swap_ProbHitWithin_or_exit_short
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax hEmax hDmax C hSrank
  exact hshort.trans
    (Probability.ProbHitWithin_mono_time
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C
      (fun D => InSswap D ∨ ¬ InSrank D)
      (by
        calc
          4 * n * (n - 1) ≤ 4 * n * n := by
            exact Nat.mul_le_mul_left (4 * n) (Nat.sub_le n 1)
          _ ≤ 4 * n * n := le_rfl))

noncomputable def srankMedianMaxEvent (C : Config (AgentState n) Opinion n)
    (i j : Fin n) : Bool :=
  by
    classical
    exact decide
      (InSrank C ∧
      (((C i).1.rank.val + 1 = ceilHalf n ∧
          (C j).1.rank.val + 1 = n) ∨
        ((C j).1.rank.val + 1 = ceilHalf n ∧
          (C i).1.rank.val + 1 = n)))

private theorem srankMedianMaxEvent_eq_true_iff
    {n : ℕ} {C : Config (AgentState n) Opinion n} {i j : Fin n} :
    srankMedianMaxEvent C i j = true ↔
      InSrank C ∧
        (((C i).1.rank.val + 1 = ceilHalf n ∧
            (C j).1.rank.val + 1 = n) ∨
          ((C j).1.rank.val + 1 = ceilHalf n ∧
            (C i).1.rank.val + 1 = n)) := by
  classical
  rw [srankMedianMaxEvent]
  constructor
  · intro h
    exact of_decide_eq_true h
  · intro h
    exact decide_eq_true h

private theorem srankMedianMaxEvent_eq_false_of_not_rank
    {n : ℕ} {C : Config (AgentState n) Opinion n} {i j : Fin n}
    (h : ¬ InSrank C) :
    srankMedianMaxEvent C i j = false := by
  classical
  rw [Bool.eq_false_iff]
  intro ht
  exact h (srankMedianMaxEvent_eq_true_iff.mp ht).1

private theorem srankMedianMaxEvent_mass_le
    {n : ℕ} (hn2 : 2 ≤ n)
    (C : Config (AgentState n) Opinion n) :
    (Probability.uniformPair n hn2).toOuterMeasure
        {p : Fin n × Fin n |
          srankMedianMaxEvent C p.1 p.2 = true} ≤
      (2 : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
  classical
  let S : Finset (Fin n × Fin n) :=
    (Probability.OffDiagonalPairs n).filter
      (fun p : Fin n × Fin n => srankMedianMaxEvent C p.1 p.2 = true)
  have hmass :
      Probability.pairSetMass n hn2 S =
        (Probability.uniformPair n hn2).toOuterMeasure
          {p : Fin n × Fin n |
            srankMedianMaxEvent C p.1 p.2 = true} := by
    simpa [S] using
      (Probability.pairSetMass_filter_offDiagonal_eq_toOuterMeasure
        n hn2
        (fun p : Fin n × Fin n =>
          srankMedianMaxEvent C p.1 p.2 = true))
  rw [← hmass]
  rw [Probability.pairSetMass_eq_card_mul_inv_of_subset]
  · gcongr
    by_cases hRank : InSrank C
    · let medRank : Fin n :=
        ⟨ceilHalf n - 1, by unfold ceilHalf; omega⟩
      let maxRank : Fin n :=
        ⟨n - 1, by omega⟩
      have hsurj : Function.Surjective (fun u : Fin n => (C u).1.rank) :=
        Finite.injective_iff_surjective.mp hRank.ranks_inj
      obtain ⟨μ, hμ⟩ := hsurj medRank
      obtain ⟨v, hv⟩ := hsurj maxRank
      let T : Finset (Fin n × Fin n) := {(μ, v), (v, μ)}
      have hsub : S ⊆ T := by
        intro p hp
        have hpEvent : srankMedianMaxEvent C p.1 p.2 = true :=
          (Finset.mem_filter.mp hp).2
        rw [srankMedianMaxEvent] at hpEvent
        have hpProp :
            InSrank C ∧
              (((C p.1).1.rank.val + 1 = ceilHalf n ∧
                  (C p.2).1.rank.val + 1 = n) ∨
                ((C p.2).1.rank.val + 1 = ceilHalf n ∧
                  (C p.1).1.rank.val + 1 = n)) := by
          simpa using (of_decide_eq_true hpEvent)
        rcases hpProp.2 with hdir | hdir
        · have hp1 : p.1 = μ := by
            apply hRank.ranks_inj
            apply Fin.ext
            have hvalμ : (C μ).1.rank.val = ceilHalf n - 1 := by
              change (C μ).1.rank.val = medRank.val
              exact congrArg Fin.val hμ
            have hpval : (C p.1).1.rank.val = ceilHalf n - 1 := by
              omega
            rw [hpval, hvalμ]
          have hp2 : p.2 = v := by
            apply hRank.ranks_inj
            apply Fin.ext
            have hvalv : (C v).1.rank.val = n - 1 := by
              change (C v).1.rank.val = maxRank.val
              exact congrArg Fin.val hv
            have hpval : (C p.2).1.rank.val = n - 1 := by
              omega
            rw [hpval, hvalv]
          cases hp1
          cases hp2
          simp [T]
        · have hp1 : p.1 = v := by
            apply hRank.ranks_inj
            apply Fin.ext
            have hvalv : (C v).1.rank.val = n - 1 := by
              change (C v).1.rank.val = maxRank.val
              exact congrArg Fin.val hv
            have hpval : (C p.1).1.rank.val = n - 1 := by
              omega
            rw [hpval, hvalv]
          have hp2 : p.2 = μ := by
            apply hRank.ranks_inj
            apply Fin.ext
            have hvalμ : (C μ).1.rank.val = ceilHalf n - 1 := by
              change (C μ).1.rank.val = medRank.val
              exact congrArg Fin.val hμ
            have hpval : (C p.2).1.rank.val = ceilHalf n - 1 := by
              omega
            rw [hpval, hvalμ]
          cases hp1
          cases hp2
          simp [T]
      have hcardT : T.card ≤ 2 := by
        calc
          T.card ≤ ({(v, μ)} : Finset (Fin n × Fin n)).card + 1 := by
            simpa [T] using
              (Finset.card_insert_le (μ, v) ({(v, μ)} : Finset (Fin n × Fin n)))
          _ ≤ 2 := by
            have hsingle :
                ({(v, μ)} : Finset (Fin n × Fin n)).card ≤ 1 := by
              simpa using
                (Finset.card_insert_le (v, μ) (∅ : Finset (Fin n × Fin n)))
            omega
      exact_mod_cast (Finset.card_le_card hsub).trans hcardT
    · have hEmpty : S = ∅ := by
        ext p
        constructor
        · intro hp
          have hpEvent : srankMedianMaxEvent C p.1 p.2 = true :=
            (Finset.mem_filter.mp hp).2
          rw [srankMedianMaxEvent] at hpEvent
          have hpProp :
              InSrank C ∧
                (((C p.1).1.rank.val + 1 = ceilHalf n ∧
                    (C p.2).1.rank.val + 1 = n) ∨
                  ((C p.2).1.rank.val + 1 = ceilHalf n ∧
                    (C p.1).1.rank.val + 1 = n)) := by
            simpa using (of_decide_eq_true hpEvent)
          exact False.elim (hRank hpProp.1)
        · intro hp
          simp at hp
      rw [hEmpty]
      simp
  · intro p hp
    exact (Finset.mem_filter.mp hp).1

private theorem srankMedianMaxEvent_count_tail_le
    {n Rmax Emax Dmax : ℕ}
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n) (t K : ℕ) [NeZero K] :
    (Probability.eventCountDist
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        hn2 C (@srankMedianMaxEvent n) t).toOuterMeasure
      {S : Config (AgentState n) Opinion n × ℕ | K ≤ S.2} ≤
      (t : ENNReal) *
        ((2 : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹) /
          (K : ENNReal) := by
  exact
    Probability.eventCountDist_expected_le
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (hn := hn2) (C₀ := C) (Event := @srankMedianMaxEvent n)
      (eventProb := (2 : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
      (K := K)
      (hProb := by
        intro D
        exact srankMedianMaxEvent_mass_le hn2 D)
      (t := t)

private theorem srankMedianMaxEvent_count_tail_le_quarter
    {n Rmax Emax Dmax : ℕ}
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n) :
    (Probability.eventCountDist
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C (@srankMedianMaxEvent n) (4 * n * n)).toOuterMeasure
      {S : Config (AgentState n) Opinion n × ℕ | 12 * n ≤ S.2} ≤
      ((4 : ENNReal)⁻¹) := by
  classical
  have hn2 : 2 ≤ n := by omega
  haveI : NeZero (12 * n) := ⟨by omega⟩
  have htail :=
    srankMedianMaxEvent_count_tail_le
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 C (t := 4 * n * n) (K := 12 * n)
  refine htail.trans ?_
  let A : ENNReal :=
    ((4 * n * n : ℕ) : ENNReal) *
      ((2 : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹) /
      ((12 * n : ℕ) : ENNReal)
  have hA_ne_top : A ≠ ⊤ := by
    dsimp [A]
    rw [div_eq_mul_inv]
    refine ENNReal.mul_ne_top ?_ ?_
    · refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_
      refine ENNReal.mul_ne_top (by norm_num) ?_
      rw [ENNReal.inv_ne_top]
      exact_mod_cast (Nat.mul_ne_zero (by omega : n ≠ 0) (by omega : n - 1 ≠ 0))
    · rw [ENNReal.inv_ne_top]
      exact_mod_cast (Nat.mul_ne_zero (by norm_num : (12 : ℕ) ≠ 0) (by omega : n ≠ 0))
  have hquarter_ne_top : ((4 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  change A ≤ (4 : ENNReal)⁻¹
  rw [← ENNReal.toReal_le_toReal hA_ne_top hquarter_ne_top]
  dsimp [A]
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Nat.cast_mul, Nat.cast_ofNat]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnm1R : (0 : ℝ) < (n - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < n - 1)
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  have hn4R : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hdenpos : (0 : ℝ) < n - 1 := by nlinarith
  field_simp [hnR.ne', hdenpos.ne']
  ring_nf
  have hpos : (0 : ℝ) < -1 + n := by nlinarith
  have hge : (3 : ℝ) ≤ -1 + n := by nlinarith
  have hinv : (-1 + (n : ℝ))⁻¹ ≤ (3 : ℝ)⁻¹ :=
    (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 3)).2 hge
  have hupper : (32 : ℝ) * (-1 + (n : ℝ))⁻¹ ≤ 32 * (3 : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_left hinv (by norm_num)
  have hlt : (32 : ℝ) * (3 : ℝ)⁻¹ < 12 := by norm_num
  have hconst₁ : ENNReal.toReal 12 = (12 : ℝ) := by norm_num
  have hconst₂ : ENNReal.toReal 4 ^ 2 * ENNReal.toReal 2 = (32 : ℝ) := by norm_num
  nlinarith

private theorem srankMedianMaxEvent_count_tail_le_quarter_short35
    {n Rmax Emax Dmax : ℕ}
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n) :
    (Probability.eventCountDist
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C (@srankMedianMaxEvent n)
        (4 * n * (n - 1))).toOuterMeasure
      {S : Config (AgentState n) Opinion n × ℕ | 35 ≤ S.2} ≤
      ((4 : ENNReal)⁻¹) := by
  classical
  have hn2 : 2 ≤ n := by omega
  haveI : NeZero 35 := ⟨by norm_num⟩
  have htail :=
    srankMedianMaxEvent_count_tail_le
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 C (t := 4 * n * (n - 1)) (K := 35)
  refine htail.trans ?_
  let A : ENNReal :=
    ((4 * n * (n - 1) : ℕ) : ENNReal) *
      ((2 : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹) /
      ((35 : ℕ) : ENNReal)
  have hA_ne_top : A ≠ ⊤ := by
    dsimp [A]
    rw [div_eq_mul_inv]
    refine ENNReal.mul_ne_top ?_ ?_
    · refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_
      refine ENNReal.mul_ne_top (by norm_num) ?_
      rw [ENNReal.inv_ne_top]
      exact_mod_cast
        (Nat.mul_ne_zero (by omega : n ≠ 0) (by omega : n - 1 ≠ 0))
    · rw [ENNReal.inv_ne_top]
      norm_num
  have hquarter_ne_top : ((4 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  change A ≤ (4 : ENNReal)⁻¹
  rw [← ENNReal.toReal_le_toReal hA_ne_top hquarter_ne_top]
  dsimp [A]
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Nat.cast_mul, Nat.cast_ofNat]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  have hdenpos : (0 : ℝ) < n - 1 := by
    have hn4R : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    nlinarith
  field_simp [hnR.ne', hdenpos.ne']
  ring_nf
  norm_num

set_option maxHeartbeats 8000000 in
private theorem step_at_median_max_no_swap_odd_explicit_preserves_InSrank
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn : 2 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hpar : ¬ n % 2 = 0)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : 2 ≤ (C μ).1.timer) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) μ v) := by
  set P := protocolPEM n trank Rmax rankDelta
  have hsu : (C μ).1.role = .Settled := hC.allSettled μ
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hsu hsv
      (by
        intro h
        have := congrArg Fin.val h
        unfold ceilHalf at hμ_med
        omega)
  have hv_not_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    have hlt : ceilHalf n < n := by
      unfold ceilHalf
      omega
    omega
  have hvμ : v ≠ μ := Ne.symm hμv
  have hN_ne_ceil : ¬ (n = ceilHalf n) := by
    unfold ceilHalf
    omega
  have htr :
      transitionPEM n trank Rmax rankDelta (C μ, C v) =
        ({ (C μ).1 with
            answer := opinionToAnswer (C μ).2,
            timer := (C μ).1.timer - 1 },
         (C v).1) := by
    unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
      phase4_swap phase4_decide phase4_propagate
    simp only [hRD, hsu, hsv, ne_eq,
      role_settled_ne_resetting,
      not_true_eq_false, not_false_eq_true,
      false_and, and_false, if_false,
      and_self, if_true, h_no_swap, hpar, hμ_med, hv_not_med, hv_max,
      hN_ne_ceil]
    split_ifs with h
    · exfalso
      obtain ⟨hzero, _⟩ := h
      omega
    · rfl
  have h_rank : (C.step P μ v μ).1.rank = (C μ).1.rank := by
    unfold Config.step
    simp only [P, if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.rank = _
    rw [htr]
  have h_role : (C.step P μ v μ).1.role = (C μ).1.role := by
    unfold Config.step
    simp only [P, if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.role = _
    rw [htr]
  have h_v : (C.step P μ v v).1 = (C v).1 := by
    unfold Config.step
    rw [if_neg hμv, if_neg hvμ, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).2 = _
    rw [htr]
  have h_others : ∀ w : Fin n, w ≠ μ → w ≠ v → C.step P μ v w = C w := by
    intro w hwμ hwv
    unfold Config.step
    simp only [P, if_neg hμv, if_neg hwμ, if_neg hwv]
  refine { allSettled := ?_, ranks_inj := ?_ }
  · intro w
    by_cases hwμ : w = μ
    · subst w
      rw [h_role]
      exact hC.allSettled μ
    · by_cases hwv : w = v
      · subst w
        rw [show (C.step P μ v v).1.role = (C v).1.role from
          congrArg (fun s => s.role) h_v]
        exact hC.allSettled v
      · rw [show C.step P μ v w = C w from h_others w hwμ hwv]
        exact hC.allSettled w
  · have h_rank_w : ∀ w : Fin n, (C.step P μ v w).1.rank = (C w).1.rank := by
      intro w
      by_cases hwμ : w = μ
      · subst w
        exact h_rank
      · by_cases hwv : w = v
        · subst w
          exact congrArg (fun s => s.rank) h_v
        · rw [show C.step P μ v w = C w from h_others w hwμ hwv]
    intro w₁ w₂ hw
    apply hC.ranks_inj
    calc
      (C w₁).1.rank = (C.step P μ v w₁).1.rank := (h_rank_w w₁).symm
      _ = (C.step P μ v w₂).1.rank := hw
      _ = (C w₂).1.rank := h_rank_w w₂

set_option maxHeartbeats 8000000 in
private theorem step_at_max_median_no_swap_odd_explicit_preserves_InSrank
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn : 2 ≤ n)
    {v μ : Fin n} (hvμ : v ≠ μ)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hpar : ¬ n % 2 = 0)
    (h_no_swap :
      ¬ ((C v).1.rank < (C μ).1.rank ∧
        (C v).2 = Opinion.B ∧ (C μ).2 = Opinion.A))
    (h_timer : 2 ≤ (C μ).1.timer) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) v μ) := by
  set P := protocolPEM n trank Rmax rankDelta
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hsμ : (C μ).1.role = .Settled := hC.allSettled μ
  have hRD : rankDelta ((C v).1, (C μ).1) = ((C v).1, (C μ).1) :=
    hRank (C v).1 (C μ).1 hsv hsμ
      (by
        intro h
        have := congrArg Fin.val h
        unfold ceilHalf at hμ_med
        omega)
  have hv_not_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    have hlt : ceilHalf n < n := by
      unfold ceilHalf
      omega
    omega
  have hμv : μ ≠ v := Ne.symm hvμ
  have hN_ne_ceil : ¬ (n = ceilHalf n) := by
    unfold ceilHalf
    omega
  have htr :
      transitionPEM n trank Rmax rankDelta (C v, C μ) =
        ((C v).1,
         { (C μ).1 with
            answer := opinionToAnswer (C μ).2,
            timer := (C μ).1.timer - 1 }) := by
    unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
      phase4_swap phase4_decide phase4_propagate
    simp only [hRD, hsv, hsμ, ne_eq,
      role_settled_ne_resetting,
      not_true_eq_false, not_false_eq_true,
      false_and, and_false, if_false,
      and_self, if_true, h_no_swap, hpar, hμ_med, hv_not_med, hv_max,
      hN_ne_ceil]
    split_ifs with h
    · exfalso
      obtain ⟨hzero, _⟩ := h
      omega
    · rfl
  have h_v : (C.step P v μ v).1 = (C v).1 := by
    unfold Config.step
    simp only [P, if_neg hvμ, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C v, C μ)).1 = _
    rw [htr]
  have h_rank : (C.step P v μ μ).1.rank = (C μ).1.rank := by
    unfold Config.step
    rw [if_neg hvμ, if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C v, C μ)).2.rank = _
    rw [htr]
  have h_role : (C.step P v μ μ).1.role = (C μ).1.role := by
    unfold Config.step
    rw [if_neg hvμ, if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C v, C μ)).2.role = _
    rw [htr]
  have h_others : ∀ w : Fin n, w ≠ v → w ≠ μ → C.step P v μ w = C w := by
    intro w hwv hwμ
    unfold Config.step
    simp only [P, if_neg hvμ, if_neg hwv, if_neg hwμ]
  refine { allSettled := ?_, ranks_inj := ?_ }
  · intro w
    by_cases hwv : w = v
    · subst w
      rw [show (C.step P v μ v).1.role = (C v).1.role from
        congrArg (fun s => s.role) h_v]
      exact hC.allSettled v
    · by_cases hwμ : w = μ
      · subst w
        rw [h_role]
        exact hC.allSettled μ
      · rw [show C.step P v μ w = C w from h_others w hwv hwμ]
        exact hC.allSettled w
  · have h_rank_w : ∀ w : Fin n, (C.step P v μ w).1.rank = (C w).1.rank := by
      intro w
      by_cases hwv : w = v
      · subst w
        exact congrArg (fun s => s.rank) h_v
      · by_cases hwμ : w = μ
        · subst w
          exact h_rank
        · rw [show C.step P v μ w = C w from h_others w hwv hwμ]
    intro w₁ w₂ hw
    apply hC.ranks_inj
    calc
      (C w₁).1.rank = (C.step P v μ w₁).1.rank := (h_rank_w w₁).symm
      _ = (C.step P v μ w₂).1.rank := hw
      _ = (C w₂).1.rank := h_rank_w w₂

set_option maxHeartbeats 8000000 in
private theorem step_at_even_lower_max_timer_ge_two_preserves_InSrank
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : 2 ≤ (C μ).1.timer) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) μ v) := by
  set P := protocolPEM n trank Rmax rankDelta
  have hμ_settled : (C μ).1.role = .Settled := hC.allSettled μ
  have hv_settled : (C v).1.role = .Settled := hC.allSettled v
  have h_rank_ne : (C μ).1.rank ≠ (C v).1.rank := by
    intro hEq
    exact hμv (hC.ranks_inj hEq)
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hμ_settled hv_settled h_rank_ne
  have hceil : ceilHalf n = n / 2 := by
    unfold ceilHalf
    omega
  have hμ_ceil : (C μ).1.rank.val + 1 = ceilHalf n := by
    rw [hceil]
    exact hμ_lower
  have hv_not_ceil : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    rw [hceil]
    omega
  have hv_not_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1 := by
    omega
  have hN_ne_ceil : ¬ n = ceilHalf n := by
    unfold ceilHalf
    omega
  have h_dec1a :
      ¬ ((C μ).1.rank.val + 1 = n / 2 ∧ (C v).1.rank.val = n / 2) := by
    intro h
    exact hv_not_upper (by omega)
  have h_dec2a :
      ¬ ((C v).1.rank.val + 1 = n / 2 ∧ (C μ).1.rank.val = n / 2) := by
    intro h
    omega
  have h_no_reset :
      ¬ ((C μ).1.timer - 1 = 0 ∧
        ({ (C μ).1 with timer := (C μ).1.timer - 1 } : AgentState n).answer
          ≠ (C v).1.answer) := by
    rintro ⟨hzero, _⟩
    omega
  have hswap :
      phase4_swap (C μ).1 (C v).1 (C μ).2 (C v).2 = ((C μ).1, (C v).1) := by
    unfold phase4_swap
    simp [h_no_swap]
  have hdec :
      phase4_decide n (C μ).1 (C v).1 (C μ).2 (C v).2 = ((C μ).1, (C v).1) := by
    unfold phase4_decide
    simp [hpar, h_dec1a, h_dec2a]
  have hprop :
      phase4_propagate n Rmax (C μ).1 (C v).1 =
        ({ (C μ).1 with timer := (C μ).1.timer - 1 }, (C v).1) := by
    unfold phase4_propagate
    simp [hμ_ceil, hv_max, h_timer, h_no_reset]
  have htr :
      transitionPEM n trank Rmax rankDelta (C μ, C v) =
        ({ (C μ).1 with timer := (C μ).1.timer - 1 }, (C v).1) := by
    unfold transitionPEM transitionPEM_prePhase4 transitionPEM_phase4
    simp [hRD, hμ_settled, hv_settled, role_settled_ne_resetting,
      hswap, hdec, hprop]
  have hvμ : v ≠ μ := Ne.symm hμv
  have h_rank : (C.step P μ v μ).1.rank = (C μ).1.rank := by
    unfold Config.step
    simp only [P, if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.rank = _
    rw [htr]
  have h_role : (C.step P μ v μ).1.role = (C μ).1.role := by
    unfold Config.step
    simp only [P, if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.role = _
    rw [htr]
  have h_v : (C.step P μ v v).1 = (C v).1 := by
    unfold Config.step
    rw [if_neg hμv, if_neg hvμ, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).2 = _
    rw [htr]
  have h_others : ∀ w : Fin n, w ≠ μ → w ≠ v → C.step P μ v w = C w := by
    intro w hwμ hwv
    unfold Config.step
    simp only [P, if_neg hμv, if_neg hwμ, if_neg hwv]
  refine { allSettled := ?_, ranks_inj := ?_ }
  · intro w
    by_cases hwμ : w = μ
    · subst w
      rw [h_role]
      exact hC.allSettled μ
    · by_cases hwv : w = v
      · subst w
        rw [show (C.step P μ v v).1.role = (C v).1.role from
          congrArg (fun s => s.role) h_v]
        exact hC.allSettled v
      · rw [show C.step P μ v w = C w from h_others w hwμ hwv]
        exact hC.allSettled w
  · have h_rank_w : ∀ w : Fin n, (C.step P μ v w).1.rank = (C w).1.rank := by
      intro w
      by_cases hwμ : w = μ
      · subst w
        exact h_rank
      · by_cases hwv : w = v
        · subst w
          exact congrArg (fun s => s.rank) h_v
        · rw [show C.step P μ v w = C w from h_others w hwμ hwv]
    intro w₁ w₂ hw
    apply hC.ranks_inj
    calc
      (C w₁).1.rank = (C.step P μ v w₁).1.rank := (h_rank_w w₁).symm
      _ = (C.step P μ v w₂).1.rank := hw
      _ = (C w₂).1.rank := h_rank_w w₂

set_option maxHeartbeats 8000000 in
private theorem step_at_even_max_lower_timer_ge_two_preserves_InSrank
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {v μ : Fin n} (hvμ : v ≠ μ)
    (hpar : n % 2 = 0)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (h_no_swap :
      ¬ ((C v).1.rank < (C μ).1.rank ∧
        (C v).2 = Opinion.B ∧ (C μ).2 = Opinion.A))
    (h_timer : 2 ≤ (C μ).1.timer) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) v μ) := by
  set P := protocolPEM n trank Rmax rankDelta
  have hv_settled : (C v).1.role = .Settled := hC.allSettled v
  have hμ_settled : (C μ).1.role = .Settled := hC.allSettled μ
  have h_rank_ne : (C v).1.rank ≠ (C μ).1.rank := by
    intro hEq
    exact hvμ (hC.ranks_inj hEq)
  have hRD : rankDelta ((C v).1, (C μ).1) = ((C v).1, (C μ).1) :=
    hRank (C v).1 (C μ).1 hv_settled hμ_settled h_rank_ne
  have hceil : ceilHalf n = n / 2 := by
    unfold ceilHalf
    omega
  have hμ_ceil : (C μ).1.rank.val + 1 = ceilHalf n := by
    rw [hceil]
    exact hμ_lower
  have hv_not_ceil : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    rw [hceil]
    omega
  have hv_not_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1 := by
    omega
  have hN_ne_ceil : ¬ n = ceilHalf n := by
    unfold ceilHalf
    omega
  have h_dec1a :
      ¬ ((C v).1.rank.val + 1 = n / 2 ∧ (C μ).1.rank.val = n / 2) := by
    intro h
    omega
  have h_dec2a :
      ¬ ((C μ).1.rank.val + 1 = n / 2 ∧ (C v).1.rank.val = n / 2) := by
    intro h
    exact hv_not_upper (by omega)
  have h_no_reset :
      ¬ ((C μ).1.timer - 1 = 0 ∧
        ({ (C μ).1 with timer := (C μ).1.timer - 1 } : AgentState n).answer
          ≠ (C v).1.answer) := by
    rintro ⟨hzero, _⟩
    omega
  have hswap :
      phase4_swap (C v).1 (C μ).1 (C v).2 (C μ).2 = ((C v).1, (C μ).1) := by
    unfold phase4_swap
    simp [h_no_swap]
  have hdec :
      phase4_decide n (C v).1 (C μ).1 (C v).2 (C μ).2 = ((C v).1, (C μ).1) := by
    unfold phase4_decide
    simp [hpar, h_dec1a, h_dec2a]
  have hprop :
      phase4_propagate n Rmax (C v).1 (C μ).1 =
        ((C v).1, { (C μ).1 with timer := (C μ).1.timer - 1 }) := by
    unfold phase4_propagate
    simp [hv_not_ceil, hμ_ceil, hv_max, hN_ne_ceil, h_timer, h_no_reset]
  have htr :
      transitionPEM n trank Rmax rankDelta (C v, C μ) =
        ((C v).1, { (C μ).1 with timer := (C μ).1.timer - 1 }) := by
    unfold transitionPEM transitionPEM_prePhase4 transitionPEM_phase4
    simp [hRD, hv_settled, hμ_settled, role_settled_ne_resetting,
      hswap, hdec, hprop]
  have hμv : μ ≠ v := Ne.symm hvμ
  have h_v : (C.step P v μ v).1 = (C v).1 := by
    unfold Config.step
    simp only [P, if_neg hvμ, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C v, C μ)).1 = _
    rw [htr]
  have h_rank : (C.step P v μ μ).1.rank = (C μ).1.rank := by
    unfold Config.step
    rw [if_neg hvμ, if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C v, C μ)).2.rank = _
    rw [htr]
  have h_role : (C.step P v μ μ).1.role = (C μ).1.role := by
    unfold Config.step
    rw [if_neg hvμ, if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C v, C μ)).2.role = _
    rw [htr]
  have h_others : ∀ w : Fin n, w ≠ v → w ≠ μ → C.step P v μ w = C w := by
    intro w hwv hwμ
    unfold Config.step
    simp only [P, if_neg hvμ, if_neg hwv, if_neg hwμ]
  refine { allSettled := ?_, ranks_inj := ?_ }
  · intro w
    by_cases hwv : w = v
    · subst w
      rw [show (C.step P v μ v).1.role = (C v).1.role from
        congrArg (fun s => s.role) h_v]
      exact hC.allSettled v
    · by_cases hwμ : w = μ
      · subst w
        rw [h_role]
        exact hC.allSettled μ
      · rw [show C.step P v μ w = C w from h_others w hwv hwμ]
        exact hC.allSettled w
  · have h_rank_w : ∀ w : Fin n, (C.step P v μ w).1.rank = (C w).1.rank := by
      intro w
      by_cases hwv : w = v
      · subst w
        exact congrArg (fun s => s.rank) h_v
      · by_cases hwμ : w = μ
        · subst w
          exact h_rank
        · rw [show C.step P v μ w = C w from h_others w hwv hwμ]
    intro w₁ w₂ hw
    apply hC.ranks_inj
    calc
      (C w₁).1.rank = (C.step P v μ w₁).1.rank := (h_rank_w w₁).symm
      _ = (C.step P v μ w₂).1.rank := hw
      _ = (C w₂).1.rank := h_rank_w w₂

private theorem misordered_pair_8way_case_of_timer_count_safe
    {n K : ℕ} {C : Config (AgentState n) Opinion n}
    (hn4 : 4 ≤ n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast K C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hKpos : 0 < K)
    (hEventSafe : srankMedianMaxEvent C u v = true → 1 < K) :
      ((C u).1.rank.val + 1 ≠ ceilHalf n ∧
        (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
      (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
        (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer) ∨
      (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer) ∨
      (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
        (C v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
      (¬ n % 2 = 0 ∧ (C v).1.rank.val + 1 = ceilHalf n ∧
        1 ≤ (C v).1.timer) ∨
      (n % 2 = 0 ∧ (C v).1.rank.val + 1 = n / 2 ∧
        1 ≤ (C v).1.timer ∧ 4 ≤ n) ∨
      (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
        (C v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (C v).1.rank.val + 1 ≠ n ∧
        1 ≤ (C u).1.timer ∧ 4 ≤ n) ∨
      (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer ∧ 4 ≤ n) := by
  classical
  obtain ⟨_huB, _hvA, hlt⟩ := hMis
  by_cases hpar : n % 2 = 0
  · have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
    by_cases hu_med : (C u).1.rank.val + 1 = ceilHalf n
    · have hu_med' : (C u).1.rank.val + 1 = n / 2 := by
        rw [← hceil]; exact hu_med
      have hu_timer1 : 1 ≤ (C u).1.timer :=
        le_trans (Nat.succ_le_of_lt hKpos) (hTimer u hu_med)
      by_cases hv_upper : (C v).1.rank.val + 1 = n / 2 + 1
      · right; right; right; left
        exact ⟨hpar, hu_med', hv_upper, hn4⟩
      · by_cases hv_max : (C v).1.rank.val + 1 = n
        · have hevent : srankMedianMaxEvent C u v = true := by
            rw [srankMedianMaxEvent]
            exact decide_eq_true
              ⟨hSrank, Or.inl ⟨hu_med, hv_max⟩⟩
          have hu_timer2 : 2 ≤ (C u).1.timer :=
            le_trans (hEventSafe hevent) (hTimer u hu_med)
          right; right; right; right; right; right; right
          exact ⟨hpar, hu_med', hv_max, hu_timer2, hn4⟩
        · right; right; right; right; right; right; left
          exact ⟨hpar, hu_med', hv_upper, hv_max, hu_timer1, hn4⟩
    · by_cases hv_med : (C v).1.rank.val + 1 = ceilHalf n
      · have hv_med' : (C v).1.rank.val + 1 = n / 2 := by
          rw [← hceil]; exact hv_med
        have hv_timer1 : 1 ≤ (C v).1.timer :=
          le_trans (Nat.succ_le_of_lt hKpos) (hTimer v hv_med)
        right; right; right; right; right; left
        exact ⟨hpar, hv_med', hv_timer1, hn4⟩
      · left
        exact ⟨hu_med, hv_med⟩
  · by_cases hu_med : (C u).1.rank.val + 1 = ceilHalf n
    · have hu_timer1 : 1 ≤ (C u).1.timer :=
        le_trans (Nat.succ_le_of_lt hKpos) (hTimer u hu_med)
      by_cases hv_max : (C v).1.rank.val + 1 = n
      · have hevent : srankMedianMaxEvent C u v = true := by
          rw [srankMedianMaxEvent]
          exact decide_eq_true
            ⟨hSrank, Or.inl ⟨hu_med, hv_max⟩⟩
        have hu_timer2 : 2 ≤ (C u).1.timer :=
          le_trans (hEventSafe hevent) (hTimer u hu_med)
        right; right; left
        exact ⟨hpar, hu_med, hv_max, hu_timer2⟩
      · right; left
        exact ⟨hpar, hu_med, hv_max, hu_timer1⟩
    · by_cases hv_med : (C v).1.rank.val + 1 = ceilHalf n
      · have hv_timer1 : 1 ≤ (C v).1.timer :=
          le_trans (Nat.succ_le_of_lt hKpos) (hTimer v hv_med)
        right; right; right; right; left
        exact ⟨hpar, hv_med, hv_timer1⟩
      · left
        exact ⟨hu_med, hv_med⟩

private theorem step_at_misordered_non_median_preserves_timer_geK
    {n trank Rmax K : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hu_no_med : (C u).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hTimer : MedianTimerAtLeast K C) :
    MedianTimerAtLeast K (C.step (protocolPEM n trank Rmax rankDelta) u v) := by
  classical
  obtain ⟨hu_state, hv_state, hother_state, _⟩ :=
    step_at_misordered_non_median (trank := trank) (Rmax := Rmax)
      hRank hC hMis hu_no_med hv_no_med
  intro μ hμ_med
  by_cases hμu : μ = u
  · subst μ
    rw [hu_state] at hμ_med ⊢
    exact (hv_no_med hμ_med).elim
  · by_cases hμv : μ = v
    · subst μ
      rw [hv_state] at hμ_med ⊢
      exact (hu_no_med hμ_med).elim
    · rw [hother_state μ hμu hμv] at hμ_med ⊢
      exact hTimer μ hμ_med

private theorem step_at_v_max_misorder_preserves_timer_geK_sub_one
    {n trank Rmax K : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hv_max : (C v).1.rank.val + 1 = n)
    (hTimer : MedianTimerAtLeast K C) :
    MedianTimerAtLeast (K - 1)
      (C.step (protocolPEM n trank Rmax rankDelta) u v) := by
  classical
  have huv : u ≠ v := by
    intro h
    rw [h] at hMis
    exact absurd hMis.2.2 (lt_irrefl _)
  have h_no_max_u : (C u).1.rank.val + 1 ≠ n :=
    fun h => absurd hMis (not_misordered_fst_at_max_rank h)
  have hRankSwap :=
    transitionPEM_rank_swap_at_misorder (trank := trank) (Rmax := Rmax)
      hRank hC hMis
  have hTimerV :=
    transitionPEM_timer_of_v_max_at_misorder (trank := trank) (Rmax := Rmax)
      hRank hC hMis h_no_max_u hv_max hn4
  set P := protocolPEM n trank Rmax rankDelta
  intro μ hμ_med
  by_cases hμu : μ = u
  · subst μ
    have hstep := Config.step_fst_state P C huv
    have h_u_rank_eq : (C.step P u v u).1.rank.val = (C v).1.rank.val := by
      have h := congrArg (fun s => s.rank) hstep
      simp only [P, protocolPEM, hRankSwap.1] at h
      exact congrArg Fin.val h
    exfalso
    rw [h_u_rank_eq, hv_max] at hμ_med
    unfold ceilHalf at hμ_med
    omega
  · by_cases hμv : μ = v
    · subst μ
      have hstep := Config.step_snd_state P C huv huv.symm
      have h_v_rank_eq : (C.step P u v v).1.rank.val = (C u).1.rank.val := by
        have h := congrArg (fun s => s.rank) hstep
        simp only [P, protocolPEM, hRankSwap.2] at h
        exact congrArg Fin.val h
      have hpre_med : (C u).1.rank.val + 1 = ceilHalf n := by
        rw [h_v_rank_eq] at hμ_med
        exact hμ_med
      have hstep_timer :
          (C.step P u v v).1.timer =
            (transitionPEM n trank Rmax rankDelta (C u, C v)).2.timer := by
        have h := congrArg (fun s => s.timer) hstep
        simpa [P, protocolPEM] using h
      rw [hstep_timer]
      exact le_trans (Nat.sub_le_sub_right (hTimer u hpre_med) 1) hTimerV
    · unfold Config.step at hμ_med ⊢
      simp only [P, if_neg huv, if_neg hμu, if_neg hμv] at hμ_med ⊢
      exact le_trans (Nat.sub_le K 1) (hTimer μ hμ_med)

private lemma phase4_propagate_median_timer_lower_of_no_reset
    {n Rmax L : ℕ} {b₀ b₁ : AgentState n}
    (hceil_lt : ceilHalf n < n)
    (hnz₀ : b₀.rank.val + 1 = ceilHalf n →
      (if b₁.rank.val + 1 = n then b₀.timer - 1 else b₀.timer) ≠ 0)
    (hnz₁ : b₁.rank.val + 1 = ceilHalf n →
      (if b₀.rank.val + 1 = n then b₁.timer - 1 else b₁.timer) ≠ 0)
    (hle₀ : b₀.rank.val + 1 = ceilHalf n →
      L ≤ if b₁.rank.val + 1 = n then b₀.timer - 1 else b₀.timer)
    (hle₁ : b₁.rank.val + 1 = ceilHalf n →
      L ≤ if b₀.rank.val + 1 = n then b₁.timer - 1 else b₁.timer) :
    ((phase4_propagate n Rmax b₀ b₁).1.rank.val + 1 = ceilHalf n →
        L ≤ (phase4_propagate n Rmax b₀ b₁).1.timer) ∧
      ((phase4_propagate n Rmax b₀ b₁).2.rank.val + 1 = ceilHalf n →
        L ≤ (phase4_propagate n Rmax b₀ b₁).2.timer) := by
  classical
  unfold phase4_propagate
  by_cases hmed₀ : b₀.rank.val + 1 = ceilHalf n
  · simp [hmed₀]
    by_cases hmax₁ : b₁.rank.val + 1 = n
    · simp [hmax₁]
      have hnz : b₀.timer - 1 ≠ 0 := by simpa [hmax₁] using hnz₀ hmed₀
      have hle : L ≤ b₀.timer - 1 := by simpa [hmax₁] using hle₀ hmed₀
      by_cases hreset : b₀.timer - 1 = 0 ∧
          ({ b₀ with timer := b₀.timer - 1 } : AgentState n).answer ≠ b₁.answer
      · exact False.elim (hnz hreset.1)
      · simp [hreset]
        constructor
        · intro _; exact hle
        · intro h
          have hmax₀ : ¬ b₀.rank.val + 1 = n := by
            intro hmax
            omega
          simpa [hmax₀] using hle₁ h
    · simp [hmax₁]
      have hnz : b₀.timer ≠ 0 := by simpa [hmax₁] using hnz₀ hmed₀
      have hle : L ≤ b₀.timer := by simpa [hmax₁] using hle₀ hmed₀
      by_cases hreset : b₀.timer = 0 ∧ b₀.answer ≠ b₁.answer
      · exact False.elim (hnz hreset.1)
      · simp [hreset]
        constructor
        · intro _; exact hle
        · intro h
          have hmax₀ : ¬ b₀.rank.val + 1 = n := by
            intro hmax
            omega
          simpa [hmax₀] using hle₁ h
  · simp [hmed₀]
    by_cases hmed₁ : b₁.rank.val + 1 = ceilHalf n
    · simp [hmed₁]
      by_cases hmax₀ : b₀.rank.val + 1 = n
      · simp [hmax₀]
        have hnz : b₁.timer - 1 ≠ 0 := by simpa [hmax₀] using hnz₁ hmed₁
        have hle : L ≤ b₁.timer - 1 := by simpa [hmax₀] using hle₁ hmed₁
        by_cases hreset : b₁.timer - 1 = 0 ∧
            ({ b₁ with timer := b₁.timer - 1 } : AgentState n).answer ≠ b₀.answer
        · exact False.elim (hnz hreset.1)
        · simp [hreset]
          constructor
          · intro h
            have hmax₁ : ¬ b₁.rank.val + 1 = n := by
              intro hmax
              omega
            simpa [hmax₁] using hle₀ h
          · intro _; exact hle
      · simp [hmax₀]
        have hnz : b₁.timer ≠ 0 := by simpa [hmax₀] using hnz₁ hmed₁
        have hle : L ≤ b₁.timer := by simpa [hmax₀] using hle₁ hmed₁
        by_cases hreset : b₁.timer = 0 ∧ b₁.answer ≠ b₀.answer
        · exact False.elim (hnz hreset.1)
        · simp [hreset]
          constructor
          · intro h
            have hmax₁ : ¬ b₁.rank.val + 1 = n := by
              intro hmax
              omega
            simpa [hmax₁] using hle₀ h
          · intro _; exact hle
    · simp [hmed₁]
      exact fun h => False.elim (hmed₀ h)

set_option maxHeartbeats 8000000 in
private theorem PEM_exit_step_preserves_srank_timer_count
    {n Rmax Emax Dmax K : ℕ}
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast K C)
    {i j : Fin n} (hij : i ≠ j)
    (hKpos : 0 < K)
    (hEventSafe : srankMedianMaxEvent C i j = true → 1 < K) :
    let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
    let C' := C.step P i j
    InSrank C' ∧
      MedianTimerAtLeast
        (K - if srankMedianMaxEvent C i j then 1 else 0) C' := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hRankFix : RankDeltaSettledFix (rankDeltaOSSR Rmax Emax Dmax hn0) :=
    rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn0)
  by_cases hswap :
      (C i).1.rank < (C j).1.rank ∧ (C i).2 = Opinion.B ∧ (C j).2 = Opinion.A
  · have hMis : MisorderedPair C (i, j) :=
      ⟨hswap.2.1, hswap.2.2, hswap.1⟩
    have hcase :=
      misordered_pair_8way_case_of_timer_count_safe
        (K := K) hn4 hSrank hTimer hMis hKpos hEventSafe
    have hSrank' : InSrank (C.step P i j) := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        (swap_step_decreases_eight_way
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
          hRankFix hSrank hMis hcase).1
    refine ⟨hSrank', ?_⟩
    by_cases hi_med : (C i).1.rank.val + 1 = ceilHalf n
    · by_cases hj_max : (C j).1.rank.val + 1 = n
      · have hevent : srankMedianMaxEvent C i j = true := by
          rw [srankMedianMaxEvent]
          exact decide_eq_true ⟨hSrank, Or.inl ⟨hi_med, hj_max⟩⟩
        have hTimer' :
            MedianTimerAtLeast (K - 1) (C.step P i j) := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using
            (step_at_v_max_misorder_preserves_timer_geK_sub_one
              (trank := Rmax) (Rmax := Rmax)
              (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
              hRankFix hSrank hn4 hMis hj_max hTimer)
        simpa [hevent] using hTimer'
      · have hi_no_max : (C i).1.rank.val + 1 ≠ n := by
          intro hmax
          unfold ceilHalf at hi_med
          omega
        have hTimer' :
            MedianTimerAtLeast K (C.step P i j) := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using
            (step_at_misorder_preserves_timer_geK
              (trank := Rmax) (Rmax := Rmax)
              hRankFix hSrank hMis hi_no_max hj_max hTimer)
        have hevent : srankMedianMaxEvent C i j = false := by
          rw [srankMedianMaxEvent]
          apply decide_eq_false
          rintro ⟨_, hleft | hright⟩
          · exact hj_max hleft.2
          · exact hi_no_max hright.2
        simpa [hevent] using hTimer'
    · by_cases hj_med : (C j).1.rank.val + 1 = ceilHalf n
      · have hj_no_max : (C j).1.rank.val + 1 ≠ n := by
          intro hmax
          unfold ceilHalf at hj_med
          omega
        have hi_no_max : (C i).1.rank.val + 1 ≠ n := by
          intro hmax
          have hlt : (C i).1.rank.val < (C j).1.rank.val := hswap.1
          unfold ceilHalf at hj_med
          omega
        have hTimer' :
            MedianTimerAtLeast K (C.step P i j) := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using
            (step_at_misorder_preserves_timer_geK
              (trank := Rmax) (Rmax := Rmax)
              hRankFix hSrank hMis hi_no_max hj_no_max hTimer)
        have hevent : srankMedianMaxEvent C i j = false := by
          rw [srankMedianMaxEvent]
          apply decide_eq_false
          rintro ⟨_, hleft | hright⟩
          · exact hi_med hleft.1
          · exact hi_no_max hright.2
        simpa [hevent] using hTimer'
      · have hTimer' :
            MedianTimerAtLeast K (C.step P i j) := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using
            (step_at_misordered_non_median_preserves_timer_geK
              (trank := Rmax) (Rmax := Rmax)
              (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
              hRankFix hSrank hMis hi_med hj_med hTimer)
        have hevent : srankMedianMaxEvent C i j = false := by
          rw [srankMedianMaxEvent]
          apply decide_eq_false
          rintro ⟨_, hleft | hright⟩
          · exact hi_med hleft.1
          · exact hj_med hright.1
        simpa [hevent] using hTimer'
  · have hceil_lt : ceilHalf n < n := by
      unfold ceilHalf
      omega
    have hsu : (C i).1.role = .Settled := hSrank.allSettled i
    have hsv : (C j).1.role = .Settled := hSrank.allSettled j
    have hne_rank : (C i).1.rank ≠ (C j).1.rank := by
      intro h
      exact hij (hSrank.ranks_inj h)
    have hRD :
        rankDeltaOSSR Rmax Emax Dmax hn0 ((C i).1, (C j).1) =
          ((C i).1, (C j).1) :=
      hRankFix (C i).1 (C j).1 hsu hsv hne_rank
    let q := phase4_decide n (C i).1 (C j).1 (C i).2 (C j).2
    have hdec := phase4_decide_preserves_role_rank_children
      (n := n) (b₀ := (C i).1) (b₁ := (C j).1)
      (x₀ := (C i).2) (x₁ := (C j).2)
    have hdt := phase4_decide_preserves_timer
      (n := n) (b₀ := (C i).1) (b₁ := (C j).1)
      (x₀ := (C i).2) (x₁ := (C j).2)
    have hq₁_role : q.1.role = .Settled := by
      simpa [q] using hdec.1.trans hsu
    have hq₂_role : q.2.role = .Settled := by
      simpa [q] using hdec.2.2.2.1.trans hsv
    have hq₁_rank : q.1.rank = (C i).1.rank := by
      simpa [q] using hdec.2.1
    have hq₂_rank : q.2.rank = (C j).1.rank := by
      simpa [q] using hdec.2.2.2.2.1
    have hq₁_timer : q.1.timer = (C i).1.timer := by
      simpa [q] using hdt.1
    have hq₂_timer : q.2.timer = (C j).1.timer := by
      simpa [q] using hdt.2
    have htrans :
        transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (C i, C j) =
          phase4_propagate n Rmax q.1 q.2 := by
      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
      simp [hRD, hsu, hsv, role_settled_ne_resetting,
        phase4_swap_eq_of_not_swap hswap, q]
    let L := K - if srankMedianMaxEvent C i j then 1 else 0
    have hnz₀ : q.1.rank.val + 1 = ceilHalf n →
        (if q.2.rank.val + 1 = n then q.1.timer - 1 else q.1.timer) ≠ 0 := by
      intro hqmed
      have hi_med : (C i).1.rank.val + 1 = ceilHalf n := by
        rwa [hq₁_rank] at hqmed
      by_cases hqmax : q.2.rank.val + 1 = n
      · have hj_max : (C j).1.rank.val + 1 = n := by
          rwa [hq₂_rank] at hqmax
        have hevent : srankMedianMaxEvent C i j = true := by
          rw [srankMedianMaxEvent]
          exact decide_eq_true ⟨hSrank, Or.inl ⟨hi_med, hj_max⟩⟩
        have hKi := hEventSafe hevent
        have hti := hTimer i hi_med
        simp [hqmax, hq₁_timer]
        omega
      · have hti := hTimer i hi_med
        simp [hqmax, hq₁_timer]
        omega
    have hnz₁ : q.2.rank.val + 1 = ceilHalf n →
        (if q.1.rank.val + 1 = n then q.2.timer - 1 else q.2.timer) ≠ 0 := by
      intro hqmed
      have hj_med : (C j).1.rank.val + 1 = ceilHalf n := by
        rwa [hq₂_rank] at hqmed
      by_cases hqmax : q.1.rank.val + 1 = n
      · have hi_max : (C i).1.rank.val + 1 = n := by
          rwa [hq₁_rank] at hqmax
        have hevent : srankMedianMaxEvent C i j = true := by
          rw [srankMedianMaxEvent]
          exact decide_eq_true ⟨hSrank, Or.inr ⟨hj_med, hi_max⟩⟩
        have hKj := hEventSafe hevent
        have htj := hTimer j hj_med
        simp [hqmax, hq₂_timer]
        omega
      · have htj := hTimer j hj_med
        simp [hqmax, hq₂_timer]
        omega
    have hle₀ : q.1.rank.val + 1 = ceilHalf n →
        L ≤ if q.2.rank.val + 1 = n then q.1.timer - 1 else q.1.timer := by
      intro hqmed
      have hi_med : (C i).1.rank.val + 1 = ceilHalf n := by
        rwa [hq₁_rank] at hqmed
      by_cases hqmax : q.2.rank.val + 1 = n
      · have hj_max : (C j).1.rank.val + 1 = n := by
          rwa [hq₂_rank] at hqmax
        have hevent : srankMedianMaxEvent C i j = true := by
          rw [srankMedianMaxEvent]
          exact decide_eq_true ⟨hSrank, Or.inl ⟨hi_med, hj_max⟩⟩
        have hti := hTimer i hi_med
        simp [L, hqmax, hevent, hq₁_timer]
        omega
      · have hi_not_max : (C i).1.rank.val + 1 ≠ n := by
          intro hmax
          omega
        have hevent : srankMedianMaxEvent C i j = false := by
          rw [srankMedianMaxEvent]
          apply decide_eq_false
          rintro ⟨_, hleft | hright⟩
          · exact hqmax (by simpa [hq₂_rank] using hleft.2)
          · exact hi_not_max hright.2
        have hti := hTimer i hi_med
        simp [L, hqmax, hevent, hq₁_timer]
        exact hti
    have hle₁ : q.2.rank.val + 1 = ceilHalf n →
        L ≤ if q.1.rank.val + 1 = n then q.2.timer - 1 else q.2.timer := by
      intro hqmed
      have hj_med : (C j).1.rank.val + 1 = ceilHalf n := by
        rwa [hq₂_rank] at hqmed
      by_cases hqmax : q.1.rank.val + 1 = n
      · have hi_max : (C i).1.rank.val + 1 = n := by
          rwa [hq₁_rank] at hqmax
        have hevent : srankMedianMaxEvent C i j = true := by
          rw [srankMedianMaxEvent]
          exact decide_eq_true ⟨hSrank, Or.inr ⟨hj_med, hi_max⟩⟩
        have htj := hTimer j hj_med
        simp [L, hqmax, hevent, hq₂_timer]
        omega
      · have hj_not_max : (C j).1.rank.val + 1 ≠ n := by
          intro hmax
          omega
        have hevent : srankMedianMaxEvent C i j = false := by
          rw [srankMedianMaxEvent]
          apply decide_eq_false
          rintro ⟨_, hleft | hright⟩
          · exact hj_not_max hleft.2
          · exact hqmax (by simpa [hq₁_rank] using hright.2)
        have htj := hTimer j hj_med
        simp [L, hqmax, hevent, hq₂_timer]
        exact htj
    have hroles :=
      phase4_propagate_settled_of_positive_median_timers
        (n := n) (Rmax := Rmax) (b₀ := q.1) (b₁ := q.2)
        hq₁_role hq₂_role hnz₀ hnz₁
    have hprop := phase4_propagate_preserves_rank_children
      (n := n) (Rmax := Rmax) (b₀ := q.1) (b₁ := q.2)
    have hlower :=
      phase4_propagate_median_timer_lower_of_no_reset
        (n := n) (Rmax := Rmax) (L := L) (b₀ := q.1) (b₁ := q.2)
        hceil_lt hnz₀ hnz₁ hle₀ hle₁
    have hδ_rank₁ :
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
          (C i, C j)).1.rank = (C i).1.rank := by
      rw [htrans, hprop.1, hq₁_rank]
    have hδ_rank₂ :
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
          (C i, C j)).2.rank = (C j).1.rank := by
      rw [htrans, hprop.2.2.1, hq₂_rank]
    have hSrank' : InSrank (C.step P i j) := by
      refine { allSettled := ?_, ranks_inj := ?_ }
      · intro w
        by_cases hwi : w = i
        · subst w
          unfold Config.step
          simp only [P, PEMProtocolCoupled, PEMProtocol, if_neg hij, if_pos rfl]
          show
            (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
              (C i, C j)).1.role = .Settled
          rw [htrans]
          exact hroles.1
        · by_cases hwj : w = j
          · subst w
            unfold Config.step
            simp only [P, PEMProtocolCoupled, PEMProtocol, if_neg hij,
              if_neg hij.symm, if_pos rfl]
            show
              (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (C i, C j)).2.role = .Settled
            rw [htrans]
            exact hroles.2
          · unfold Config.step
            simp only [P, if_neg hij, if_neg hwi, if_neg hwj]
            exact hSrank.allSettled w
      · have hrank : ∀ w : Fin n, (C.step P i j w).1.rank = (C w).1.rank := by
          intro w
          by_cases hwi : w = i
          · subst w
            unfold Config.step
            simp only [P, PEMProtocolCoupled, PEMProtocol, if_neg hij, if_pos rfl]
            exact hδ_rank₁
          · by_cases hwj : w = j
            · subst w
              unfold Config.step
              simp only [P, PEMProtocolCoupled, PEMProtocol, if_neg hij,
                if_neg hij.symm, if_pos rfl]
              exact hδ_rank₂
            · unfold Config.step
              simp only [P, if_neg hij, if_neg hwi, if_neg hwj]
        intro w₁ w₂ hw
        apply hSrank.ranks_inj
        calc
          (C w₁).1.rank = (C.step P i j w₁).1.rank := (hrank w₁).symm
          _ = (C.step P i j w₂).1.rank := hw
          _ = (C w₂).1.rank := hrank w₂
    refine ⟨hSrank', ?_⟩
    intro μ hμ_med
    by_cases hμi : μ = i
    · subst μ
      unfold Config.step at hμ_med ⊢
      simp only [P, PEMProtocolCoupled, PEMProtocol, if_neg hij, if_pos rfl]
        at hμ_med ⊢
      change
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (C i, C j)).1.rank.val + 1 = ceilHalf n at hμ_med
      change L ≤
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (C i, C j)).1.timer
      rw [htrans] at hμ_med ⊢
      exact hlower.1 hμ_med
    · by_cases hμj : μ = j
      · subst μ
        unfold Config.step at hμ_med ⊢
        simp only [P, PEMProtocolCoupled, PEMProtocol, if_neg hij,
          if_neg hij.symm, if_pos rfl] at hμ_med ⊢
        change
          (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
              (C i, C j)).2.rank.val + 1 = ceilHalf n at hμ_med
        change L ≤
          (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
              (C i, C j)).2.timer
        rw [htrans] at hμ_med ⊢
        exact hlower.2 hμ_med
      · unfold Config.step at hμ_med ⊢
        simp only [P, if_neg hij, if_neg hμi, if_neg hμj] at hμ_med ⊢
        exact le_trans
          (Nat.sub_le K (if srankMedianMaxEvent C i j then 1 else 0))
          (hTimer μ hμ_med)

/-! The swap ProbHitWithin bound uses the union bound:
ProbHitWithin(InSswap, t) ≥ ProbHitWithin(InSswap ∨ ¬InSrank, t) - P(¬InSrank in t)
The first term ≥ 1/2 (Markov on swap E[T]).
The second term ≤ 8n/((n-1)·7·(Rmax+4)) < 1/4 (Markov on timer decrements).
So ProbHitWithin(InSswap, t) ≥ 1/2 - 1/4 = 1/4. -/

/-! Exit probability bound: from InSrank with sufficient median timer,
the probability of exiting InSrank within 4n² steps is ≤ 1/4.
Timer ≥ K means K (median,max) interactions needed before timer = 0.
P(≥K interactions in 4n²) ≤ 4n²·2/(n(n-1)) / K = 8n/((n-1)K).
For K ≥ 12n (which holds when timer ≥ 7(Rmax+4) and Rmax ≥ n ≥ 4):
8n/((n-1)·12n) = 2/(3(n-1)) ≤ 2/9 < 1/4. -/
theorem PEM_exit_prob_le_quarter
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (_hRmax : n ≤ Rmax) (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (_hSrank : InSrank C)
    (_hTimer : MedianTimerAtLeast (12 * n) C) :
    Probability.ProbHitWithin
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C (fun D => ¬ InSrank D) (4 * n * n) ≤
      ((4 : ENNReal)⁻¹) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Goal : Config (AgentState n) Opinion n → Prop := fun D => ¬ InSrank D
  let Event : Config (AgentState n) Opinion n → Fin n → Fin n → Bool :=
    @srankMedianMaxEvent n
  let T : ℕ := 12 * n
  have hn2 : 2 ≤ n := by omega
  have hSupport :
      ∀ S : Config (AgentState n) Opinion n × (Bool × ℕ),
        Probability.hitEventCountDist P hn2 C Goal Event (4 * n * n) S ≠ 0 →
          S.2.1 = true → T ≤ S.2.2 := by
    let Inv : Config (AgentState n) Opinion n × (Bool × ℕ) → Prop :=
      fun S => S.2.2 < T →
        S.2.1 = false ∧ InSrank S.1 ∧
          MedianTimerAtLeast (T - S.2.2) S.1
    have h0 : Inv (C, (decide (Goal C), 0)) := by
      intro _
      have hgoal : decide (Goal C) = false := by
        simp [Goal, _hSrank]
      simp [Inv, hgoal, _hSrank, _hTimer, T]
    have hstep : ∀ S : Config (AgentState n) Opinion n × (Bool × ℕ),
        Inv S →
          ∀ p : Fin n × Fin n, p ∈ (Probability.uniformPair n hn2).support →
            Inv
              (let C' : Config (AgentState n) Opinion n := S.1.step P p.1 p.2
               (C', (S.2.1 || decide (Goal C'),
                 S.2.2 + if Event S.1 p.1 p.2 then 1 else 0))) := by
      intro S hInv p hp
      intro hlt
      by_cases hcount_lt : S.2.2 < T
      · obtain ⟨hhitFalse, hSrankS, hTimerS⟩ := hInv hcount_lt
        have hp_ne : p.1 ≠ p.2 := by
          by_contra hEq
          have hprob : Probability.uniformPair n hn2 p = 0 := by
            rcases p with ⟨i, j⟩
            dsimp at hEq ⊢
            subst j
            exact Probability.uniformPair_apply_self n hn2 i
          have hmem : Probability.uniformPair n hn2 p ≠ 0 := by
            simpa [PMF.mem_support_iff] using hp
          exact hmem hprob
        have hKpos : 0 < T - S.2.2 := by omega
        have hstep' :=
          PEM_exit_step_preserves_srank_timer_count
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (K := T - S.2.2) hn4 hn0 hSrankS hTimerS hp_ne hKpos
            (by
              intro hevent
              have hnew :
                  S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0) < T := by
                simpa using hlt
              simp [Event, hevent] at hnew
              omega)
        let C' : Config (AgentState n) Opinion n := S.1.step P p.1 p.2
        have hSrankC' : InSrank C' := by
          simpa [C', P] using hstep'.1
        have hgoalFalse : decide (Goal C') = false := by
          simp [Goal, hSrankC']
        refine ⟨?_, hSrankC', ?_⟩
        · simp [C', hhitFalse, hgoalFalse]
        · have htimer := hstep'.2
          by_cases hevent : Event S.1 p.1 p.2 = true
          · have hbound :
                T - (S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0)) =
                  T - S.2.2 - 1 := by
              simp [hevent]
              omega
            simpa [C', P, Event, hevent, hbound] using htimer
          · have hbound :
                T - (S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0)) =
                  T - S.2.2 := by
              simp [hevent]
            simpa [C', P, Event, hevent, hbound] using htimer
      · exfalso
        have hnew :
            S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0) < T := by
          simpa using hlt
        exact hcount_lt
          (lt_of_le_of_lt
            (Nat.le_add_right S.2.2 (if Event S.1 p.1 p.2 then 1 else 0))
            hnew)
    intro S hSupp hhit
    have hInvS :=
      Probability.hitEventCountDist_support_inv_decide
        (P := P) (hn := hn2) (C₀ := C) (Goal := Goal) (Event := Event)
        (Inv := Inv) h0 hstep (4 * n * n) S
        (by simpa [PMF.mem_support_iff] using hSupp)
    by_contra hnot
    have hlt : S.2.2 < T := Nat.lt_of_not_ge hnot
    obtain ⟨hflagFalse, _, _⟩ := hInvS hlt
    rw [hflagFalse] at hhit
    cases hhit
  have hMain :=
    Probability.ProbHitWithin_le_eventCountDist_tail_of_support_imp
      (P := P) (hn := hn2) (C₀ := C) (Goal := Goal) (Event := Event)
      (t := 4 * n * n) (K := T) hSupport
  refine hMain.trans ?_
  simpa [P, Event, T] using
    srankMedianMaxEvent_count_tail_le_quarter
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn4 hn0 C

/-- Strengthened exit/timer-failure bound.  From `Srank` with median timer at
least `12n`, within the `4n²` swap window the probability of either leaving
`Srank` or losing positive median timer is at most `1/4`.  The proof is the
same event-count argument as `PEM_exit_prob_le_quarter`: before `12n`
median/max interactions have occurred, the maintained invariant gives both
`InSrank` and `MedianTimerAtLeast 1`. -/
theorem PEM_srank_or_timer_failure_prob_le_quarter
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (_hRmax : n ≤ Rmax) (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (_hSrank : InSrank C)
    (_hTimer : MedianTimerAtLeast (12 * n) C) :
    Probability.ProbHitWithin
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D) (4 * n * n) ≤
      ((4 : ENNReal)⁻¹) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D
  let Event : Config (AgentState n) Opinion n → Fin n → Fin n → Bool :=
    @srankMedianMaxEvent n
  let T : ℕ := 12 * n
  have hn2 : 2 ≤ n := by omega
  have hSupport :
      ∀ S : Config (AgentState n) Opinion n × (Bool × ℕ),
        Probability.hitEventCountDist P hn2 C Goal Event (4 * n * n) S ≠ 0 →
          S.2.1 = true → T ≤ S.2.2 := by
    let Inv : Config (AgentState n) Opinion n × (Bool × ℕ) → Prop :=
      fun S => S.2.2 < T →
        S.2.1 = false ∧ InSrank S.1 ∧
          MedianTimerAtLeast (T - S.2.2) S.1
    have h0 : Inv (C, (decide (Goal C), 0)) := by
      intro _
      have htimer1 : MedianTimerAtLeast 1 C :=
        MedianTimerAtLeast.mono (n := n) (a := 1) (b := T) (by
          dsimp [T]
          omega) _hTimer
      have hgoal : decide (Goal C) = false := by
        simp [Goal, _hSrank, htimer1]
      simp [hgoal, _hSrank, _hTimer, T]
    have hstep : ∀ S : Config (AgentState n) Opinion n × (Bool × ℕ),
        Inv S →
          ∀ p : Fin n × Fin n, p ∈ (Probability.uniformPair n hn2).support →
            Inv
              (let C' : Config (AgentState n) Opinion n := S.1.step P p.1 p.2
               (C', (S.2.1 || decide (Goal C'),
                 S.2.2 + if Event S.1 p.1 p.2 then 1 else 0))) := by
      intro S hInv p hp
      intro hlt
      by_cases hcount_lt : S.2.2 < T
      · obtain ⟨hhitFalse, hSrankS, hTimerS⟩ := hInv hcount_lt
        have hp_ne : p.1 ≠ p.2 := by
          by_contra hEq
          have hprob : Probability.uniformPair n hn2 p = 0 := by
            rcases p with ⟨i, j⟩
            dsimp at hEq ⊢
            subst j
            exact Probability.uniformPair_apply_self n hn2 i
          have hmem : Probability.uniformPair n hn2 p ≠ 0 := by
            simpa [PMF.mem_support_iff] using hp
          exact hmem hprob
        have hKpos : 0 < T - S.2.2 := by omega
        have hstep' :=
          PEM_exit_step_preserves_srank_timer_count
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (K := T - S.2.2) hn4 hn0 hSrankS hTimerS hp_ne hKpos
            (by
              intro hevent
              have hnew :
                  S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0) < T := by
                simpa using hlt
              simp [Event, hevent] at hnew
              omega)
        let C' : Config (AgentState n) Opinion n := S.1.step P p.1 p.2
        have hSrankC' : InSrank C' := by
          simpa [C', P] using hstep'.1
        have htimerNew :
            MedianTimerAtLeast
              (T - (S.2.2 + if Event S.1 p.1 p.2 then 1 else 0)) C' := by
          have htimer := hstep'.2
          by_cases hevent : Event S.1 p.1 p.2 = true
          · have hbound :
                T - (S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0)) =
                  T - S.2.2 - 1 := by
              simp [hevent]
              omega
            simpa [C', P, Event, hevent, hbound] using htimer
          · have hbound :
                T - (S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0)) =
                  T - S.2.2 := by
              simp [hevent]
            simpa [C', P, Event, hevent, hbound] using htimer
        have htimer1C' : MedianTimerAtLeast 1 C' :=
          MedianTimerAtLeast.mono (n := n) (a := 1)
            (b := T - (S.2.2 + if Event S.1 p.1 p.2 then 1 else 0))
            (by
              have hnew :
                  S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0) < T := by
                simpa using hlt
              omega)
            htimerNew
        have hgoalFalse : decide (Goal C') = false := by
          simp [Goal, hSrankC', htimer1C']
        refine ⟨?_, hSrankC', htimerNew⟩
        simp [C', hhitFalse, hgoalFalse]
      · exfalso
        have hnew :
            S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0) < T := by
          simpa using hlt
        exact hcount_lt
          (lt_of_le_of_lt
            (Nat.le_add_right S.2.2 (if Event S.1 p.1 p.2 then 1 else 0))
            hnew)
    intro S hSupp hhit
    have hInvS :=
      Probability.hitEventCountDist_support_inv_decide
        (P := P) (hn := hn2) (C₀ := C) (Goal := Goal) (Event := Event)
        (Inv := Inv) h0 hstep (4 * n * n) S
        (by simpa [PMF.mem_support_iff] using hSupp)
    by_contra hnot
    have hlt : S.2.2 < T := Nat.lt_of_not_ge hnot
    obtain ⟨hflagFalse, _, _⟩ := hInvS hlt
    rw [hflagFalse] at hhit
    cases hhit
  have hMain :=
    Probability.ProbHitWithin_le_eventCountDist_tail_of_support_imp
      (P := P) (hn := hn2) (C₀ := C) (Goal := Goal) (Event := Event)
      (t := 4 * n * n) (K := T) hSupport
  refine hMain.trans ?_
  simpa [P, Event, T] using
    srankMedianMaxEvent_count_tail_le_quarter
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn4 hn0 C

theorem PEM_srank_or_timer_failure_prob_le_quarter_short35
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (_hRmax : n ≤ Rmax) (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (_hSrank : InSrank C)
    (_hTimer : MedianTimerAtLeast 35 C) :
    Probability.ProbHitWithin
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D)
      (4 * n * (n - 1)) ≤ ((4 : ENNReal)⁻¹) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D
  let Event : Config (AgentState n) Opinion n → Fin n → Fin n → Bool :=
    @srankMedianMaxEvent n
  let T : ℕ := 35
  have hn2 : 2 ≤ n := by omega
  have hSupport :
      ∀ S : Config (AgentState n) Opinion n × (Bool × ℕ),
        Probability.hitEventCountDist P hn2 C Goal Event (4 * n * (n - 1)) S ≠ 0 →
          S.2.1 = true → T ≤ S.2.2 := by
    let Inv : Config (AgentState n) Opinion n × (Bool × ℕ) → Prop :=
      fun S => S.2.2 < T →
        S.2.1 = false ∧ InSrank S.1 ∧
          MedianTimerAtLeast (T - S.2.2) S.1
    have h0 : Inv (C, (decide (Goal C), 0)) := by
      intro _
      have htimer1 : MedianTimerAtLeast 1 C :=
        MedianTimerAtLeast.mono (n := n) (a := 1) (b := T) (by
          dsimp [T]
          omega) _hTimer
      have hgoal : decide (Goal C) = false := by
        simp [Goal, _hSrank, htimer1]
      simp [hgoal, _hSrank, _hTimer, T]
    have hstep : ∀ S : Config (AgentState n) Opinion n × (Bool × ℕ),
        Inv S →
          ∀ p : Fin n × Fin n, p ∈ (Probability.uniformPair n hn2).support →
            Inv
              (let C' : Config (AgentState n) Opinion n := S.1.step P p.1 p.2
               (C', (S.2.1 || decide (Goal C'),
                 S.2.2 + if Event S.1 p.1 p.2 then 1 else 0))) := by
      intro S hInv p hp
      intro hlt
      by_cases hcount_lt : S.2.2 < T
      · obtain ⟨hhitFalse, hSrankS, hTimerS⟩ := hInv hcount_lt
        have hp_ne : p.1 ≠ p.2 := by
          by_contra hEq
          have hprob : Probability.uniformPair n hn2 p = 0 := by
            rcases p with ⟨i, j⟩
            dsimp at hEq ⊢
            subst j
            exact Probability.uniformPair_apply_self n hn2 i
          have hmem : Probability.uniformPair n hn2 p ≠ 0 := by
            simpa [PMF.mem_support_iff] using hp
          exact hmem hprob
        have hKpos : 0 < T - S.2.2 := by omega
        have hstep' :=
          PEM_exit_step_preserves_srank_timer_count
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (K := T - S.2.2) hn4 hn0 hSrankS hTimerS hp_ne hKpos
            (by
              intro hevent
              have hnew :
                  S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0) < T := by
                simpa using hlt
              simp [Event, hevent] at hnew
              omega)
        let C' : Config (AgentState n) Opinion n := S.1.step P p.1 p.2
        have hSrankC' : InSrank C' := by
          simpa [C', P] using hstep'.1
        have htimerNew :
            MedianTimerAtLeast
              (T - (S.2.2 + if Event S.1 p.1 p.2 then 1 else 0)) C' := by
          have htimer := hstep'.2
          by_cases hevent : Event S.1 p.1 p.2 = true
          · have hbound :
                T - (S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0)) =
                  T - S.2.2 - 1 := by
              simp [hevent]
              omega
            simpa [C', P, Event, hevent, hbound] using htimer
          · have hbound :
                T - (S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0)) =
                  T - S.2.2 := by
              simp [hevent]
            simpa [C', P, Event, hevent, hbound] using htimer
        have htimer1C' : MedianTimerAtLeast 1 C' :=
          MedianTimerAtLeast.mono (n := n) (a := 1)
            (b := T - (S.2.2 + if Event S.1 p.1 p.2 then 1 else 0))
            (by
              have hnew :
                  S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0) < T := by
                simpa using hlt
              omega)
            htimerNew
        have hgoalFalse : decide (Goal C') = false := by
          simp [Goal, hSrankC', htimer1C']
        refine ⟨?_, hSrankC', htimerNew⟩
        simp [C', hhitFalse, hgoalFalse]
      · exfalso
        have hnew :
            S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0) < T := by
          simpa using hlt
        exact hcount_lt
          (lt_of_le_of_lt
            (Nat.le_add_right S.2.2 (if Event S.1 p.1 p.2 then 1 else 0))
            hnew)
    intro S hSupp hhit
    have hInvS :=
      Probability.hitEventCountDist_support_inv_decide
        (P := P) (hn := hn2) (C₀ := C) (Goal := Goal) (Event := Event)
        (Inv := Inv) h0 hstep (4 * n * (n - 1)) S
        (by simpa [PMF.mem_support_iff] using hSupp)
    by_contra hnot
    have hlt : S.2.2 < T := Nat.lt_of_not_ge hnot
    obtain ⟨hflagFalse, _, _⟩ := hInvS hlt
    rw [hflagFalse] at hhit
    cases hhit
  have hMain :=
    Probability.ProbHitWithin_le_eventCountDist_tail_of_support_imp
      (P := P) (hn := hn2) (C₀ := C) (Goal := Goal) (Event := Event)
      (t := 4 * n * (n - 1)) (K := T) hSupport
  refine hMain.trans ?_
  simpa [P, Event, T] using
    srankMedianMaxEvent_count_tail_le_quarter_short35
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn4 hn0 C

theorem PEM_swap_ProbHitWithin_InSswap
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast (12 * n) C) :
    ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C InSswap (4 * n * n) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  have hOrExit := PEM_swap_ProbHitWithin_or_exit hn4 hn0 hRmax hEmax hDmax C hSrank
  have hExit := PEM_exit_prob_le_quarter hn4 hn0 hRmax hEmax hDmax C hSrank hTimer
  simpa [P] using
    (ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4
      P hn2 C InSswap (fun D => ¬ InSrank D) (4 * n * n)
      hOrExit hExit)

/-- Timer-live swap lower bound.  The phase-B descent reaches `InSswap` with
probability at least `1/2` unless it exits `InSrank`; the event-count tail bound
also rules out, with probability `3/4`, either exiting `InSrank` or exhausting
the median timer.  A union-bound subtraction leaves a `1/4` chance of reaching
`InSswap` while the median timer is still positive. -/
theorem PEM_swap_ProbHitWithin_InSswap_timer_live
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast (12 * n) C) :
    ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => InSswap D ∧ MedianTimerAtLeast 1 D) (4 * n * n) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  let Good : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianTimerAtLeast 1 D
  let Bad : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D
  let OrExit : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∨ ¬ InSrank D
  have hOrExit :
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C OrExit (4 * n * n) := by
    simpa [P, OrExit] using
      PEM_swap_ProbHitWithin_or_exit hn4 hn0 hRmax hEmax hDmax C hSrank
  have hBad :
      Probability.ProbHitWithin P hn2 C Bad (4 * n * n) ≤
        ((4 : ENNReal)⁻¹) := by
    simpa [P, Bad] using
      PEM_srank_or_timer_failure_prob_le_quarter
        hn4 hn0 hRmax hEmax hDmax C hSrank hTimer
  have hOrExit_mono :
      Probability.ProbHitWithin P hn2 C OrExit (4 * n * n) ≤
        Probability.ProbHitWithin P hn2 C
          (fun D => Good D ∨ Bad D) (4 * n * n) := by
    refine Probability.ProbHitWithin_mono_goal P hn2 C OrExit
      (fun D => Good D ∨ Bad D) ?_ (4 * n * n)
    intro D hD
    rcases hD with hSwap | hNotRank
    · by_cases hTimerD : MedianTimerAtLeast 1 D
      · exact Or.inl ⟨hSwap, hTimerD⟩
      · exact Or.inr (Or.inr hTimerD)
    · exact Or.inr (Or.inl hNotRank)
  have hOrGoodBad :
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C
          (fun D => Good D ∨ Bad D) (4 * n * n) :=
    hOrExit.trans hOrExit_mono
  simpa [P, Good] using
    (ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4
      P hn2 C Good Bad (4 * n * n) hOrGoodBad hBad)

theorem PEM_swap_ProbHitWithin_InSswap_timer_live_short35
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast 35 C) :
    ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => InSswap D ∧ MedianTimerAtLeast 1 D)
        (4 * n * (n - 1)) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  let Good : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianTimerAtLeast 1 D
  let Bad : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D
  let OrExit : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∨ ¬ InSrank D
  have hOrExit :
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C OrExit (4 * n * (n - 1)) := by
    simpa [P, OrExit] using
      PEM_swap_ProbHitWithin_or_exit_short hn4 hn0 hRmax hEmax hDmax C hSrank
  have hBad :
      Probability.ProbHitWithin P hn2 C Bad (4 * n * (n - 1)) ≤
        ((4 : ENNReal)⁻¹) := by
    simpa [P, Bad] using
      PEM_srank_or_timer_failure_prob_le_quarter_short35
        hn4 hn0 hRmax hEmax hDmax C hSrank hTimer
  have hOrExit_mono :
      Probability.ProbHitWithin P hn2 C OrExit (4 * n * (n - 1)) ≤
        Probability.ProbHitWithin P hn2 C
          (fun D => Good D ∨ Bad D) (4 * n * (n - 1)) := by
    refine Probability.ProbHitWithin_mono_goal P hn2 C OrExit
      (fun D => Good D ∨ Bad D) ?_ (4 * n * (n - 1))
    intro D hD
    rcases hD with hSwap | hNotRank
    · by_cases hTimerD : MedianTimerAtLeast 1 D
      · exact Or.inl ⟨hSwap, hTimerD⟩
      · exact Or.inr (Or.inr hTimerD)
    · exact Or.inr (Or.inl hNotRank)
  have hOrGoodBad :
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C
          (fun D => Good D ∨ Bad D) (4 * n * (n - 1)) :=
    hOrExit.trans hOrExit_mono
  simpa [P, Good] using
    (ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4
      P hn2 C Good Bad (4 * n * (n - 1)) hOrGoodBad hBad)

theorem PEM_swap_ProbHitWithin_InSswap_timer_live_const35
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast 35 C) :
    ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => InSswap D ∧ MedianTimerAtLeast 1 D) (4 * n * n) := by
  have hshort :=
    PEM_swap_ProbHitWithin_InSswap_timer_live_short35
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax hEmax hDmax C hSrank hTimer
  exact hshort.trans
    (Probability.ProbHitWithin_mono_time
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C
      (fun D => InSswap D ∧ MedianTimerAtLeast 1 D)
      (by
        exact Nat.mul_le_mul_left (4 * n) (Nat.sub_le n 1)))

theorem PEM_swap_ProbHitWithin_InSswap_timer_live_const35_bounded
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast 35 C)
    (hBound : IsTimerBoundedConfig (7 * (Rmax + 4)) C) :
    ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D =>
          InSswap D ∧ MedianTimerAtLeast 1 D ∧
            IsTimerBoundedConfig (7 * (Rmax + 4)) D)
        (4 * n * n) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  let Good : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianTimerAtLeast 1 D
  let Inv : Config (AgentState n) Opinion n → Prop :=
    IsTimerBoundedConfig (7 * (Rmax + 4))
  have hBase :
      ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C Good (4 * n * n) := by
    simpa [P, Good] using
      PEM_swap_ProbHitWithin_InSswap_timer_live_const35
        hn4 hn0 hRmax hEmax hDmax C hSrank hTimer
  have hInvStep : ∀ D : Config (AgentState n) Opinion n, Inv D →
      ∀ i j : Fin n, Inv (D.step P i j) := by
    intro D hD i j
    simpa [P, Inv] using
      PEMProtocolCoupled_preserves_timer_bounded hn0 D hD i j
  have hEq :=
    Probability.ProbHitWithin_eq_and_inv_of_invariant
      P hn2 C Good Inv hBound hInvStep (4 * n * n)
  rw [← hEq] at hBase
  simpa [P, Good, Inv, and_assoc] using hBase

/-- Timer-live swap lower bound, retaining an ambient timer upper-bound
invariant.  This is the phase-B form needed by the paper-aligned chain:
`InSswap` is reached while the median timer is positive and all timers remain
bounded by the protocol timer budget. -/
theorem PEM_swap_ProbHitWithin_InSswap_timer_live_bounded
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast (12 * n) C)
    (hBound : IsTimerBoundedConfig (7 * (Rmax + 4)) C) :
    ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D =>
          InSswap D ∧ MedianTimerAtLeast 1 D ∧
            IsTimerBoundedConfig (7 * (Rmax + 4)) D)
        (4 * n * n) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  let Good : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianTimerAtLeast 1 D
  let Inv : Config (AgentState n) Opinion n → Prop :=
    IsTimerBoundedConfig (7 * (Rmax + 4))
  have hBase :
      ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C Good (4 * n * n) := by
    simpa [P, Good] using
      PEM_swap_ProbHitWithin_InSswap_timer_live
        hn4 hn0 hRmax hEmax hDmax C hSrank hTimer
  have hInvStep : ∀ D : Config (AgentState n) Opinion n, Inv D →
      ∀ i j : Fin n, Inv (D.step P i j) := by
    intro D hD i j
    simpa [P, Inv] using
      PEMProtocolCoupled_preserves_timer_bounded hn0 D hD i j
  have hEq :=
    Probability.ProbHitWithin_eq_and_inv_of_invariant
      P hn2 C Good Inv hBound hInvStep (4 * n * n)
  rw [← hEq] at hBase
  simpa [P, Good, Inv, and_assoc] using hBase

theorem PEM_end_to_end_ProbHitWithin_from_expected_phase_bounds
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C₀ : Config (AgentState n) Opinion n)
    (hInit : IsInitialConfig C₀)
    (hRankBound :
      Probability.expectedHittingTime
        (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀
        (fun C =>
          InSrank C ∧ MedianTimerAtLeast 35 C ∧
            IsTimerBoundedConfig (7 * (Rmax + 4)) C) ≤
        ((Rmax * n * n : ℕ) : ENNReal))
    (hConsensusBound :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C → MedianTimerAtLeast 1 C →
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        Probability.expectedHittingTime
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C IsConsensusConfig ≤
          ((10 * Rmax * n * n : ℕ) : ENNReal)) :
    ((16 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀ IsConsensusConfig
        ((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n) with hP_def
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  let RankTarget : Config (AgentState n) Opinion n → Prop :=
    fun C =>
      InSrank C ∧ MedianTimerAtLeast 35 C ∧
        IsTimerBoundedConfig (7 * (Rmax + 4)) C
  let SwapLiveTarget : Config (AgentState n) Opinion n → Prop :=
    fun C =>
      InSswap C ∧ MedianTimerAtLeast 1 C ∧
        IsTimerBoundedConfig (7 * (Rmax + 4)) C
  have hRankE : Probability.expectedHittingTime P hn2 C₀ RankTarget ≤
      ((Rmax * n * n : ℕ) : ENNReal) :=
    hRankBound
  have hRankW : 2 * (Rmax * n * n) ≤ (2 * Rmax * n * n) + 1 := by nlinarith
  have hRankPH : ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C₀ RankTarget (2 * Rmax * n * n) :=
    Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le P hn2 C₀ RankTarget
      hRankE hRankW
  have hSwapPH : ∀ C : Config (AgentState n) Opinion n, RankTarget C →
      ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C SwapLiveTarget (4 * n * n) :=
    fun C ⟨hR, hT, hB⟩ => by
      simpa [P, SwapLiveTarget] using
        PEM_swap_ProbHitWithin_InSswap_timer_live_const35_bounded
          hn4 hn0 hRmax hEmax hDmax C hR hT hB
  have hConsE : ∀ C : Config (AgentState n) Opinion n, SwapLiveTarget C →
      Probability.expectedHittingTime P hn2 C IsConsensusConfig ≤
        ((10 * Rmax * n * n : ℕ) : ENNReal) :=
    fun C hC => hConsensusBound C hC.1 hC.2.1 hC.2.2
  have hConsW : 2 * (10 * Rmax * n * n) ≤ (20 * Rmax * n * n) + 1 := by nlinarith
  have hConsPH : ∀ C : Config (AgentState n) Opinion n, SwapLiveTarget C →
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig (20 * Rmax * n * n) :=
    fun C hC => Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le P hn2 C
      IsConsensusConfig (hConsE C hC) hConsW
  have hAB : ((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C₀ SwapLiveTarget
        (2 * Rmax * n * n + 4 * n * n) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀ RankTarget SwapLiveTarget
      (2 * Rmax * n * n) (4 * n * n)
      ((2 : ENNReal)⁻¹) ((4 : ENNReal)⁻¹)
      hRankPH (fun D hD => hSwapPH D hD)
  have hChain : (((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹)) * ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C₀ IsConsensusConfig
        ((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀ SwapLiveTarget IsConsensusConfig
      (2 * Rmax * n * n + 4 * n * n) (20 * Rmax * n * n)
      (((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹)) ((2 : ENNReal)⁻¹)
      hAB (fun D hD => hConsPH D hD)
  calc ((16 : ENNReal)⁻¹)
      = ((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) := by
        rw [← ENNReal.toReal_eq_toReal_iff'
          (by rw [ENNReal.inv_ne_top]; norm_num)
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top (by simp [ENNReal.inv_ne_top]) (by simp [ENNReal.inv_ne_top]))
            (by simp [ENNReal.inv_ne_top]))]
        simp only [ENNReal.toReal_inv, ENNReal.toReal_mul]
        norm_num
    _ ≤ _ := hChain

/-- Global-window version of
`PEM_end_to_end_ProbHitWithin_from_expected_phase_bounds`.

The remaining phase work is isolated in two reusable expected-time hypotheses:
ranking from every timer-bounded configuration, and consensus from every live
`InSswap` configuration.  This theorem removes the artificial
`IsInitialConfig` dependency from the window-success composition, which is the
form needed for geometric restarts. -/
theorem PEM_end_to_end_ProbHitWithin_from_global_expected_phase_bounds
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRankBound :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        Probability.expectedHittingTime
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C
          (fun D =>
            InSrank D ∧ MedianTimerAtLeast 35 D ∧
              IsTimerBoundedConfig (7 * (Rmax + 4)) D) ≤
          ((Rmax * n * n : ℕ) : ENNReal))
    (hConsensusBound :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C → MedianTimerAtLeast 1 C →
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        Probability.expectedHittingTime
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C IsConsensusConfig ≤
          ((10 * Rmax * n * n : ℕ) : ENNReal)) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C₀ →
      ((16 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C₀ IsConsensusConfig
          ((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n) := by
  classical
  intro C₀ hTimer₀
  set P := PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n) with hP_def
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  let RankTarget : Config (AgentState n) Opinion n → Prop :=
    fun C =>
      InSrank C ∧ MedianTimerAtLeast 35 C ∧
        IsTimerBoundedConfig (7 * (Rmax + 4)) C
  let SwapLiveTarget : Config (AgentState n) Opinion n → Prop :=
    fun C =>
      InSswap C ∧ MedianTimerAtLeast 1 C ∧
        IsTimerBoundedConfig (7 * (Rmax + 4)) C
  have hRankE : Probability.expectedHittingTime P hn2 C₀ RankTarget ≤
      ((Rmax * n * n : ℕ) : ENNReal) :=
    hRankBound C₀ hTimer₀
  have hRankW : 2 * (Rmax * n * n) ≤ (2 * Rmax * n * n) + 1 := by nlinarith
  have hRankPH : ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C₀ RankTarget (2 * Rmax * n * n) :=
    Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le P hn2 C₀ RankTarget
      hRankE hRankW
  have hSwapPH : ∀ C : Config (AgentState n) Opinion n, RankTarget C →
      ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C SwapLiveTarget (4 * n * n) :=
    fun C ⟨hR, hT, hB⟩ => by
      simpa [P, SwapLiveTarget] using
        PEM_swap_ProbHitWithin_InSswap_timer_live_const35_bounded
          hn4 hn0 hRmax hEmax hDmax C hR hT hB
  have hConsE : ∀ C : Config (AgentState n) Opinion n, SwapLiveTarget C →
      Probability.expectedHittingTime P hn2 C IsConsensusConfig ≤
        ((10 * Rmax * n * n : ℕ) : ENNReal) :=
    fun C hC => hConsensusBound C hC.1 hC.2.1 hC.2.2
  have hConsW : 2 * (10 * Rmax * n * n) ≤ (20 * Rmax * n * n) + 1 := by nlinarith
  have hConsPH : ∀ C : Config (AgentState n) Opinion n, SwapLiveTarget C →
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig (20 * Rmax * n * n) :=
    fun C hC => Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le P hn2 C
      IsConsensusConfig (hConsE C hC) hConsW
  have hAB : ((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C₀ SwapLiveTarget
        (2 * Rmax * n * n + 4 * n * n) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀ RankTarget SwapLiveTarget
      (2 * Rmax * n * n) (4 * n * n)
      ((2 : ENNReal)⁻¹) ((4 : ENNReal)⁻¹)
      hRankPH (fun D hD => hSwapPH D hD)
  have hChain : (((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹)) * ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C₀ IsConsensusConfig
        ((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀ SwapLiveTarget IsConsensusConfig
      (2 * Rmax * n * n + 4 * n * n) (20 * Rmax * n * n)
      (((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹)) ((2 : ENNReal)⁻¹)
      hAB (fun D hD => hConsPH D hD)
  calc ((16 : ENNReal)⁻¹)
      = ((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) := by
        rw [← ENNReal.toReal_eq_toReal_iff'
          (by rw [ENNReal.inv_ne_top]; norm_num)
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top (by simp [ENNReal.inv_ne_top]) (by simp [ENNReal.inv_ne_top]))
            (by simp [ENNReal.inv_ne_top]))]
        simp only [ENNReal.toReal_inv, ENNReal.toReal_mul]
        norm_num
    _ ≤ _ := hChain

/-- Expected-parallel-time consequence of the global phase expected-time
bounds.  This is the restart-ready end-to-end form: the timer upper bound is
an invariant of the coupled protocol, and the two remaining quantitative
obligations are exactly the global ranking and live-consensus expected-time
phase bounds. -/
theorem PEM_expected_parallel_time_from_global_expected_phase_bounds
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRankBound :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        Probability.expectedHittingTime
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C
          (fun D =>
            InSrank D ∧ MedianTimerAtLeast 35 D ∧
              IsTimerBoundedConfig (7 * (Rmax + 4)) D) ≤
          ((Rmax * n * n : ℕ) : ENNReal))
    (hConsensusBound :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C → MedianTimerAtLeast 1 C →
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        Probability.expectedHittingTime
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C IsConsensusConfig ≤
          ((10 * Rmax * n * n : ℕ) : ENNReal)) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C₀ →
      Probability.expectedParallelTimeToConsensus
        (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀ ≤
        (((((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n : ℕ) : ENNReal) *
          ((16 : ENNReal)⁻¹)⁻¹) / n) := by
  classical
  intro C₀ hTimer₀
  set P := PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n) with hP_def
  have hn2 : 2 ≤ n := by omega
  let Inv : Config (AgentState n) Opinion n → Prop :=
    IsTimerBoundedConfig (7 * (Rmax + 4))
  let K : ℕ := (2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n
  have hKpos : 0 < K := by
    dsimp [K]
    have hRpos : 0 < Rmax := by omega
    have hnpos : 0 < n := by omega
    have hfirst : 0 < 2 * Rmax * n * n := by positivity
    omega
  haveI : NeZero K := ⟨Nat.pos_iff_ne_zero.mp hKpos⟩
  have hp_le_one : ((16 : ENNReal)⁻¹) ≤ 1 := by norm_num
  have hInvStep : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j) := by
    intro C hC i j
    simpa [P, Inv] using
      PEMProtocolCoupled_preserves_timer_bounded (by omega : 0 < n) C hC i j
  have hwin : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ¬ IsConsensusConfig C →
      ((16 : ENNReal)⁻¹) ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig K := by
    intro C hC _hNot
    simpa [P, Inv, K] using
      (PEM_end_to_end_ProbHitWithin_from_global_expected_phase_bounds
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hRmax hEmax hDmax hRankBound hConsensusBound C hC)
  simpa [Probability.expectedParallelTimeToConsensus, P, Inv, K] using
    (Probability.expectedParallelTime_le_window_mul_inv_of_invariant
      P hn2 C₀ IsConsensusConfig Inv K ((16 : ENNReal)⁻¹)
      hp_le_one hTimer₀ hInvStep hwin)

end SSEM
