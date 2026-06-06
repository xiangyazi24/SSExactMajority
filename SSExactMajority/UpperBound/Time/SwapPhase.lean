import SSExactMajority.UpperBound.Time.Defs

namespace SSEM

open scoped ENNReal

/-! ### Swap-phase good-pair counting

These are the first quantitative bridge lemmas for Phase B.  They turn the
existing deterministic descent theorem for a misordered pair into a lower bound
on the number of scheduler pairs that strictly decrease `misorderedCount`.
-/

/-- B-input agents that currently occupy the low-rank A side. -/
def wrongLowBSet (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter fun u => (C u).2 = Opinion.B ∧ (C u).1.rank.val < nAOf C

/-- A-input agents that currently occupy the high-rank B side. -/
def wrongHighASet (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter fun u => (C u).2 = Opinion.A ∧ nAOf C ≤ (C u).1.rank.val

/-- Agents currently occupying the low-rank side. -/
def lowRankSet (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter fun u => (C u).1.rank.val < nAOf C

/-- A-input agents currently occupying the low-rank side. -/
def lowASet (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter fun u => (C u).2 = Opinion.A ∧ (C u).1.rank.val < nAOf C

/-- Count of B-input agents on the low-rank side. -/
def wrongLowBCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (wrongLowBSet C).card

/-- Count of A-input agents on the high-rank side. -/
def wrongHighACount (C : Config (AgentState n) Opinion n) : ℕ :=
  (wrongHighASet C).card

/-- Auxiliary: cardinality of `{i : Fin n | i.val < k}` is exactly `k`
when `k ≤ n`.  This local copy keeps the time-bound layer independent of the
private helper used in the deterministic swap proof. -/
theorem time_card_Fin_filter_val_lt {n k : ℕ} (hk : k ≤ n) :
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

/-- In an `Srank` configuration, exactly `k` agents have rank below `k`. -/
theorem time_card_filter_rank_lt {C : Config (AgentState n) Opinion n}
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
  rw [← Finset.card_image_of_injective _ hinj, himg, time_card_Fin_filter_val_lt hk]

theorem lowRankSet_card_of_InSrank {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (lowRankSet C).card = nAOf C := by
  unfold lowRankSet
  exact time_card_filter_rank_lt hSrank (by have := nAOf_add_nBOf C; omega)

theorem lowRankSet_eq_lowA_union_wrongLowB
    {C : Config (AgentState n) Opinion n} :
    lowRankSet C = lowASet C ∪ wrongLowBSet C := by
  classical
  ext u
  simp only [lowRankSet, lowASet, wrongLowBSet, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hlow
    cases h : (C u).2 with
    | A => exact Or.inl ⟨rfl, hlow⟩
    | B => exact Or.inr ⟨rfl, hlow⟩
  · rintro (⟨_, hlow⟩ | ⟨_, hlow⟩) <;> exact hlow

theorem agentsWithInput_A_eq_lowA_union_wrongHighA
    {C : Config (AgentState n) Opinion n} :
    C.agentsWithInput Opinion.A = lowASet C ∪ wrongHighASet C := by
  classical
  ext u
  simp only [Config.agentsWithInput, Config.inputOf, lowASet, wrongHighASet,
    Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hA
    by_cases hlow : (C u).1.rank.val < nAOf C
    · exact Or.inl ⟨hA, hlow⟩
    · exact Or.inr ⟨hA, by omega⟩
  · rintro (⟨hA, _⟩ | ⟨hA, _⟩) <;> exact hA

theorem lowA_disjoint_wrongLowB {C : Config (AgentState n) Opinion n} :
    Disjoint (lowASet C) (wrongLowBSet C) := by
  classical
  rw [Finset.disjoint_left]
  intro u huA huB
  rw [lowASet, Finset.mem_filter] at huA
  rw [wrongLowBSet, Finset.mem_filter] at huB
  rw [huA.2.1] at huB
  cases huB.2.1

theorem lowA_disjoint_wrongHighA {C : Config (AgentState n) Opinion n} :
    Disjoint (lowASet C) (wrongHighASet C) := by
  classical
  rw [Finset.disjoint_left]
  intro u huLow huHigh
  rw [lowASet, Finset.mem_filter] at huLow
  rw [wrongHighASet, Finset.mem_filter] at huHigh
  omega

/-- In an `Srank` configuration, the two misplaced sides have the same
cardinality. -/
theorem wrongLowBCount_eq_wrongHighACount_of_InSrank
    {C : Config (AgentState n) Opinion n} (hSrank : InSrank C) :
    wrongLowBCount C = wrongHighACount C := by
  classical
  have hLowPartition :
      (lowASet C).card + (wrongLowBSet C).card = nAOf C := by
    have hcard := Finset.card_union_of_disjoint
      (lowA_disjoint_wrongLowB (C := C))
    rw [← lowRankSet_eq_lowA_union_wrongLowB (C := C)] at hcard
    rw [lowRankSet_card_of_InSrank hSrank] at hcard
    exact hcard.symm
  have hAPartition :
      (lowASet C).card + (wrongHighASet C).card = nAOf C := by
    have hcard := Finset.card_union_of_disjoint
      (lowA_disjoint_wrongHighA (C := C))
    rw [← agentsWithInput_A_eq_lowA_union_wrongHighA (C := C)] at hcard
    unfold nAOf
    exact hcard.symm
  unfold wrongLowBCount wrongHighACount
  omega

/-- If no B-input agent remains on the low-rank side, then an `Srank`
configuration is already in `Sswap`. -/
theorem InSswap_of_InSrank_of_wrongLowBCount_zero
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (h0 : wrongLowBCount C = 0) :
    InSswap C := by
  classical
  have hLowEmpty : wrongLowBSet C = ∅ := by
    unfold wrongLowBCount at h0
    exact Finset.card_eq_zero.mp h0
  have hHigh0 : wrongHighACount C = 0 := by
    rw [← wrongLowBCount_eq_wrongHighACount_of_InSrank hSrank]
    exact h0
  have hHighEmpty : wrongHighASet C = ∅ := by
    unfold wrongHighACount at hHigh0
    exact Finset.card_eq_zero.mp hHigh0
  refine { toInSrank := hSrank, input_rank := ?_ }
  intro v
  constructor
  · intro hA
    by_contra hnot
    push_neg at hnot
    have hmem : v ∈ wrongHighASet C := by
      rw [wrongHighASet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hA, hnot⟩
    rw [hHighEmpty] at hmem
    exact Finset.notMem_empty v hmem
  · intro hLow
    cases h : (C v).2 with
    | A => rfl
    | B =>
        have hmem : v ∈ wrongLowBSet C := by
          rw [wrongLowBSet, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, h, hLow⟩
        rw [hLowEmpty] at hmem
        exact (Finset.notMem_empty v hmem).elim

/-- In an `Sswap` configuration, the single-side misplaced count is zero. -/
theorem wrongLowBCount_eq_zero_of_InSswap
    {C : Config (AgentState n) Opinion n} (hSswap : InSswap C) :
    wrongLowBCount C = 0 := by
  classical
  unfold wrongLowBCount
  rw [Finset.card_eq_zero]
  apply Finset.ext
  intro v
  constructor
  · intro hmem
    rw [wrongLowBSet, Finset.mem_filter] at hmem
    have hRankGe : nAOf C ≤ (C v).1.rank.val := by
      by_contra hlt
      push_neg at hlt
      have hA : (C v).2 = Opinion.A := (hSswap.input_rank v).mpr hlt
      rw [hA] at hmem
      cases hmem.2.1
    omega
  · intro hmem
    exact (Finset.notMem_empty v hmem).elim

/-- If an `Srank` configuration has not yet reached `Sswap`, the single-side
misplaced count is positive. -/
theorem wrongLowBCount_pos_of_InSrank_not_InSswap
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hNotSwap : ¬ InSswap C) :
    0 < wrongLowBCount C := by
  by_contra hpos
  have hzero : wrongLowBCount C = 0 := by omega
  exact hNotSwap (InSswap_of_InSrank_of_wrongLowBCount_zero hSrank hzero)

/-- Within `Srank`, `Sswap` is exactly the zero level of the single-side
misplaced potential. -/
theorem InSswap_iff_wrongLowBCount_zero_of_InSrank
    {C : Config (AgentState n) Opinion n} (hSrank : InSrank C) :
    InSswap C ↔ wrongLowBCount C = 0 := by
  constructor
  · exact wrongLowBCount_eq_zero_of_InSswap
  · exact InSswap_of_InSrank_of_wrongLowBCount_zero hSrank

/-- The single-side misplaced count is always bounded by the population size. -/
theorem wrongLowBCount_le_n (C : Config (AgentState n) Opinion n) :
    wrongLowBCount C ≤ n := by
  unfold wrongLowBCount wrongLowBSet
  calc
    (Finset.univ.filter
        (fun u : Fin n => (C u).2 = Opinion.B ∧ (C u).1.rank.val < nAOf C)).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-- Stepping a low-side B against a high-side A removes that low-side B from
the single-side misplaced set and changes no other membership. -/
theorem wrongLowBSet_step_at_wrongLowB_wrongHighA
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hSrank : InSrank C)
    {u v : Fin n}
    (hu : u ∈ wrongLowBSet C) (hv : v ∈ wrongHighASet C) :
    wrongLowBSet (C.step (protocolPEM n trank Rmax rankDelta) u v) =
      (wrongLowBSet C).erase u := by
  classical
  rw [wrongLowBSet, Finset.mem_filter] at hu
  rw [wrongHighASet, Finset.mem_filter] at hv
  rcases hu with ⟨_, huB, huLow⟩
  rcases hv with ⟨_, hvA, hvHigh⟩
  have huv : u ≠ v := by
    intro huv
    subst v
    rw [huB] at hvA
    cases hvA
  have hRankLt : (C u).1.rank < (C v).1.rank := by
    exact_mod_cast (by omega : (C u).1.rank.val < (C v).1.rank.val)
  have hMis : MisorderedPair C (u, v) :=
    ⟨huB, hvA, hRankLt⟩
  set C' := C.step (protocolPEM n trank Rmax rankDelta) u v
  have hRankSwap := transitionPEM_rank_swap_at_misorder
    (trank := trank) (Rmax := Rmax) hRankDelta hSrank hMis
  have huRank : (C' u).1.rank = (C v).1.rank := by
    show ((C.step (protocolPEM n trank Rmax rankDelta) u v) u).1.rank =
      (C v).1.rank
    unfold Config.step
    simp only [if_neg huv, if_pos rfl]
    exact hRankSwap.1
  have hvRank : (C' v).1.rank = (C u).1.rank := by
    show ((C.step (protocolPEM n trank Rmax rankDelta) u v) v).1.rank =
      (C u).1.rank
    unfold Config.step
    simp only [if_neg huv, if_neg huv.symm, if_pos rfl]
    exact hRankSwap.2
  have hOtherRank :
      ∀ w : Fin n, w ≠ u → w ≠ v → (C' w).1.rank = (C w).1.rank := by
    intro w hwu hwv
    show ((C.step (protocolPEM n trank Rmax rankDelta) u v) w).1.rank =
      (C w).1.rank
    unfold Config.step
    simp [huv, hwu, hwv]
  have hInput : ∀ w : Fin n, (C' w).2 = (C w).2 := by
    intro w
    exact step_input_preserved
      (protocolPEM n trank Rmax rankDelta) C u v w
  have hnA : nAOf C' = nAOf C := by
    simpa [C'] using
      (nAOf_step_eq (trank := trank) (Rmax := Rmax)
        (rankDelta := rankDelta) C u v)
  ext w
  by_cases hwu : w = u
  · subst w
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and]
    constructor
    · intro hmem
      rw [wrongLowBSet, Finset.mem_filter] at hmem
      have hlow' : (C v).1.rank.val < nAOf C := by
        have hlow'' : (C' u).1.rank.val < nAOf C' := hmem.2.2
        rw [huRank, hnA] at hlow''
        exact hlow''
      omega
    · intro h
      exact h.elim
  · by_cases hwv : w = v
    · subst w
      simp only [Finset.mem_erase, huv.symm, true_and]
      constructor
      · intro hmem
        rw [wrongLowBSet, Finset.mem_filter] at hmem
        have hvB : (C v).2 = Opinion.B := by
          rw [← hInput v]
          exact hmem.2.1
        rw [hvA] at hvB
        cases hvB
      · intro hmem
        rw [wrongLowBSet, Finset.mem_filter] at hmem
        have hvB : (C v).2 = Opinion.B := hmem.2.2.1
        rw [hvA] at hvB
        cases hvB
    · rw [wrongLowBSet, Finset.mem_erase, wrongLowBSet]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hInput w, hOtherRank w hwu hwv, hnA]
      constructor
      · intro hmem
        exact ⟨hwu, hmem⟩
      · intro hmem
        exact hmem.2

/-- A low-side B/high-side A interaction strictly decreases the single-side
misplaced count. -/
theorem wrongLowBCount_decreases_step_at_wrongLowB_wrongHighA
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hSrank : InSrank C)
    {u v : Fin n}
    (hu : u ∈ wrongLowBSet C) (hv : v ∈ wrongHighASet C) :
    wrongLowBCount (C.step (protocolPEM n trank Rmax rankDelta) u v) <
      wrongLowBCount C := by
  classical
  have hset := wrongLowBSet_step_at_wrongLowB_wrongHighA
    (trank := trank) (Rmax := Rmax) hRankDelta hSrank hu hv
  unfold wrongLowBCount
  have hpos : 0 < (wrongLowBSet C).card := Finset.card_pos.mpr ⟨u, hu⟩
  rw [hset, Finset.card_erase_of_mem hu]
  omega

/-- While the configuration is in `Srank`, one PEM step cannot increase the
single-side misplaced-count potential.  A Phase-4 swap only exchanges a lower
ranked `B` with a higher ranked `A`; all other settled pairs preserve ranks. -/
theorem wrongLowBCount_step_le_of_InSrank
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hSrank : InSrank C)
    (u v : Fin n) :
    wrongLowBCount (C.step (protocolPEM n trank Rmax rankDelta) u v) ≤
      wrongLowBCount C := by
  classical
  by_cases huv : u = v
  · subst v
    simp [Config.step]
  · set P := protocolPEM n trank Rmax rankDelta
    set C' := C.step P u v
    have hInput : ∀ w : Fin n, (C' w).2 = (C w).2 := by
      intro w
      simpa [C', P] using step_input_preserved P C u v w
    have hnA : nAOf C' = nAOf C := by
      simpa [C', P] using
        (nAOf_step_eq (trank := trank) (Rmax := Rmax)
          (rankDelta := rankDelta) C u v)
    have hRankNe : (C u).1.rank ≠ (C v).1.rank := by
      intro hEq
      exact huv (hSrank.ranks_inj hEq)
    by_cases hswap :
        (C u).1.rank < (C v).1.rank ∧ (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A
    · have hMis : MisorderedPair C (u, v) := ⟨hswap.2.1, hswap.2.2, hswap.1⟩
      have hRankSwap := transitionPEM_rank_swap_at_misorder
        (trank := trank) (Rmax := Rmax) hRankDelta hSrank hMis
      have huRank : (C' u).1.rank = (C v).1.rank := by
        show ((C.step P u v) u).1.rank = (C v).1.rank
        simp only [P, Config.step, if_neg huv, if_pos rfl]
        exact hRankSwap.1
      have hvRank : (C' v).1.rank = (C u).1.rank := by
        show ((C.step P u v) v).1.rank = (C u).1.rank
        simp only [P, Config.step, if_neg huv, if_neg (Ne.symm huv), if_pos rfl]
        exact hRankSwap.2
      have hOtherRank :
          ∀ w : Fin n, w ≠ u → w ≠ v → (C' w).1.rank = (C w).1.rank := by
        intro w hwu hwv
        show ((C.step P u v) w).1.rank = (C w).1.rank
        simp [P, Config.step, huv, hwu, hwv]
      unfold wrongLowBCount
      apply Finset.card_le_card
      intro w hw
      rw [wrongLowBSet, Finset.mem_filter] at hw
      rw [wrongLowBSet, Finset.mem_filter]
      rcases hw with ⟨_, hwB, hwLow⟩
      rw [hInput w] at hwB
      refine ⟨Finset.mem_univ _, hwB, ?_⟩
      by_cases hwu : w = u
      · subst w
        rw [huRank, hnA] at hwLow
        have hltRank : (C u).1.rank.val < (C v).1.rank.val := by
          exact_mod_cast hswap.1
        omega
      · by_cases hwv : w = v
        · subst w
          rw [hswap.2.2] at hwB
          cases hwB
        · rw [hOtherRank w hwu hwv, hnA] at hwLow
          exact hwLow
    · have hRanks := transitionPEM_rank_of_no_swap
        (n := n) (trank := trank) (Rmax := Rmax)
        (rankDelta := rankDelta) hRankDelta
        (s₀ := (C u).1) (s₁ := (C v).1)
        (x₀ := (C u).2) (x₁ := (C v).2)
        (hSrank.allSettled u) (hSrank.allSettled v) hswap hRankNe
      have huRank : (C' u).1.rank = (C u).1.rank := by
        show ((C.step P u v) u).1.rank = (C u).1.rank
        simp only [P, Config.step, if_neg huv, if_pos rfl]
        exact hRanks.1
      have hvRank : (C' v).1.rank = (C v).1.rank := by
        show ((C.step P u v) v).1.rank = (C v).1.rank
        simp only [P, Config.step, if_neg huv, if_neg (Ne.symm huv), if_pos rfl]
        exact hRanks.2
      have hOtherRank :
          ∀ w : Fin n, w ≠ u → w ≠ v → (C' w).1.rank = (C w).1.rank := by
        intro w hwu hwv
        show ((C.step P u v) w).1.rank = (C w).1.rank
        simp [P, Config.step, huv, hwu, hwv]
      unfold wrongLowBCount
      apply Finset.card_le_card
      intro w hw
      rw [wrongLowBSet, Finset.mem_filter] at hw
      rw [wrongLowBSet, Finset.mem_filter]
      rcases hw with ⟨_, hwB, hwLow⟩
      rw [hInput w] at hwB
      refine ⟨Finset.mem_univ _, hwB, ?_⟩
      by_cases hwu : w = u
      · subst w
        rw [huRank, hnA] at hwLow
        exact hwLow
      · by_cases hwv : w = v
        · subst w
          rw [hvRank, hnA] at hwLow
          exact hwLow
        · rw [hOtherRank w hwu hwv, hnA] at hwLow
          exact hwLow

/-- Every low-side B / high-side A ordered pair is a good scheduler pair for
the single-side misplaced-count potential. -/
theorem wrongLowB_product_wrongHighA_subset_GoodPairs_wrongLowBCount
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (wrongLowBSet C).product (wrongHighASet C) ⊆
      Probability.GoodPairs
        (protocolPEM n trank Rmax rankDelta) wrongLowBCount C := by
  intro p hp
  rcases p with ⟨u, v⟩
  have hp' := Finset.mem_product.mp hp
  rcases hp' with ⟨hu, hv⟩
  rw [wrongLowBSet, Finset.mem_filter] at hu
  rw [wrongHighASet, Finset.mem_filter] at hv
  have huv : u ≠ v := by
    intro huv
    subst v
    rw [hu.2.1] at hv
    cases hv.2.1
  exact (Probability.mem_GoodPairs
    (protocolPEM n trank Rmax rankDelta) wrongLowBCount C (u, v)).mpr
      ⟨huv,
        wrongLowBCount_decreases_step_at_wrongLowB_wrongHighA
          (trank := trank) (Rmax := Rmax) hRankDelta hSrank
          (by
            rw [wrongLowBSet, Finset.mem_filter]
            exact hu)
          (by
            rw [wrongHighASet, Finset.mem_filter]
            exact hv)⟩

/-- Product-form lower bound on scheduler pairs that decrease the single-side
misplaced-count potential. -/
theorem wrongLowB_mul_wrongHighA_le_GoodPairs_wrongLowBCount_card
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    wrongLowBCount C * wrongHighACount C ≤
      (Probability.GoodPairs
        (protocolPEM n trank Rmax rankDelta) wrongLowBCount C).card := by
  unfold wrongLowBCount wrongHighACount
  rw [← Finset.card_product]
  exact Finset.card_le_card
    (wrongLowB_product_wrongHighA_subset_GoodPairs_wrongLowBCount
      (trank := trank) (Rmax := Rmax) hRankDelta hSrank)

/-- Square-form lower bound on scheduler pairs that decrease the single-side
misplaced-count potential. -/
theorem wrongLowB_square_le_GoodPairs_wrongLowBCount_card
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    wrongLowBCount C * wrongLowBCount C ≤
      (Probability.GoodPairs
        (protocolPEM n trank Rmax rankDelta) wrongLowBCount C).card := by
  have hEq : wrongHighACount C = wrongLowBCount C :=
    (wrongLowBCount_eq_wrongHighACount_of_InSrank hSrank).symm
  simpa [hEq] using
    (wrongLowB_mul_wrongHighA_le_GoodPairs_wrongLowBCount_card
      (trank := trank) (Rmax := Rmax) hRankDelta hSrank)

/-- One-step scheduler mass of side-potential progress pairs is at least
`i^2 / (n * (n - 1))`, with `i = wrongLowBCount C`. -/
theorem wrongLowB_square_sideGoodPairs_mass_lower_bound
    {n trank Rmax : ℕ} (hn : 2 ≤ n)
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.pairSetMass n hn
        (Probability.GoodPairs
          (protocolPEM n trank Rmax rankDelta) wrongLowBCount C) := by
  rw [Probability.pairSetMass_GoodPairs]
  exact mul_le_mul_left
    (by exact_mod_cast
      wrongLowB_square_le_GoodPairs_wrongLowBCount_card hRankDelta hSrank)
    (((n * (n - 1) : ℕ) : ENNReal)⁻¹)

/-- PEM specialization of the side-potential square-form scheduler mass
bound. -/
theorem PEM_wrongLowB_square_sideGoodPairs_mass_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.pairSetMass n hn2
        (Probability.GoodPairs
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) wrongLowBCount C) := by
  simpa [PEMProtocolCoupled, PEMProtocol] using
    (wrongLowB_square_sideGoodPairs_mass_lower_bound
      (n := n) (trank := Rmax) (Rmax := Rmax) hn2
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hSrank)

/-- One-step probability form of the side-potential square lower bound. -/
theorem PEM_wrongLowB_one_step_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C) 1 := by
  classical
  rw [Probability.ProbHitWithin_one_eq_pairSetMass_GoodPairs]
  exact PEM_wrongLowB_square_sideGoodPairs_mass_lower_bound
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank

/-- Nonzero-window form of the side-potential square lower bound. -/
theorem PEM_wrongLowB_window_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) {t : ℕ} (ht : 1 ≤ t) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C) t := by
  exact Probability.ProbHitWithin_lower_bound_of_one_lower_bound
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
    (fun D => wrongLowBCount D < wrongLowBCount C) ht
    (PEM_wrongLowB_one_step_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank)

/-- Phase-B square-form progress bound.

This is the bound needed for Kanaya Lemma 7.  At misplaced-side level
`k = wrongLowBCount C`, the one-step probability of decreasing the swap
potential is at least `k^2 / (n * (n - 1))`.  Using the linear
`misorderedCount / (n * (n - 1))` bound instead would introduce a harmonic
sum and only give an `O(n^2 log n)` sequential expectation. -/
theorem PEM_swap_phase_wrongLowB_square_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C) 1 := by
  exact PEM_wrongLowB_one_step_descent_prob_lower_bound
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank

/-- If the single-side misplaced count is positive, at least one ordered pair
strictly decreases it in one random interaction. -/
theorem PEM_wrongLowB_positive_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hpos : 0 < wrongLowBCount C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C) 1 := by
  have hcount : (1 : ENNReal) ≤
      ((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) := by
    have hsq : 1 ≤ wrongLowBCount C * wrongLowBCount C := by
      nlinarith [hpos]
    exact_mod_cast hsq
  calc
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹
        = (1 : ENNReal) *
            ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by simp
    _ ≤ ((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
          exact mul_le_mul_left hcount _
    _ ≤ Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C) 1 :=
          PEM_wrongLowB_one_step_descent_prob_lower_bound
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank

/-- Nonzero-window version of
`PEM_wrongLowB_positive_descent_prob_lower_bound`. -/
theorem PEM_wrongLowB_positive_window_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hpos : 0 < wrongLowBCount C)
    {t : ℕ} (ht : 1 ≤ t) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C) t := by
  exact Probability.ProbHitWithin_lower_bound_of_one_lower_bound
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
    (fun D => wrongLowBCount D < wrongLowBCount C) ht
    (PEM_wrongLowB_positive_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank hpos)

/-- Swap-phase entry form: every `Srank` state outside `Sswap` has at least
one scheduler pair that decreases the single-side misplaced count. -/
theorem PEM_swap_not_done_wrongLowB_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hNotSwap : ¬ InSswap C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C) 1 := by
  exact PEM_wrongLowB_positive_descent_prob_lower_bound
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn2 hn0 hSrank
    (wrongLowBCount_pos_of_InSrank_not_InSswap hSrank hNotSwap)

/-- Nonzero-window version of
`PEM_swap_not_done_wrongLowB_descent_prob_lower_bound`. -/
theorem PEM_swap_not_done_wrongLowB_window_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hNotSwap : ¬ InSswap C)
    {t : ℕ} (ht : 1 ≤ t) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C) t := by
  exact Probability.ProbHitWithin_lower_bound_of_one_lower_bound
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
    (fun D => wrongLowBCount D < wrongLowBCount C) ht
    (PEM_swap_not_done_wrongLowB_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hSrank hNotSwap)

/-- Marginal one-step version of
`PEM_wrongLowB_positive_descent_prob_lower_bound`, for phase composition.
The strict-descent target is false at the start state. -/
theorem PEM_wrongLowB_positive_descent_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hpos : 0 < wrongLowBCount C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by infer_instance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => wrongLowBCount D < wrongLowBCount C
  have hGoal : ¬ Goal C := by
    intro h
    exact Nat.lt_irrefl _ h
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_wrongLowB_positive_descent_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hSrank hpos)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-- Marginal one-step swap-phase entry form: every `Srank` state outside
`Sswap` has one-step endpoint probability at least one ordered pair of
strictly decreasing the side misplaced-count potential. -/
theorem PEM_swap_not_done_wrongLowB_descent_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hNotSwap : ¬ InSswap C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by infer_instance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C)
        (by classical exact inferInstance) 1 := by
  exact PEM_wrongLowB_positive_descent_probReached_lower_bound
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn2 hn0 hSrank
    (wrongLowBCount_pos_of_InSrank_not_InSswap hSrank hNotSwap)

/-- Every low-side B paired with every high-side A is a misordered pair. -/
theorem wrongLowB_product_wrongHighA_subset_misorderedSet
    {C : Config (AgentState n) Opinion n} :
    (wrongLowBSet C).product (wrongHighASet C) ⊆ misorderedSet C := by
  intro p hp
  rcases p with ⟨u, v⟩
  have hp' := Finset.mem_product.mp hp
  rcases hp' with ⟨hu, hv⟩
  rw [wrongLowBSet, Finset.mem_filter] at hu
  rw [wrongHighASet, Finset.mem_filter] at hv
  rcases hu with ⟨_, huB, huLow⟩
  rcases hv with ⟨_, hvA, hvHigh⟩
  exact mem_misorderedSet.mpr ⟨huB, hvA, by omega⟩

/-- Product-form lower bound on the number of misordered pairs. -/
theorem wrongLowB_mul_wrongHighA_le_misorderedCount
    {C : Config (AgentState n) Opinion n} :
    wrongLowBCount C * wrongHighACount C ≤ misorderedCount C := by
  unfold wrongLowBCount wrongHighACount misorderedCount
  rw [← Finset.card_product]
  exact Finset.card_le_card wrongLowB_product_wrongHighA_subset_misorderedSet

/-- Every currently misordered ordered pair is a good scheduler pair for the
`misorderedCount` potential. -/
theorem misorderedSet_subset_GoodPairs_misorderedCount
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    misorderedSet C ⊆
      Probability.GoodPairs
        (protocolPEM n trank Rmax rankDelta) misorderedCount C := by
  intro p hp
  rcases p with ⟨u, v⟩
  have hMis : MisorderedPair C (u, v) := mem_misorderedSet.mp hp
  rcases hMis with ⟨huB, hvA, hlt⟩
  have huv : u ≠ v := by
    intro huv
    subst v
    rw [huB] at hvA
    cases hvA
  exact (Probability.mem_GoodPairs
    (protocolPEM n trank Rmax rankDelta) misorderedCount C (u, v)).mpr
      ⟨huv, misorderedCount_decreases_step_at_misorder
        hRankDelta hSrank ⟨huB, hvA, hlt⟩⟩

/-- The number of good scheduler pairs is at least the current
`misorderedCount`. -/
theorem misorderedCount_le_GoodPairs_card
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    misorderedCount C ≤
      (Probability.GoodPairs
        (protocolPEM n trank Rmax rankDelta) misorderedCount C).card := by
  unfold misorderedCount
  exact Finset.card_le_card
    (misorderedSet_subset_GoodPairs_misorderedCount hRankDelta hSrank)

/-- Product-form lower bound on swap-progress scheduler pairs. -/
theorem wrongLowB_mul_wrongHighA_le_GoodPairs_card
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    wrongLowBCount C * wrongHighACount C ≤
      (Probability.GoodPairs
        (protocolPEM n trank Rmax rankDelta) misorderedCount C).card := by
  exact (wrongLowB_mul_wrongHighA_le_misorderedCount (C := C)).trans
    (misorderedCount_le_GoodPairs_card hRankDelta hSrank)

/-- Square-form lower bound on swap-progress scheduler pairs.  Here
`wrongLowBCount` is the common misplaced-side count in an `Srank`
configuration. -/
theorem wrongLowB_square_le_GoodPairs_card
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    wrongLowBCount C * wrongLowBCount C ≤
      (Probability.GoodPairs
        (protocolPEM n trank Rmax rankDelta) misorderedCount C).card := by
  have hEq : wrongHighACount C = wrongLowBCount C :=
    (wrongLowBCount_eq_wrongHighACount_of_InSrank hSrank).symm
  simpa [hEq] using
    (wrongLowB_mul_wrongHighA_le_GoodPairs_card
      (trank := trank) (Rmax := Rmax) hRankDelta hSrank)

/-- One-step scheduler mass of swap-progress pairs is at least
`misorderedCount / (n * (n - 1))`. -/
theorem misordered_goodPairs_mass_lower_bound
    {n trank Rmax : ℕ} (hn : 2 ≤ n)
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    ((misorderedCount C : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.pairSetMass n hn
        (Probability.GoodPairs
          (protocolPEM n trank Rmax rankDelta) misorderedCount C) := by
  rw [Probability.pairSetMass_GoodPairs]
  exact mul_le_mul_left
    (by exact_mod_cast
      misorderedCount_le_GoodPairs_card hRankDelta hSrank)
    (((n * (n - 1) : ℕ) : ENNReal)⁻¹)

/-- Specialization of the swap good-pair mass lower bound to the PEM protocol
family used in the time-bound theorem. -/
theorem PEM_misordered_goodPairs_mass_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    ((misorderedCount C : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.pairSetMass n hn2
        (Probability.GoodPairs
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) misorderedCount C) := by
  simpa [PEMProtocolCoupled, PEMProtocol] using
    (misordered_goodPairs_mass_lower_bound
      (n := n) (trank := Rmax) (Rmax := Rmax) hn2
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hSrank)

/-- One-step probability form of the linear `misorderedCount` good-pair
lower bound. -/
theorem PEM_misordered_one_step_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    ((misorderedCount C : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => misorderedCount D < misorderedCount C) 1 := by
  classical
  rw [Probability.ProbHitWithin_one_eq_pairSetMass_GoodPairs]
  exact PEM_misordered_goodPairs_mass_lower_bound
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank

/-- Nonzero-window form of the linear `misorderedCount` lower bound. -/
theorem PEM_misordered_window_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) {t : ℕ} (ht : 1 ≤ t) :
    ((misorderedCount C : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => misorderedCount D < misorderedCount C) t := by
  exact Probability.ProbHitWithin_lower_bound_of_one_lower_bound
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
    (fun D => misorderedCount D < misorderedCount C) ht
    (PEM_misordered_one_step_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank)

/-- If an `Srank` configuration has a positive misordered count, the one-step
probability of strictly decreasing that count is at least the mass of one
ordered scheduler pair. -/
theorem PEM_misordered_positive_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hpos : 0 < misorderedCount C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => misorderedCount D < misorderedCount C) 1 := by
  have hcount : (1 : ENNReal) ≤ (misorderedCount C : ENNReal) := by
    exact_mod_cast hpos
  calc
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹
        = (1 : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by simp
    _ ≤ (misorderedCount C : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
          exact mul_le_mul_left hcount _
    _ ≤ Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => misorderedCount D < misorderedCount C) 1 :=
          PEM_misordered_one_step_descent_prob_lower_bound
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank

/-- Nonzero-window version of `PEM_misordered_positive_descent_prob_lower_bound`. -/
theorem PEM_misordered_positive_window_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hpos : 0 < misorderedCount C)
    {t : ℕ} (ht : 1 ≤ t) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => misorderedCount D < misorderedCount C) t := by
  exact Probability.ProbHitWithin_lower_bound_of_one_lower_bound
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
    (fun D => misorderedCount D < misorderedCount C) ht
    (PEM_misordered_positive_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank hpos)

/-- One-step scheduler mass of swap-progress pairs is at least the Kanaya
square-form lower bound `i^2 / (n * (n - 1))`, where `i` is the common
misplaced-side count. -/
theorem wrongLowB_square_goodPairs_mass_lower_bound
    {n trank Rmax : ℕ} (hn : 2 ≤ n)
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.pairSetMass n hn
        (Probability.GoodPairs
          (protocolPEM n trank Rmax rankDelta) misorderedCount C) := by
  rw [Probability.pairSetMass_GoodPairs]
  exact mul_le_mul_left
    (by exact_mod_cast
      wrongLowB_square_le_GoodPairs_card hRankDelta hSrank)
    (((n * (n - 1) : ℕ) : ENNReal)⁻¹)

/-- PEM specialization of the square-form swap good-pair mass lower bound. -/
theorem PEM_wrongLowB_square_goodPairs_mass_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.pairSetMass n hn2
        (Probability.GoodPairs
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) misorderedCount C) := by
  simpa [PEMProtocolCoupled, PEMProtocol] using
    (wrongLowB_square_goodPairs_mass_lower_bound
      (n := n) (trank := Rmax) (Rmax := Rmax) hn2
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hSrank)

/-- One-step probability form of the Kanaya square lower bound for swap
progress measured by `misorderedCount`. -/
theorem PEM_wrongLowB_square_swap_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => misorderedCount D < misorderedCount C) 1 := by
  classical
  rw [Probability.ProbHitWithin_one_eq_pairSetMass_GoodPairs]
  exact PEM_wrongLowB_square_goodPairs_mass_lower_bound
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank

/-- Nonzero-window form of the Kanaya square lower bound for swap progress. -/
theorem PEM_wrongLowB_square_swap_window_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) {t : ℕ} (ht : 1 ≤ t) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => misorderedCount D < misorderedCount C) t := by
  exact Probability.ProbHitWithin_lower_bound_of_one_lower_bound
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
    (fun D => misorderedCount D < misorderedCount C) ht
    (PEM_wrongLowB_square_swap_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank)

/-- Marginal one-step version of the Kanaya square lower bound for swap
progress measured by `misorderedCount`. -/
theorem PEM_wrongLowB_square_swap_descent_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by infer_instance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => misorderedCount D < misorderedCount C)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => misorderedCount D < misorderedCount C
  have hGoal : ¬ Goal C := by
    intro h
    exact Nat.lt_irrefl _ h
  have hhit :
      (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_wrongLowB_square_swap_descent_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hSrank)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

end SSEM
