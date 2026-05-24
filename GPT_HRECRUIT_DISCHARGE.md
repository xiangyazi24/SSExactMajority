I’ll sanity-check the majority-opinion child shortcut first, since it likely needs stronger ranking-phase counting hypotheses before it can discharge hRecruit.

The shortcut is false as stated: ¬ InSrank and ResAns do not ensure an unsettled majority-opinion agent. It needs a median-slot counting hypothesis.

I would not try to prove the simplified theorem as stated. It is false with the listed hypotheses. The uploaded note correctly says the median recruit is unsafe when the child has minority opinion, and proposes choosing a majority-opinion child for the median slot instead. 

Pasted markdown

 But the proposed lemma

lean
¬ InSrank C →
ResAns m₀ C →
m₀ = majorityAnswer C →
4 ≤ n →
∃ child, (C child).1.role = .Unsettled ∧ (C child).2 = majorityOpinion C

does not follow. ¬ InSrank C only says ranking is unfinished; it does not say fewer than half the agents have already been recruited, nor that a majority-opinion agent remains unsettled. The uploaded task itself notes that the real counting argument is “at the time median rank is filled,” not at every non-ranked state. 

Pasted markdown

A typical counterexample shape is:

lean
-- n = 5
-- 3 agents have opinion .A, 2 have opinion .B
-- majorityAnswer C = .outA
-- all answers are .outA, so ResAns .outA C holds
-- all .A agents are already Settled
-- one .B agent remains Unsettled
-- C is not InSrank because some agent is Unsettled
--
-- Then there is no Unsettled child with majorityOpinion C = .A.

So the theorem you can actually use is this strengthened counting lemma:

lean
open Classical

def majorityOpinion {n : ℕ} (C : Config (AgentState n) Opinion n) : Opinion :=
  match majorityAnswer C with
  | .outA => .A
  | .outB => .B
  | .outT => .A   -- arbitrary; not used in strict-majority cases
  | .phi  => .A   -- arbitrary; majorityAnswer should not be .phi in ranked phase

private def settledSet {n : ℕ} (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter fun w => (C w).1.role = .Settled

private def majorityOpinionSet {n : ℕ} (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter fun w => (C w).2 = majorityOpinion C

lemma exists_majority_opinion_unsettled_of_settled_lt_majority
    {n : ℕ}
    {C : Config (AgentState n) Opinion n}
    (hRoles :
      ∀ w : Fin n,
        (C w).1.role = .Settled ∨ (C w).1.role = .Unsettled)
    (hlt :
      (settledSet C).card < (majorityOpinionSet C).card) :
    ∃ child : Fin n,
      (C child).1.role = .Unsettled ∧
      (C child).2 = majorityOpinion C := by
  classical

  by_contra hnone
  push_neg at hnone
  -- hnone :
  --   ∀ child, (C child).1.role = .Unsettled →
  --     (C child).2 ≠ majorityOpinion C

  have hsub : majorityOpinionSet C ⊆ settledSet C := by
    intro w hw
    simp [majorityOpinionSet] at hw
    have hMaj : (C w).2 = majorityOpinion C := hw

    rcases hRoles w with hSettled | hUnsettled
    · simp [settledSet, hSettled]
    · have hNotMaj := hnone w hUnsettled
      contradiction

  have hcard : (majorityOpinionSet C).card ≤ (settledSet C).card :=
    Finset.card_le_card hsub

  exact Nat.not_lt_of_ge hcard hlt

Now specialize this to the median slot. This is the lemma that replaces the false exists_majority_opinion_unsettled.

lean
lemma exists_majority_opinion_unsettled_at_median_slot
    {n : ℕ}
    {C : Config (AgentState n) Opinion n}
    (hn : 0 < n)
    (hRoles :
      ∀ w : Fin n,
        (C w).1.role = .Settled ∨ (C w).1.role = .Unsettled)
    -- Ranking-prefix invariant from the ranking driver:
    -- the number of settled agents is exactly the number of already-filled ranks.
    (hSettledCount :
      (settledSet C).card = ceilHalf n - 1)
    -- Strict-majority counting fact:
    -- in the odd median case, the majority side has at least ceilHalf n agents.
    (hMajCount :
      ceilHalf n ≤ (majorityOpinionSet C).card) :
    ∃ child : Fin n,
      (C child).1.role = .Unsettled ∧
      (C child).2 = majorityOpinion C := by
  classical

  apply exists_majority_opinion_unsettled_of_settled_lt_majority
    (C := C) hRoles

  rw [hSettledCount]

  have hceil_pos : 0 < ceilHalf n := by
    exact ceilHalf_pos hn

  omega

For even non-tie, you need the same lemma twice: once for the lower median slot and once for the upper median slot. The settled counts are n / 2 - 1 and n / 2, and strict majority gives n / 2 + 1 ≤ majorityOpinionSet.card.

lean
lemma exists_majority_opinion_unsettled_at_even_lower_median_slot
    {n : ℕ}
    {C : Config (AgentState n) Opinion n}
    (hn : 0 < n)
    (heven : n % 2 = 0)
    (hRoles :
      ∀ w : Fin n,
        (C w).1.role = .Settled ∨ (C w).1.role = .Unsettled)
    (hSettledCount :
      (settledSet C).card = n / 2 - 1)
    (hMajCount :
      n / 2 + 1 ≤ (majorityOpinionSet C).card) :
    ∃ child : Fin n,
      (C child).1.role = .Unsettled ∧
      (C child).2 = majorityOpinion C := by
  classical
  apply exists_majority_opinion_unsettled_of_settled_lt_majority
    (C := C) hRoles
  rw [hSettledCount]
  omega

lemma exists_majority_opinion_unsettled_at_even_upper_median_slot
    {n : ℕ}
    {C : Config (AgentState n) Opinion n}
    (hn : 0 < n)
    (heven : n % 2 = 0)
    (hRoles :
      ∀ w : Fin n,
        (C w).1.role = .Settled ∨ (C w).1.role = .Unsettled)
    (hSettledCount :
      (settledSet C).card = n / 2)
    (hMajCount :
      n / 2 + 1 ≤ (majorityOpinionSet C).card) :
    ∃ child : Fin n,
      (C child).1.role = .Unsettled ∧
      (C child).2 = majorityOpinion C := by
  classical
  apply exists_majority_opinion_unsettled_of_settled_lt_majority
    (C := C) hRoles
  rw [hSettledCount]
  omega

You also want this simp lemma:

lean
lemma opinionToAnswer_majorityOpinion_eq_majorityAnswer
    {n : ℕ}
    {C : Config (AgentState n) Opinion n}
    (hMaj :
      majorityAnswer C = .outA ∨ majorityAnswer C = .outB) :
    opinionToAnswer (majorityOpinion C) = majorityAnswer C := by
  classical
  unfold majorityOpinion
  rcases hMaj with hA | hB
  · simp [hA]
  · simp [hB]

And a version with m₀:

lean
lemma opinionToAnswer_majorityOpinion_eq_m0
    {n : ℕ}
    {C : Config (AgentState n) Opinion n}
    {m₀ : Answer}
    (hm0 : m₀ = majorityAnswer C)
    (hMaj :
      majorityAnswer C = .outA ∨ majorityAnswer C = .outB) :
    opinionToAnswer (majorityOpinion C) = m₀ := by
  rw [opinionToAnswer_majorityOpinion_eq_majorityAnswer hMaj]
  exact hm0.symm

Now the hRecruit discharge should be split by whether the recruit target is median.

The non-median case is the easy case from your green lemma:

lean
lemma recruit_pair_safe_nonmedian
    {n Rmax Emax Dmax : ℕ}
    {hn : 0 < n}
    {m₀ : Answer}
    {C : Config (AgentState n) Opinion n}
    {parent child : Fin n}
    (hResAns : ResAns m₀ C)
    (hRecruitable : RecruitablePair C parent child)
    -- This should be whatever your rank-target predicate is.
    (hNoMedianTarget :
      let r := recruitTargetRank C parent child
      r.val + 1 ≠ ceilHalf n ∧
      (n % 2 = 0 →
        r.val + 1 ≠ n / 2 ∧ r.val + 1 ≠ n / 2 + 1)) :
    PairResAnsSafe m₀
      (transitionPEM
        n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)
        (C parent, C child)) := by
  classical

  let Δ := rankDeltaOSSR Rmax Emax Dmax hn
  let out := transitionPEM n Rmax Rmax Δ (C parent, C child)

  have hAnsPres :
      out.1.1.answer = (C parent).1.answer ∧
      out.2.1.answer = (C child).1.answer := by
    exact transitionPEM_recruit_ba_answer_inert_of_no_median
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn)
      (C := C)
      (parent := parent)
      (child := child)
      hRecruitable
      hNoMedianTarget

  constructor
  · -- parent output answer safe
    rw [hAnsPres.1]
    exact hResAns parent
  · -- child output answer safe
    rw [hAnsPres.2]
    exact hResAns child

For the odd median slot, choose the majority-opinion child and prove the child output answer is m₀.

lean
lemma recruit_pair_safe_odd_median_majority_child
    {n Rmax Emax Dmax : ℕ}
    {hn : 0 < n}
    {m₀ : Answer}
    {C : Config (AgentState n) Opinion n}
    {parent child : Fin n}
    (hodd : n % 2 = 1)
    (hm0 : m₀ = majorityAnswer C)
    (hMaj :
      majorityAnswer C = .outA ∨ majorityAnswer C = .outB)
    (hResAns : ResAns m₀ C)
    (hRecruitable : RecruitablePair C parent child)
    (hChildMaj : (C child).2 = majorityOpinion C)
    -- The recruit gives child the odd median rank.
    (hChildTarget :
      (recruitTargetRank C parent child).val + 1 = ceilHalf n) :
    PairResAnsSafe m₀
      (transitionPEM
        n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)
        (C parent, C child)) := by
  classical

  let Δ := rankDeltaOSSR Rmax Emax Dmax hn
  let out := transitionPEM n Rmax Rmax Δ (C parent, C child)

  have hParentAns :
      out.1.1.answer = (C parent).1.answer := by
    exact transitionPEM_recruit_ba_parent_answer_preserved
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn)
      (C := C)
      (parent := parent)
      (child := child)
      hRecruitable

  have hChildAns :
      out.2.1.answer = opinionToAnswer (C child).2 := by
    exact transitionPEM_recruit_ba_child_answer_median_odd
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn)
      (hodd := hodd)
      (C := C)
      (parent := parent)
      (child := child)
      hRecruitable
      hChildTarget

  constructor
  · rw [hParentAns]
    exact hResAns parent
  · left
    calc
      out.2.1.answer
          = opinionToAnswer (C child).2 := hChildAns
      _   = opinionToAnswer (majorityOpinion C) := by rw [hChildMaj]
      _   = m₀ := opinionToAnswer_majorityOpinion_eq_m0
              (C := C) (m₀ := m₀) hm0 hMaj

For even non-tie median slots, use the same pattern. The only difference is the median predicate and the answer lemma:

lean
lemma recruit_pair_safe_even_median_majority_child
    {n Rmax Emax Dmax : ℕ}
    {hn : 0 < n}
    {m₀ : Answer}
    {C : Config (AgentState n) Opinion n}
    {parent child : Fin n}
    (heven : n % 2 = 0)
    (hne : nAOf C ≠ nBOf C)
    (hm0 : m₀ = majorityAnswer C)
    (hMaj :
      majorityAnswer C = .outA ∨ majorityAnswer C = .outB)
    (hResAns : ResAns m₀ C)
    (hRecruitable : RecruitablePair C parent child)
    (hChildMaj : (C child).2 = majorityOpinion C)
    (hChildTarget :
      (recruitTargetRank C parent child).val + 1 = n / 2 ∨
      (recruitTargetRank C parent child).val + 1 = n / 2 + 1) :
    PairResAnsSafe m₀
      (transitionPEM
        n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)
        (C parent, C child)) := by
  classical

  let Δ := rankDeltaOSSR Rmax Emax Dmax hn
  let out := transitionPEM n Rmax Rmax Δ (C parent, C child)

  have hParentAns :
      out.1.1.answer = (C parent).1.answer := by
    exact transitionPEM_recruit_ba_parent_answer_preserved
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn)
      (C := C)
      (parent := parent)
      (child := child)
      hRecruitable

  have hChildAns :
      out.2.1.answer = opinionToAnswer (C child).2 := by
    exact transitionPEM_recruit_ba_child_answer_median_even_not_tie
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn)
      (heven := heven)
      (hne := hne)
      (C := C)
      (parent := parent)
      (child := child)
      hRecruitable
      hChildTarget

  constructor
  · rw [hParentAns]
    exact hResAns parent
  · left
    calc
      out.2.1.answer
          = opinionToAnswer (C child).2 := hChildAns
      _   = opinionToAnswer (majorityOpinion C) := by rw [hChildMaj]
      _   = m₀ := opinionToAnswer_majorityOpinion_eq_m0
              (C := C) (m₀ := m₀) hm0 hMaj

Even tie is separate: the median decision writes .outT, so no majority-opinion child is needed.

lean
lemma recruit_pair_safe_even_median_tie
    {n Rmax Emax Dmax : ℕ}
    {hn : 0 < n}
    {m₀ : Answer}
    {C : Config (AgentState n) Opinion n}
    {parent child : Fin n}
    (heven : n % 2 = 0)
    (htie : nAOf C = nBOf C)
    (hm0 : m₀ = majorityAnswer C)
    (hResAns : ResAns m₀ C)
    (hRecruitable : RecruitablePair C parent child)
    (hChildTarget :
      (recruitTargetRank C parent child).val + 1 = n / 2 ∨
      (recruitTargetRank C parent child).val + 1 = n / 2 + 1) :
    PairResAnsSafe m₀
      (transitionPEM
        n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)
        (C parent, C child)) := by
  classical

  let Δ := rankDeltaOSSR Rmax Emax Dmax hn
  let out := transitionPEM n Rmax Rmax Δ (C parent, C child)

  have hParentAns :
      out.1.1.answer = (C parent).1.answer := by
    exact transitionPEM_recruit_ba_parent_answer_preserved
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn)
      (C := C)
      (parent := parent)
      (child := child)
      hRecruitable

  have hChildAns :
      out.2.1.answer = .outT := by
    exact transitionPEM_recruit_ba_child_answer_median_even_tie
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn)
      (heven := heven)
      (htie := htie)
      (C := C)
      (parent := parent)
      (child := child)
      hRecruitable
      hChildTarget

  have hMajT : majorityAnswer C = .outT := by
    exact majorityAnswer_eq_outT_of_even_tie
      (C := C) heven htie

  constructor
  · rw [hParentAns]
    exact hResAns parent
  · left
    calc
      out.2.1.answer = .outT := hChildAns
      _ = majorityAnswer C := hMajT.symm
      _ = m₀ := hm0.symm

Then your scheduler-side safe-recruit selection should look like this:

lean
lemma exists_answer_safe_recruit_pair_for_ranking_step
    {n Rmax Emax Dmax : ℕ}
    {hn : 0 < n}
    {m₀ : Answer}
    {C : Config (AgentState n) Opinion n}
    (hNotRank : ¬ InSrank C)
    (hPrefix : RankingPrefixInvariant C)
    (hRoles :
      ∀ w : Fin n,
        (C w).1.role = .Settled ∨ (C w).1.role = .Unsettled)
    (hResAns : ResAns m₀ C)
    (hm0 : m₀ = majorityAnswer C) :
    ∃ parent child : Fin n,
      RecruitablePair C parent child ∧
      PairResAnsSafe m₀
        (transitionPEM
          n Rmax Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)
          (C parent, C child)) := by
  classical

  -- Existing structural ranking lemma:
  obtain ⟨parent, hParent⟩ :=
    exists_recruiting_parent_from_not_InSrank
      (C := C) hPrefix hNotRank

  let target := nextRecruitTargetRank C parent

  by_cases hOdd : n % 2 = 1

  · by_cases hMedian : target.val + 1 = ceilHalf n

    · -- Odd median slot: choose majority-opinion child.
      have hSettledCount :
          (settledSet C).card = ceilHalf n - 1 := by
        exact hPrefix.settled_count_before_odd_median
          hOdd hMedian

      have hMajCount :
          ceilHalf n ≤ (majorityOpinionSet C).card := by
        exact hPrefix.majority_count_ge_ceilHalf_odd
          hOdd hm0

      obtain ⟨child, hChildUnsettled, hChildMaj⟩ :=
        exists_majority_opinion_unsettled_at_median_slot
          (C := C)
          hn
          hRoles
          hSettledCount
          hMajCount

      have hRecruitable : RecruitablePair C parent child := by
        exact hParent.recruitable_with_unsettled_child child hChildUnsettled

      refine ⟨parent, child, hRecruitable, ?_⟩

      have hMajOut :
          majorityAnswer C = .outA ∨ majorityAnswer C = .outB := by
        exact majorityAnswer_strict_of_odd
          (C := C) hOdd hn

      exact recruit_pair_safe_odd_median_majority_child
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn)
        (hodd := hOdd)
        (hm0 := hm0)
        (hMaj := hMajOut)
        (hResAns := hResAns)
        (hRecruitable := hRecruitable)
        (hChildMaj := hChildMaj)
        (hChildTarget := by
          -- connect `target` to `recruitTargetRank C parent child`
          exact hPrefix.recruitTargetRank_eq_nextTarget parent child hRecruitable ▸ hMedian)

    · -- Odd non-median slot: any unsettled child is safe.
      obtain ⟨child, hChildUnsettled⟩ :=
        exists_unsettled_child_from_not_InSrank
          (C := C) hPrefix hNotRank

      have hRecruitable : RecruitablePair C parent child := by
        exact hParent.recruitable_with_unsettled_child child hChildUnsettled

      refine ⟨parent, child, hRecruitable, ?_⟩

      apply recruit_pair_safe_nonmedian
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn)
        (hResAns := hResAns)
        (hRecruitable := hRecruitable)

      dsimp
      constructor
      · exact by
          rw [hPrefix.recruitTargetRank_eq_nextTarget parent child hRecruitable]
          exact hMedian
      · intro heven
        exfalso
        -- hOdd contradicts heven.
        exact Nat.mod_two_ne_zero_of_eq_one hOdd heven

  · have hEven : n % 2 = 0 := by
      exact Nat.mod_two_eq_zero_of_ne_one hOdd

    by_cases hTie : nAOf C = nBOf C

    · -- Even tie.
      by_cases hMedian :
          target.val + 1 = n / 2 ∨ target.val + 1 = n / 2 + 1

      · obtain ⟨child, hChildUnsettled⟩ :=
          exists_unsettled_child_from_not_InSrank
            (C := C) hPrefix hNotRank

        have hRecruitable : RecruitablePair C parent child := by
          exact hParent.recruitable_with_unsettled_child child hChildUnsettled

        refine ⟨parent, child, hRecruitable, ?_⟩

        exact recruit_pair_safe_even_median_tie
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          (hn := hn)
          (heven := hEven)
          (htie := hTie)
          (hm0 := hm0)
          (hResAns := hResAns)
          (hRecruitable := hRecruitable)
          (hChildTarget := by
            simpa [hPrefix.recruitTargetRank_eq_nextTarget parent child hRecruitable]
              using hMedian)

      · -- Even tie, non-median slot.
        obtain ⟨child, hChildUnsettled⟩ :=
          exists_unsettled_child_from_not_InSrank
            (C := C) hPrefix hNotRank

        have hRecruitable : RecruitablePair C parent child := by
          exact hParent.recruitable_with_unsettled_child child hChildUnsettled

        refine ⟨parent, child, hRecruitable, ?_⟩

        apply recruit_pair_safe_nonmedian
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          (hn := hn)
          (hResAns := hResAns)
          (hRecruitable := hRecruitable)

        dsimp
        constructor
        · -- not ceilHalf follows from not being lower/upper median;
          -- in even case ceilHalf should simplify to n/2 or n/2+1
          exact hPrefix.not_ceilHalf_of_not_even_median
            hEven hMedian
        · intro _
          exact hMedian

    · -- Even non-tie.
      by_cases hMedian :
          target.val + 1 = n / 2 ∨ target.val + 1 = n / 2 + 1

      · -- choose majority-opinion child.
        have hSettledCount :
            (settledSet C).card =
              if target.val + 1 = n / 2 then n / 2 - 1 else n / 2 := by
          exact hPrefix.settled_count_before_even_median
            hEven hMedian

        have hMajCount :
            n / 2 + 1 ≤ (majorityOpinionSet C).card := by
          exact hPrefix.majority_count_gt_half_even_not_tie
            hEven hTie hm0

        obtain ⟨child, hChildUnsettled, hChildMaj⟩ : ∃ child,
            (C child).1.role = .Unsettled ∧
            (C child).2 = majorityOpinion C := by
          rcases hMedian with hLower | hUpper
          · apply exists_majority_opinion_unsettled_at_even_lower_median_slot
              (C := C) hn hEven hRoles
          · apply exists_majority_opinion_unsettled_at_even_upper_median_slot
              (C := C) hn hEven hRoles
          all_goals
            · simpa [hLower, hUpper] using hSettledCount
            · exact hMajCount

        have hRecruitable : RecruitablePair C parent child := by
          exact hParent.recruitable_with_unsettled_child child hChildUnsettled

        refine ⟨parent, child, hRecruitable, ?_⟩

        have hMajOut :
            majorityAnswer C = .outA ∨ majorityAnswer C = .outB := by
          exact majorityAnswer_strict_of_even_not_tie
            (C := C) hEven hTie

        exact recruit_pair_safe_even_median_majority_child
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          (hn := hn)
          (heven := hEven)
          (hne := hTie)
          (hm0 := hm0)
          (hMaj := hMajOut)
          (hResAns := hResAns)
          (hRecruitable := hRecruitable)
          (hChildMaj := hChildMaj)
          (hChildTarget := by
            simpa [hPrefix.recruitTargetRank_eq_nextTarget parent child hRecruitable]
              using hMedian)

      · -- Even non-tie, non-median slot.
        obtain ⟨child, hChildUnsettled⟩ :=
          exists_unsettled_child_from_not_InSrank
            (C := C) hPrefix hNotRank

        have hRecruitable : RecruitablePair C parent child := by
          exact hParent.recruitable_with_unsettled_child child hChildUnsettled

        refine ⟨parent, child, hRecruitable, ?_⟩

        apply recruit_pair_safe_nonmedian
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          (hn := hn)
          (hResAns := hResAns)
          (hRecruitable := hRecruitable)

        dsimp
        constructor
        · exact hPrefix.not_ceilHalf_of_not_even_median
            hEven hMedian
        · intro _
          exact hMedian

The important replacement is:

lean
-- Do NOT try to prove this:
∀ parent child, RecruitablePair C parent child → PairResAnsSafe ...

-- Instead prove this:
∃ parent child, RecruitablePair C parent child ∧ PairResAnsSafe ...

If all_resetting_uniform_to_InSswap_ResAns really requires a universal hRecruit, the “choose a majority child” strategy cannot discharge it. Universal hRecruit still quantifies over the bad minority child at the odd median slot. To use this strategy, the ranking driver must choose recruit pairs from an existential safe-pair lemma like exists_answer_safe_recruit_pair_for_ranking_step.

That is why the endpoint-repair route remains cleaner: your own notes identify that non-median preservation is structural and that median correctness should be repaired at the InSswap endpoint rather than maintained through every recruit. 

Pasted markdown