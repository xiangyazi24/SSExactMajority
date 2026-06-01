import SSExactMajority.UpperBound.Time.Bridge

namespace SSEM

/-! ## transitionPEM role preservation for InSswap (Settled) agents -/

theorem transitionPEM_prePhase4_eq_of_settled_distinct
    {n : ℕ} {trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank) :
    transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁ = (s₀, s₁) := by
  unfold transitionPEM_prePhase4
  rw [hFix s₀ s₁ hs₀ hs₁ hne]
  simp [hs₀, hs₁]

theorem transitionPEM_role_settled_or_resetting_of_InSswap
    {n Rmax : ℕ} {trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank) :
    ((transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Settled ∨
      (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) ∧
    ((transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).2.role = .Settled ∨
      (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).2.role = .Resetting) := by
  simp only [transitionPEM]
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne]
  exact transitionPEM_phase4_role_settled_or_resetting hs₀ hs₁

/-! ## No mixed outcome: both Settled or both Resetting after phase4 -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000000 in
private theorem phase4_propagate_fst_resetting_of_settled
    {n Rmax : ℕ} {b₀ b₁ : AgentState n}
    (hs₀ : b₀.role = .Settled) (hs₁ : b₁.role = .Settled)
    (h : (phase4_propagate n Rmax b₀ b₁).1.role = .Resetting) :
    (phase4_propagate n Rmax b₀ b₁).2.role = .Resetting := by
  simp only [phase4_propagate] at h ⊢
  by_cases h1 : b₀.rank.val + 1 = ceilHalf n
  · simp only [h1, ite_true] at h ⊢
    by_cases h2 : b₁.rank.val + 1 = n
    · simp only [h2, ite_true] at h ⊢; split_ifs at h ⊢ <;> simp_all
    · simp only [h2, ite_false] at h ⊢; split_ifs at h ⊢ <;> simp_all
  · simp only [h1, ite_false] at h ⊢
    by_cases h4 : b₁.rank.val + 1 = ceilHalf n
    · simp only [h4, ite_true] at h ⊢
      by_cases h5 : b₀.rank.val + 1 = n
      · simp only [h5, ite_true] at h ⊢; split_ifs at h ⊢ <;> simp_all
      · simp only [h5, ite_false] at h ⊢; split_ifs at h ⊢ <;> simp_all
    · simp only [h4, ite_false] at h ⊢; rw [hs₀] at h; exact absurd h (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000000 in
private theorem phase4_propagate_snd_resetting_of_settled
    {n Rmax : ℕ} {b₀ b₁ : AgentState n}
    (hs₀ : b₀.role = .Settled) (hs₁ : b₁.role = .Settled)
    (h : (phase4_propagate n Rmax b₀ b₁).2.role = .Resetting) :
    (phase4_propagate n Rmax b₀ b₁).1.role = .Resetting := by
  simp only [phase4_propagate] at h ⊢
  by_cases h1 : b₀.rank.val + 1 = ceilHalf n
  · simp only [h1, ite_true] at h ⊢
    by_cases h2 : b₁.rank.val + 1 = n
    · simp only [h2, ite_true] at h ⊢; split_ifs at h ⊢ <;> simp_all
    · simp only [h2, ite_false] at h ⊢; split_ifs at h ⊢ <;> simp_all
  · simp only [h1, ite_false] at h ⊢
    by_cases h4 : b₁.rank.val + 1 = ceilHalf n
    · simp only [h4, ite_true] at h ⊢
      by_cases h5 : b₀.rank.val + 1 = n
      · simp only [h5, ite_true] at h ⊢; split_ifs at h ⊢ <;> simp_all
      · simp only [h5, ite_false] at h ⊢; split_ifs at h ⊢ <;> simp_all
    · simp only [h4, ite_false] at h ⊢; rw [hs₁] at h; exact absurd h (by decide)

/-! ## Full transitionPEM no-mixed-outcome for InSswap

After prePhase4 identity + transitionPEM_phase4 unfold, the goal is about
  phase4_propagate n Rmax c₀ c₁
where c₀, c₁ are the outputs of phase4_decide ∘ phase4_swap.
We show c₀, c₁ have Settled roles (swap/decide only change answer, not role),
then apply phase4_propagate_fst/snd_resetting_of_settled.  -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
theorem transitionPEM_fst_resetting_implies_snd_of_InSswap
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).2.role = .Resetting := by
  simp only [transitionPEM] at h ⊢
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h ⊢
  -- Now goal: (transitionPEM_phase4 n Rmax (s₀, s₁) x₀ x₁).2.role = .Resetting
  -- Unfold transitionPEM_phase4 + resolve the "both Settled" guard
  unfold transitionPEM_phase4 at h ⊢
  simp only [hs₀, hs₁, and_self, ite_true] at h ⊢
  -- Now the goal involves let-bound phase4_swap → phase4_decide → phase4_propagate.
  -- Use dsimp to inline the lets, then apply the propagate lemma.

  -- The input to phase4_propagate has Settled roles because
  -- phase4_swap preserves .role (just swaps or identity) and
  -- phase4_decide preserves .role (only changes .answer).
  -- Verify via unfold + split_ifs on swap and decide.
  have hsw₀ : (phase4_swap s₀ s₁ x₀ x₁).1.role = .Settled := by
    unfold phase4_swap; split_ifs <;> assumption
  have hsw₁ : (phase4_swap s₀ s₁ x₀ x₁).2.role = .Settled := by
    unfold phase4_swap; split_ifs <;> assumption
  have hsd₀ : (phase4_decide n (phase4_swap s₀ s₁ x₀ x₁).1
      (phase4_swap s₀ s₁ x₀ x₁).2 x₀ x₁).1.role = .Settled := by
    simp only [phase4_decide]; split_ifs <;> simp_all
  have hsd₁ : (phase4_decide n (phase4_swap s₀ s₁ x₀ x₁).1
      (phase4_swap s₀ s₁ x₀ x₁).2 x₀ x₁).2.role = .Settled := by
    simp only [phase4_decide]; split_ifs <;> simp_all
  exact phase4_propagate_fst_resetting_of_settled hsd₀ hsd₁ h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
theorem transitionPEM_snd_resetting_implies_fst_of_InSswap
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).2.role = .Resetting) :
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting := by
  simp only [transitionPEM] at h ⊢
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h ⊢
  unfold transitionPEM_phase4 at h ⊢
  simp only [hs₀, hs₁, and_self, ite_true] at h ⊢

  have hsw₀ : (phase4_swap s₀ s₁ x₀ x₁).1.role = .Settled := by
    unfold phase4_swap; split_ifs <;> assumption
  have hsw₁ : (phase4_swap s₀ s₁ x₀ x₁).2.role = .Settled := by
    unfold phase4_swap; split_ifs <;> assumption
  have hsd₀ : (phase4_decide n (phase4_swap s₀ s₁ x₀ x₁).1
      (phase4_swap s₀ s₁ x₀ x₁).2 x₀ x₁).1.role = .Settled := by
    simp only [phase4_decide]; split_ifs <;> simp_all
  have hsd₁ : (phase4_decide n (phase4_swap s₀ s₁ x₀ x₁).1
      (phase4_swap s₀ s₁ x₀ x₁).2 x₀ x₁).2.role = .Settled := by
    simp only [phase4_decide]; split_ifs <;> simp_all
  exact phase4_propagate_snd_resetting_of_settled hsd₀ hsd₁ h


/-! ## Conditions necessary for Resetting output (odd parity) -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
/-- Neither median → propagate identity → not Resetting. -/
theorem transitionPEM_fst_resetting_implies_some_median_odd
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    s₀.rank.val + 1 = ceilHalf n ∨ s₁.rank.val + 1 = ceilHalf n := by
  by_contra h_neither
  push_neg at h_neither
  simp only [transitionPEM] at h
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h
  unfold transitionPEM_phase4 at h
  simp only [hs₀, hs₁, and_self, ite_true] at h
  -- Swap doesn't fire
  unfold phase4_swap at h; simp only [h_no_swap, ite_false] at h
  -- Odd decide: neither is median, so both branches are identity
  unfold phase4_decide at h; simp only [hpar, ite_false, h_neither.1, h_neither.2] at h
  -- Propagate: neither ceilHalf → identity
  unfold phase4_propagate at h; simp only [h_neither.1, h_neither.2, ite_false] at h
  rw [hs₀] at h; exact absurd h (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
/-- s₀ median + s₁ NOT max + odd, Resetting → s₀.timer = 0. -/
theorem transitionPEM_fst_resetting_s0_med_no_max_odd_timer_zero
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_s0_med : s₀.rank.val + 1 = ceilHalf n)
    (h_s1_no_med : s₁.rank.val + 1 ≠ ceilHalf n)
    (h_s1_no_max : s₁.rank.val + 1 ≠ n)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    s₀.timer = 0 := by
  simp only [transitionPEM] at h
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h
  unfold transitionPEM_phase4 at h
  simp only [hs₀, hs₁, and_self, ite_true] at h
  unfold phase4_swap at h; simp only [h_no_swap, ite_false] at h
  unfold phase4_decide at h; simp only [hpar, ite_false, h_s0_med, ite_true, h_s1_no_med] at h
  unfold phase4_propagate at h; simp only [h_s0_med, ite_true, h_s1_no_max, ite_false] at h
  -- Guard: timer = 0 ∧ answer ≠ answer. If timer ≠ 0, guard fails → Settled.
  split_ifs at h with hguard
  · exact hguard.1
  · rw [hs₀] at h; exact absurd h (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
/-- s₀ median + s₁ max + odd, Resetting → s₀.timer ≤ 1. -/
theorem transitionPEM_fst_resetting_s0_med_max_odd_timer_le_one
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_s0_med : s₀.rank.val + 1 = ceilHalf n)
    (h_s1_no_med : s₁.rank.val + 1 ≠ ceilHalf n)
    (h_s1_max : s₁.rank.val + 1 = n)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    s₀.timer ≤ 1 := by
  simp only [transitionPEM] at h
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h
  unfold transitionPEM_phase4 at h
  simp only [hs₀, hs₁, and_self, ite_true] at h
  unfold phase4_swap at h; simp only [h_no_swap, ite_false] at h
  unfold phase4_decide at h; simp only [hpar, ite_false, h_s0_med, ite_true, h_s1_no_med] at h
  unfold phase4_propagate at h; simp only [h_s0_med, ite_true, h_s1_max, ite_true] at h
  -- Timer decremented: check (timer - 1 = 0 ∧ answer ≠ answer)
  split_ifs at h with hguard
  · omega
  · rw [hs₀] at h; exact absurd h (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
/-- s₀ median + odd + Resetting → opinionToAnswer x₀ ≠ s₁.answer. -/
theorem transitionPEM_fst_resetting_s0_med_odd_answer_diff
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_s0_med : s₀.rank.val + 1 = ceilHalf n)
    (h_s1_no_med : s₁.rank.val + 1 ≠ ceilHalf n)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    opinionToAnswer x₀ ≠ s₁.answer := by
  simp only [transitionPEM] at h
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h
  unfold transitionPEM_phase4 at h
  simp only [hs₀, hs₁, and_self, ite_true] at h
  unfold phase4_swap at h; simp only [h_no_swap, ite_false] at h
  unfold phase4_decide at h; simp only [hpar, ite_false, h_s0_med, ite_true, h_s1_no_med] at h
  -- Now h is about phase4_propagate with known median.
  -- The propagate guard includes answer ≠ answer.
  -- Case split on whether s₁ is max rank (affects timer decrement but not answer check).
  unfold phase4_propagate at h
  simp only [h_s0_med, ite_true] at h
  by_cases h_s1_max : s₁.rank.val + 1 = n
  · simp only [h_s1_max, ite_true] at h
    split_ifs at h with hguard
    · exact hguard.2
    · rw [hs₀] at h; exact absurd h (by decide)
  · simp only [h_s1_max, ite_false] at h
    split_ifs at h with hguard
    · exact hguard.2
    · rw [hs₀] at h; exact absurd h (by decide)

end SSEM
