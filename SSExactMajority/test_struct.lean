import SSExactMajority.UpperBound.Time.Bridge

namespace SSEM

-- The real issue: field projection inside if-condition after struct update
example (s₀ s₁ : AgentState n) (a b : Answer) (h : s₀.rank.val + 1 ≠ ceilHalf n) :
    ¬ (↑({ s₀ with answer := a }.rank) + 1 = ceilHalf n) := by
  exact h  -- rfl-reduces { s₀ with answer := a }.rank to s₀.rank

-- Does simp know this?
example (s₀ : AgentState n) (a : Answer) (h : s₀.rank.val + 1 ≠ ceilHalf n) :
    { s₀ with answer := a }.rank.val + 1 ≠ ceilHalf n := by
  exact h

-- Can we use dsimp to reduce struct projections?
example (s₀ s₁ : AgentState n) (a : Answer)
    (h : (s₀, s₁).1.role = .Settled) :
    ({ s₀ with answer := a }, { s₁ with answer := a }).1.role = .Settled := by
  dsimp at h ⊢; exact h

-- The actual pattern from the sorry: after phase4_decide + unfold
-- can we simplify the condition?
example (s₀ s₁ : AgentState n) (a : Answer)
    (h : ¬ (s₀.rank.val + 1 = ceilHalf n))
    (goal : (if ↑({ s₀ with answer := a }.rank) + 1 = ceilHalf n then True else False)) :
    False := by
  simp only [show { s₀ with answer := a }.rank = s₀.rank from rfl, h] at goal
  exact goal

end SSEM
