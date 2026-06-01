import SSExactMajority.UpperBound.Time.Bridge

namespace SSEM

-- Test: can we simplify field projections through record updates?
example (s : AgentState n) (a : Answer) : { s with answer := a }.role = s.role := by rfl
example (s : AgentState n) (a : Answer) : { s with answer := a }.rank = s.rank := by rfl
example (s : AgentState n) (a : Answer) : { s with answer := a }.timer = s.timer := by rfl
example (s : AgentState n) (a : Answer) : { s with answer := a }.leader = s.leader := by rfl
example (s : AgentState n) (a : Answer) : { s with answer := a }.resetcount = s.resetcount := by rfl

-- Test: does simp know these?
example (s : AgentState n) (a : Answer) (h : s.role = .Settled) :
    { s with answer := a }.role = .Settled := by simp [h]

-- Test: what about nested struct updates from phase4_decide?
example (s₀ s₁ : AgentState n) (a : Answer) :
    ({ s₀ with answer := a }, { s₁ with answer := a }).1.role = s₀.role := by rfl

example (s₀ s₁ : AgentState n) (a : Answer) :
    ({ s₀ with answer := a }, { s₁ with answer := a }).1.rank = s₀.rank := by rfl

end SSEM
