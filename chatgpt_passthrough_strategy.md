Yes: for a plain structure update, this is definitionally true.
leanexample {n : ℕ} (s : AgentState n) (a : Answer) :    ({ s with answer := a }).role = s.role := by  rfl
If rfl does not close, the expression is probably not literally in that head form because of surrounding let, if, or pair projections. The fallback is:
lean  dsimp
or, for a stubborn abstract record:
lean  cases s  rfl
But for your transitionPEM problem, I would not solve each sorry by split_ifs <;> rfl. The better pattern is:


Add explicit [simp] projection lemmas for AgentState updates.


Prove one “Phase 2/3 preserve structural fields if Phase 4 does not fire” lemma.


Use that lemma in all five sorrys.


AgentState has exactly the fields you describe — role, rank, leader, resetcount, answer, timer, children, errorcount, delaytimer State — and transitionPEM only changes answer/timer before the final “both Settled” Phase 4 guard Transition.
1. Add projection simp lemmas
Put these near State.lean, or in the proof file before the bottleneck lemmas.
leannamespace SSEMvariable {n : ℕ}namespace AgentState@[simp] theorem role_with_answer (s : AgentState n) (a : Answer) :    ({ s with answer := a }).role = s.role := rfl@[simp] theorem leader_with_answer (s : AgentState n) (a : Answer) :    ({ s with answer := a }).leader = s.leader := rfl@[simp] theorem rank_with_answer (s : AgentState n) (a : Answer) :    ({ s with answer := a }).rank = s.rank := rfl@[simp] theorem children_with_answer (s : AgentState n) (a : Answer) :    ({ s with answer := a }).children = s.children := rfl@[simp] theorem resetcount_with_answer (s : AgentState n) (a : Answer) :    ({ s with answer := a }).resetcount = s.resetcount := rfl@[simp] theorem delaytimer_with_answer (s : AgentState n) (a : Answer) :    ({ s with answer := a }).delaytimer = s.delaytimer := rfl@[simp] theorem errorcount_with_answer (s : AgentState n) (a : Answer) :    ({ s with answer := a }).errorcount = s.errorcount := rfl@[simp] theorem role_with_timer (s : AgentState n) (T : ℕ) :    ({ s with timer := T }).role = s.role := rfl@[simp] theorem leader_with_timer (s : AgentState n) (T : ℕ) :    ({ s with timer := T }).leader = s.leader := rfl@[simp] theorem rank_with_timer (s : AgentState n) (T : ℕ) :    ({ s with timer := T }).rank = s.rank := rfl@[simp] theorem children_with_timer (s : AgentState n) (T : ℕ) :    ({ s with timer := T }).children = s.children := rfl@[simp] theorem resetcount_with_timer (s : AgentState n) (T : ℕ) :    ({ s with timer := T }).resetcount = s.resetcount := rfl@[simp] theorem delaytimer_with_timer (s : AgentState n) (T : ℕ) :    ({ s with timer := T }).delaytimer = s.delaytimer := rfl@[simp] theorem errorcount_with_timer (s : AgentState n) (T : ℕ) :    ({ s with timer := T }).errorcount = s.errorcount := rflend AgentStateend SSEM
These are all rfl, but making them named [simp] lemmas is useful because your proofs use simp only. Without explicit lemmas, simp only [...] often does not know which record-update reductions you want.
2. Encode “same except answer/timer”
This avoids repeating seven field equalities everywhere.
leannamespace SSEMvariable {n : ℕ}def SameStructuralFields (s t : AgentState n) : Prop :=  t.role = s.role ∧  t.leader = s.leader ∧  t.rank = s.rank ∧  t.children = s.children ∧  t.resetcount = s.resetcount ∧  t.delaytimer = s.delaytimer ∧  t.errorcount = s.errorcountdef SameStructuralPair    (r out : AgentState n × AgentState n) : Prop :=  SameStructuralFields r.1 out.1 ∧  SameStructuralFields r.2 out.2@[simp] theorem SameStructuralFields_refl (s : AgentState n) :    SameStructuralFields s s := by  simp [SameStructuralFields]@[simp] theorem SameStructuralFields_with_answer    (s : AgentState n) (a : Answer) :    SameStructuralFields s { s with answer := a } := by  simp [SameStructuralFields]@[simp] theorem SameStructuralFields_with_timer    (s : AgentState n) (T : ℕ) :    SameStructuralFields s { s with timer := T } := by  simp [SameStructuralFields]end SSEM
3. Prove the one transition lemma you actually need
The key is: do not split Phase 4. First make the Phase 4 guard false using role preservation through Phase 2/3, then let simp kill the final if.
leannamespace SSEMvariable {n : ℕ}theorem transitionPEM_sameStructural_of_rankDelta_not_both_settled    {trank Rmax : ℕ}    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}    (hNoPhase4 :      ¬ ((rankDelta (s₀, s₁)).1.role = .Settled ∧         (rankDelta (s₀, s₁)).2.role = .Settled)) :    SameStructuralPair      (rankDelta (s₀, s₁))      (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))) := by  classical  -- Freeze the rankDelta output. This prevents Lean from repeatedly  -- expanding/reducing the same expression in different shapes.  generalize hrd : rankDelta (s₀, s₁) = rd  rcases rd with ⟨r₀, r₁⟩  have hNoPhase4' : ¬ (r₀.role = .Settled ∧ r₁.role = .Settled) := by    simpa [hrd] using hNoPhase4  -- Important: no global split_ifs.  -- `simp` reduces Phase 2/3 field updates, rewrites the final guard  -- to `r₀.role = .Settled ∧ r₁.role = .Settled`, then uses hNoPhase4'.  unfold transitionPEM  rw [hrd]  dsimp  simpa [SameStructuralPair, SameStructuralFields, hNoPhase4']end SSEM
This is the shape I would try first. If the last simpa is slightly too optimistic in your actual file, replace it with:
lean  simp [SameStructuralPair, SameStructuralFields, hNoPhase4']
and inspect the remaining goals. Usually the remaining goals are just projections like:
lean({ r₀ with answer := .phi }).leader = r₀.leader({ r₁ with timer := 7 * (trank + 4) }).rank = r₁.rank
which the [simp] lemmas above should now close.
4. How to use it in the five sorrys
Suppose you know that rankDeltaOSSR produced a Resetting first state, so Phase 4 cannot fire:
leanhave hNoPhase4 :    ¬ ((rankDeltaOSSR Rmax Emax Dmax hn (s₀, s₁)).1.role = .Settled ∧       (rankDeltaOSSR Rmax Emax Dmax hn (s₀, s₁)).2.role = .Settled) := by  intro h  -- use your known role equation here  -- e.g. if first role is Resetting:  -- have h₁ : (rankDeltaOSSR ... (s₀, s₁)).1.role = .Resetting := ...  -- rw [h₁] at h  -- exact Role.noConfusion h.1  ...
Then:
leanhave hStruct :=  transitionPEM_sameStructural_of_rankDelta_not_both_settled    (n := n)    (trank := trank)    (Rmax := Rmax)    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)    (s₀ := s₀)    (s₁ := s₁)    (x₀ := x₀)    (x₁ := x₁)    hNoPhase4
Now first-agent fields are in hStruct.1; second-agent fields are in hStruct.2.
For example, if using the conjunction definition above:
lean-- first output roleexact hStruct.1.1-- first output leaderexact hStruct.1.2.1-- first output rankexact hStruct.1.2.2.1-- second output roleexact hStruct.2.1
If you find the nested conjunction selectors ugly, turn SameStructuralFields into a structure instead of a def, so you can write hStruct.fst.role, hStruct.fst.rank, etc.
5. The important tactical rule
Avoid this pattern:
leanunfold transitionPEMsimp only [...]split_ifs <;> rfl
That forces Lean into the huge Phase 4 branch, where many branches are irrelevant because Phase 4 is actually false. Instead:
leanunfold transitionPEMrw [hrd]dsimpsimpa [hNoPhase4', SameStructuralPair, SameStructuralFields]
or prove the final guard false explicitly, then simplify the final if.
So the answer to your direct question is: {s with answer := x}.role = s.role is rfl; use custom [simp] projection lemmas if simp only is involved. For the larger proof, use a structural-field relation and a single “no Phase 4” lemma instead of splitting the whole transitionPEM.
