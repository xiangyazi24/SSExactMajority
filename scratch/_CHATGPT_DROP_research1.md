# SSExactMajority v4.30 migration audit — research1

## Executive summary

The root cause is not that `split_ifs` itself became unusable. The root cause is that the old proofs ask the simplifier to rediscover a long deterministic execution trace of `transitionPEM` from scratch after each case split. In v4.30 that is too brittle: hidden projection types, changed negation normal forms, structure-update syntax changes, and heavier `simp_all` search combine badly.

The robust migration path is:

1. Normalize the `Config.step`/`P.δ` bridge once into an equality whose RHS is explicitly `transitionPEM`.
2. Use trace lemmas for the exact post-state of `transitionPEM`.
3. Project fields only from explicit `AgentState n` equalities, or avoid projection by rewriting whole state equalities.
4. Use `simp only`/`rw`/`omega` on tiny residual goals, not `split_ifs <;> simp_all` on the whole transition.

The current split files already point in the right direction: the trace-builder lemmas `CRS_from_odd_trace`, `CRS_from_odd_trace_responder_median`, `CRS_from_even_trace`, and the `*_trace` lemmas are the right replacement for the old 350–477 line unfold/split proofs.

---

## 1. Systematic v4.30 fix for `congrArg AgentState.field hfst`

### Diagnosis

The fragile pattern is:

```lean
have h_fst := Config.step_fst_state P D hij
rw [← show ∀ p, P.δ p = transitionPEM n Rmax Rmax
  (rankDeltaOSSR Rmax Emax Dmax hn0) p from fun _ => rfl,
  ← congrArg AgentState.role h_fst]
```

or:

```lean
rw [congrArg AgentState.role h_fst, hP_δ]
```

This relies on Lean inferring that the equality endpoints of `h_fst` are exactly `AgentState n`, and also on reducing `P.δ` to `transitionPEM` at the right time. In v4.30, the implicit `n` in `AgentState.role` and the still-opaque `P.δ` can make the projection elaboration fail.

### Preferred fix: prove the normalized state equality first

Use a whole-state equality whose RHS is already `transitionPEM`, then rewrite with it.

```lean
set P := PEMProtocolCoupled n Rmax Emax Dmax hn0

have hfst_state :
    (D.step P i j i).1 =
      (transitionPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1 := by
  rw [Config.step_fst_state P D hij]
  change
    (transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1 =
    (transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1
  rfl

have hsnd_state :
    (D.step P i j j).1 =
      (transitionPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2 := by
  rw [Config.step_snd_state P D hij (Ne.symm hij)]
  change
    (transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2 =
    (transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2
  rfl
```

Then convert a post-step role hypothesis into a raw `transitionPEM` role hypothesis without any projected `congrArg`:

```lean
have h_i_res_raw :
    (transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1.role = .Resetting := by
  rw [← hfst_state]
  exact h_i_res

have h_j_res_raw :
    (transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2.role = .Resetting := by
  rw [← hsnd_state]
  exact h_j_res
```

And if a trace lemma gives the exact pair result:

```lean
have h_step_i : (D.step P i j i).1 = out₁ := by
  rw [hfst_state]
  simpa using congrArg Prod.fst htr

have h_step_j : (D.step P i j j).1 = out₂ := by
  rw [hsnd_state]
  simpa using congrArg Prod.snd htr
```

This is the single most important migration pattern. It also fixes the ARS blocker: `AnyResetSeed` only needs structural/reset fields, so transfer the role/resetcount/leader facts through `hfst_state` and `hsnd_state` instead of projecting `h_fst` directly.

### Acceptable fallback: annotate the projection function

If projection is genuinely convenient, project only after the equality endpoints are visibly `AgentState n`:

```lean
have hfst_role :
    (D.step P i j i).1.role =
      (transitionPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1.role := by
  exact congrArg (fun s : AgentState n => s.role) hfst_state

have hfst_answer :
    (D.step P i j i).1.answer =
      (transitionPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1.answer := by
  exact congrArg (fun s : AgentState n => s.answer) hfst_state
```

Avoid `congrArg AgentState.role h_fst` directly. Prefer `congrArg (fun s : AgentState n => s.role) hfst_state`.

---

## 2. Clean hpair_ans strategy for CRS_odd answer correctness

The clean proof should not unfold `transitionPEM` at all. Strengthen or use the trace lemma so that the two output states already carry the answer field:

```lean
(h_out1_ans : out₁.answer = opinionToAnswer (D i).2)
(h_out2_ans : out₂.answer = opinionToAnswer (D i).2)
```

for initiator-median, and similarly with `(D j).2` for responder-median.

Then answer correctness follows from exactly two semantic facts:

```lean
have h_maj : majorityAnswer (D.step P i j) = majorityAnswer D := by
  simpa [P, PEMProtocolCoupled, PEMProtocol] using
    majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j

have hμ_majority : opinionToAnswer (D i).2 = majorityAnswer D :=
  opinionToAnswer_median_eq_majorityAnswer_odd hS h_i_med hOdd
```

The local `hpair_ans` proof can then be this shape:

```lean
have hpair_ans :
    ∀ w : Fin n,
      (D.step P i j w).1.role = .Resetting →
      (D.step P i j w).1.answer = majorityAnswer (D.step P i j) := by
  intro w hw_res
  by_cases hwi : w = i
  · subst hwi
    rw [h_step_i, h_out1_ans, hμ_majority, h_maj]
  · by_cases hwj : w = j
    · subst hwj
      rw [h_step_j, h_out2_ans, hμ_majority, h_maj]
    · exfalso
      have h_post_other : D.step P i j w = D w := by
        unfold Config.step
        simp [hij, hwi, hwj]
      rw [show (D.step P i j w).1 = (D w).1 from
        congrArg Prod.fst h_post_other] at hw_res
      rw [hS.allSettled w] at hw_res
      exact Role.noConfusion hw_res
```

For responder-median, replace the median answer fact with:

```lean
have hμ_majority : opinionToAnswer (D j).2 = majorityAnswer D :=
  opinionToAnswer_median_eq_majorityAnswer_odd hS h_j_med hOdd
```

and use `h_out1_ans : out₁.answer = opinionToAnswer (D j).2`, `h_out2_ans : out₂.answer = opinionToAnswer (D j).2`.

### Recommended helper boundary

The best helper is exactly the already-emerging pattern:

```lean
private theorem CRS_from_odd_trace
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    {i j : Fin n} (hij : i ≠ j)
    (h_i_med : (D i).1.rank.val + 1 = ceilHalf n)
    (hOdd : n % 2 ≠ 0)
    {out₁ out₂ : AgentState n}
    (htr : transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j) = (out₁, out₂))
    (h_out1_role : out₁.role = .Resetting)
    (h_out1_rc : out₁.resetcount = Rmax)
    (h_out1_leader : out₁.leader = .L)
    (h_out1_ans : out₁.answer = opinionToAnswer (D i).2)
    (h_out2_role : out₂.role = .Resetting)
    (h_out2_rc : out₂.resetcount = Rmax)
    (h_out2_ans : out₂.answer = opinionToAnswer (D i).2) :
    CorrectResetSeed (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  -- bridge step outputs to out₁/out₂ once;
  -- prove resetcount/leader/answer obligations by rw;
  -- all other resetters are impossible because bystanders remain Settled.
  ...
```

This makes hpair answer correctness a 3-line rewrite in each relevant branch rather than a new `transitionPEM` proof.

---

## 3. Is there a simpler way than trace lemmas?

For this code base, no: the trace-lemma approach is the simpler approach. Trying to revive the old proof style with larger limits will remain unstable.

### Why `split_ifs <;> simp_all` is the wrong unit of proof

The unfolded `transitionPEM` contains:

- prePhase4 reset/settled/timer/epidemic logic,
- phase4 swap,
- phase4 decide,
- phase4 propagate,
- structure updates over many fields,
- rank/input invariants,
- parity-dependent median cases.

A single `simp_all` after global `split_ifs` asks Lean to solve all field, rank, parity, and contradiction obligations simultaneously. In v4.30, that is exactly where you see simp-step exhaustion, huge CPU time, or failed `change`.

### Use this reduction sequence instead

At transition-level lemmas, reduce only the outer shell:

```lean
simp only [transitionPEM] at h ⊢
rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hsi hsj hrij] at h ⊢
unfold transitionPEM_phase4 at h ⊢
simp only [hsi, hsj, and_self, ite_true] at h ⊢
```

Then use small phase lemmas:

```lean
have hsw₀ : (phase4_swap s₀ s₁ x₀ x₁).1.role = .Settled := by
  unfold phase4_swap
  split_ifs <;> assumption

have hsd₀ :
    (phase4_decide n (phase4_swap s₀ s₁ x₀ x₁).1
      (phase4_swap s₀ s₁ x₀ x₁).2 x₀ x₁).1.role = .Settled := by
  simp only [phase4_decide]
  split_ifs <;> simp [hsw₀]
```

At leaf phase proofs, `split_ifs` is fine, but avoid `simp_all`. Use named conditions and targeted simplification:

```lean
simp only [phase4_propagate] at h ⊢
by_cases hmed₀ : b₀.rank.val + 1 = ceilHalf n
· simp only [hmed₀, ite_true] at h ⊢
  by_cases hmax₁ : b₁.rank.val + 1 = n
  · simp only [hmax₁, ite_true] at h ⊢
    split_ifs with hg at h ⊢
    · rcases hg with ⟨htimer, hans⟩
      -- explicit contradiction or constructor
      ...
    · ...
  · simp only [hmax₁, ite_false] at h ⊢
    ...
· simp only [hmed₀, ite_false] at h ⊢
  ...
```

### Limit bumps are not a real fix

`set_option maxHeartbeats` and `set_option maxRecDepth` are useful to unblock isolated old lemmas, but they should not be the main strategy. Increasing simplifier limits only makes the proof less predictable. It also hides the actual boundary you want: one lemma per semantic transition trace.

`cbv` in v4.30 is better than before and can sometimes reduce closed computation-like terms, but it is not the right primitive for this blocker because your goals depend on hypotheses controlling conditionals. The trace lemmas plus targeted `rw` are more maintainable.

---

## Blocker-by-blocker audit

### A1. `CRS_even` / `step_InSswap_break_creates_CorrectResetSeed`

Use the same pattern as odd:

1. Handle `i = j` by `simp [Config.step]` and contradiction with `hS'`.
2. Establish `hsi`, `hsj`, `hrij`, `hFix`, and `h_no_swap`.
3. Bridge step roles to raw `transitionPEM` roles using `hfst_state`/`hsnd_state`, not projected `congrArg h_fst`.
4. Use role dichotomy and no-mixed-reset lemmas to show either both outputs are Settled, contradicting broken `InSswap`, or both outputs are Resetting.
5. Classify the Resetting branch by even median cases and apply an exact trace lemma.
6. Build `CorrectResetSeed` with a `CRS_from_even_trace`-style helper.

For answer correctness in the even CRS helper, do not unfold. Use:

```lean
have hcor : (D μ).1.answer = majorityAnswer D := hM μ hμ_med
have hmaj : majorityAnswer (D.step P μ v) = majorityAnswer D := by
  simpa [P, PEMProtocolCoupled, PEMProtocol] using
    majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ v

-- then after h_post_μ / h_post_v:
rw [h_post_μ, h1a, hcor, hmaj]
```

### A2. `CRS_odd hpair_ans`

Close it with the `opinionToAnswer_median_eq_majorityAnswer_odd` + `majorityAnswer_step_eq` rewrite shown above. If your current trace lemma only returns structural fields, strengthen it to return the answer fields too. The trace itself determines the answer; the CRS constructor should not have to unfold `transitionPEM` again.

### A3. `ARS`

`AnyResetSeed` should be easier than CRS because it does not need global answer correctness. The only v4.30-specific issue is the step/transition bridge. Use:

```lean
have hfst_state : (D.step P i j i).1 = (transitionPEM ... (D i, D j)).1 := by
  rw [Config.step_fst_state P D hij]
  change (transitionPEM ... (D i, D j)).1 = (transitionPEM ... (D i, D j)).1
  rfl

have hsnd_state : (D.step P i j j).1 = (transitionPEM ... (D i, D j)).2 := by
  rw [Config.step_snd_state P D hij (Ne.symm hij)]
  change (transitionPEM ... (D i, D j)).2 = (transitionPEM ... (D i, D j)).2
  rfl
```

Then rewrite whole states or explicitly annotated field projections. Do not use `congr_arg (·.role) hfst` on the original `Config.step_fst_state` equality.

### B4/B5. `live_break_CRS` and `timer_drain`

Once CRS_even/CRS_odd are stable, these should be shallow parity dispatches. The `push_neg` migration is important in the timer branch:

```lean
push_neg at hNonUpper
-- now: hNonUpper : ∀ v, (D v).1.answer ≠ majorityAnswer D →
--   (D v).1.rank.val + 1 = n / 2 + 1

have hv_upper : (D v).1.rank.val + 1 = n / 2 + 1 :=
  hNonUpper v hv_wrong
```

Do not destruct `hNonUpper v` as a disjunction in v4.30.

Also update every rank/timer preservation call with explicit interaction indices:

```lean
step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
  (Dmax := Dmax) (i := i) (j := j) hn0 hS w

step_timer_le_of_InSswap (Rmax := Rmax) (Emax := Emax)
  (Dmax := Dmax) (i := i) (j := j) hn0 hS w
```

### C6–C9. Time composition proofs

These are independent of the transition blocker. I would isolate them behind small generic lemmas:

- monotonicity of hitting goals,
- two-stage expected hitting time composition,
- Strong Markov stage composition with named intermediate predicates,
- one lemma per stage bound.

Do not mix transition proof repair with Strong Markov algebra. First make the stage lemmas compile; then compose them with a thin arithmetic layer.

### C10. arithmetic inequality

The inequality

```lean
7 * (Rmax + 4) * n * (n - 1) + n * (n - 1) + 4 * Rmax * n * n ≤
  18 * Rmax * n * n
```

is true from `4 ≤ n` and `n ≤ Rmax`. If `nlinarith` is failing on `n - 1`, introduce the predecessor as a named variable and expose `m + 1 = n`:

```lean
have hR4 : 4 ≤ Rmax := le_trans hn4 hRmax
set m : ℕ := n - 1 with hmdef
have hm : m + 1 = n := by
  dsimp [m]
  omega
-- Then try the original goal after normalization:
nlinarith [hn4, hRmax, hR4, hm]
```

If that still does not close, prove the key middle estimate explicitly:

```lean
have hkey : 29 * (n - 1) ≤ 7 * Rmax * n := by
  set m : ℕ := n - 1 with hmdef
  have hm : m + 1 = n := by dsimp [m]; omega
  nlinarith [hn4, hRmax, hm]
```

Then finish by rewriting `7 * (Rmax + 4) + 1` as `7 * Rmax + 29` and using `nlinarith [hkey]`. The important point is to avoid asking `nlinarith` to discover the predecessor relation by itself.

---

## Practical migration checklist

1. Add local bridge equalities `hfst_state`/`hsnd_state` in every CRS/ARS proof.
2. Replace projected `congrArg AgentState.role hfst` with `rw [← hfst_state]` or an annotated projection.
3. Strengthen odd/even trace helpers to include answer fields where CRS needs them.
4. Replace global `unfold transitionPEM ...; split_ifs <;> simp_all` with a trace lemma call.
5. Use `simp only` with named hypotheses, never broad `simp_all`, after unfolding only one leaf phase.
6. Update preservation lemmas with explicit `(i := ...) (j := ...)`.
7. Replace old `push_neg` disjunction destructs with implication use.
8. Keep Time.lean composition and arithmetic in separate lemmas so transition repair does not contaminate Strong Markov proofs.
