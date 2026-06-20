# Q48 / research1 audit round 2 — dead code and timer-drain dependency

Date: 2026-06-20
Branch requested: `scratch`

## Important source-state caveat

I checked the connected GitHub `scratch` branch first. As visible through the connector, `scratch` is currently only ahead of `main` by the scratch markdown files; the Lean source tree itself is not changed on that branch. In particular, the connected branch still has the old source layout in which `PhaseProofs.lean` calls `step_InSswap_break_creates_CorrectResetSeed` from `PEM_expected_reset_trigger_v2`.

So there are two separate statements:

1. **On the connected `scratch` branch as actually pushed:** I cannot confirm the Q46/Q48 source edits, because they are not present in the pushed source tree. The branch does not contain the “replace reset-trigger call with `crs_of_InSswap_break_with_MedC`” edit described in the prompt.
2. **Assuming the local Q48 state described in the prompt is the intended current source state:** the dependency analysis below is the right one. In that state, the three CRS/ARS step theorems are dead once the last reset-trigger call has been redirected to the timer-agnostic wrapper.

Everything below is therefore phrased as the audit of the **described post-Q46 source state**, with the caveat above.

---

## 1. StepProofs / step-level blockers

### Verdict

Assuming your grep result is from the current local post-Q46 tree, yes:

```text
PEM_expected_timer_drain
```

is the only sorry'd theorem in the StepProofs/time-step layer that still has a live caller.

The caller you found is the relevant one:

```text
PEM_expected_median_correct_to_consensus
  -> PEM_expected_timer_drain
```

I would treat this as the only live StepProofs sorry unless another source file outside `Time.lean` imports and explicitly calls it. In the intended post-Q46 dependency graph, the following are dead:

```text
step_InSswap_break_creates_CorrectResetSeed       -- CRS_even / timer=0 even case
step_InSswap_break_creates_CorrectResetSeed_odd   -- CRS_odd
step_InSswap_break_creates_AnyResetSeed           -- ARS
```

### Why those three become dead

After changing the reset-trigger proof to call:

```lean
crs_of_InSswap_break_with_MedC
```

there should be no high-level caller that needs the old parity-specialized break lemmas directly. The wrapper has the right abstraction boundary:

```lean
crs_of_InSswap_break_with_MedC
  : InSswap D ->
    MedianAnswerCorrect D ->
    ¬ InSswap (D.step P i j) ->
    CorrectResetSeed (D.step P i j)
```

The old theorems become implementation details of the wrapper. If the wrapper is fully proved and does not depend on the sorry versions anymore, then they can be deleted. If the wrapper still internally calls the old theorem names, then the names are not dead implementation-wise; they are just no longer public callers. Your prompt says they have 0 callers, so I am assuming the wrapper has already been refactored away from them or their replacements are separate proved lemmas.

### Timer-drain live edge

The live edge is:

```text
PEM_expected_median_correct_to_consensus
  calls PEM_expected_timer_drain
```

That makes `PEM_expected_timer_drain` live even if every CRS/ARS step theorem is deleted.

---

## 2. The five `Time.lean` sorries: callers and dependency DAG

The five named holes split into two categories:

```text
A. stage-bound theorems
  PEM_expected_allR_to_consensus
  PEM_expected_epidemic_to_consensus
  PEM_expected_anyResetSeed_to_consensus

B. composition/root theorem and its arithmetic
  nlinarith arithmetic inside the median-correct or bridge composition
  PEM_hConsensusBound_from_bridge
```

### Likely live/dead classification

In the intended post-Q46 graph:

| item | status | reason |
|---|---:|---|
| `PEM_expected_allR_to_consensus` | live if `epidemic_to_consensus` or `anyResetSeed_to_consensus` is live | Usually a downstream stage used after reset propagation reaches an all-resetting/recovery state. |
| `PEM_expected_epidemic_to_consensus` | live | Needed from `CorrectResetSeed`, and `CorrectResetSeed` is still a live endpoint of timer drain / reset trigger. |
| `PEM_expected_anyResetSeed_to_consensus` | conditional | Live only if the bridge target still has an `AnyResetSeed` disjunct. Dead if the post-Q46 bridge/DecisionProgress predicate has removed ARS. |
| arithmetic `nlinarith` at line 952 | live if it is inside `PEM_expected_median_correct_to_consensus` or `PEM_hConsensusBound_from_bridge` | It is not a theorem dependency; it is a live proof obligation of its containing theorem. |
| `PEM_hConsensusBound_from_bridge` | live/root | This is the exported bridge composition theorem. Even with no internal caller, it is the root deliverable of this layer unless superseded. |

### True dependency DAG, assuming ARS is still in the bridge target

If `DecisionProgress` / the bridge target still contains an `AnyResetSeed` branch, the dependency graph is:

```text
PEM_hConsensusBound_from_bridge
├─ already-proved bridge/hitting theorem to DecisionProgress
├─ PEM_expected_median_correct_to_consensus
│  ├─ PEM_expected_timer_drain                  -- live StepProofs sorry
│  ├─ PEM_expected_reset_trigger / reset trigger stage
│  │  └─ crs_of_InSswap_break_with_MedC          -- proved wrapper
│  ├─ PEM_expected_epidemic_to_consensus         -- Time.lean sorry
│  │  └─ PEM_expected_allR_to_consensus          -- Time.lean sorry, if epidemic routes via all-R
│  └─ arithmetic line 952                       -- live if inside this theorem
├─ PEM_expected_epidemic_to_consensus            -- for direct CRS branch
│  └─ PEM_expected_allR_to_consensus
└─ PEM_expected_anyResetSeed_to_consensus        -- only if ARS branch still exists
   └─ PEM_expected_allR_to_consensus             -- likely route, depending implementation
```

In this graph, all five Time.lean holes are live, except that `PEM_expected_allR_to_consensus` is live transitively rather than as a root.

### True dependency DAG, if ARS has been removed from the bridge target

If the bridge target is now CRS-only, with no `AnyResetSeed` disjunct, the graph becomes:

```text
PEM_hConsensusBound_from_bridge
├─ already-proved bridge/hitting theorem to DecisionProgress
├─ PEM_expected_median_correct_to_consensus
│  ├─ PEM_expected_timer_drain
│  ├─ PEM_expected_reset_trigger / reset trigger stage
│  │  └─ crs_of_InSswap_break_with_MedC
│  ├─ PEM_expected_epidemic_to_consensus
│  │  └─ PEM_expected_allR_to_consensus
│  └─ arithmetic line 952
└─ PEM_expected_epidemic_to_consensus            -- for direct CRS branch, if present
   └─ PEM_expected_allR_to_consensus
```

Then:

```text
PEM_expected_anyResetSeed_to_consensus
```

is dead code and can be deleted or moved to a separate reset-recovery file as a future optional theorem.

### Recommendation

Run the caller audit on exactly these names in the local tree:

```bash
rg -n "\bPEM_expected_allR_to_consensus\b" SSExactMajority
rg -n "\bPEM_expected_epidemic_to_consensus\b" SSExactMajority
rg -n "\bPEM_expected_anyResetSeed_to_consensus\b" SSExactMajority
rg -n "\bPEM_expected_timer_drain\b" SSExactMajority
rg -n "\bPEM_hConsensusBound_from_bridge\b" SSExactMajority
```

Interpretation rule:

- A theorem with 0 call sites can still be live if it is the public target theorem of the layer.
- A theorem with only self-reference/declaration occurrences is dead unless imported as a public API target.
- `PEM_expected_anyResetSeed_to_consensus` is dead exactly when no live predicate has an `AnyResetSeed` branch.

---

## 3. Can `timer_drain` be restored from original commit `4f9167ea5`?

### Verdict

Yes, it should be restorable now that the timer-agnostic wrapper is proved, but do not paste the original proof verbatim. Restore the original deterministic-descent structure and replace the old break-to-CRS call with the wrapper.

The old type mismatch was real:

```lean
-- old CRS_even needed timer = 0
(hT : ∀ μ, median μ -> timer μ = 0)

-- timer_drain has only timer >= 1
(hT : MedianTimerAtLeast 1 D)
```

That mismatch disappears if the break branch calls:

```lean
crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS'
```

because the wrapper only needs:

```lean
InSswap D
MedianAnswerCorrect D
¬ InSswap (D.step P i j)
```

### Patch shape inside `hInvStep`

For the original goal shape:

```lean
Goal D :=
  IsConsensusConfig D ∨ CorrectResetSeed D ∨
    (InSswap D ∧ MedianAnswerCorrect D ∧ ¬ MedianTimerAtLeast 1 D)
```

use:

```lean
intro D ⟨hS, hM, hT⟩ hG i j
by_cases hS' : InSswap (D.step P i j)
· by_cases hT' : MedianTimerAtLeast 1 (D.step P i j)
  · by_cases hM' : MedianAnswerCorrect (D.step P i j)
    · exact Or.inl ⟨hS', hM', hT'⟩
    · exact absurd (step_median_answer_of_InSswap_both hn0 hn4 hS hS' hM) hM'
  · have hM' := step_median_answer_of_InSswap_both hn0 hn4 hS hS' hM
    exact Or.inr (Or.inr (Or.inr ⟨hS', hM', hT'⟩))
· exact Or.inr (Or.inr (Or.inl
    (crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS')))
```

For the refined productive endpoint:

```lean
Goal D :=
  IsConsensusConfig D ∨ CorrectResetSeed D ∨
    (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)
```

then the non-break/no-timer branch needs the local helper:

```lean
have hmax_zero_of_not_live :
    ∀ D, InSswap D -> ¬ MedianTimerAtLeast 1 D -> maxMedianTimer D = 0 := ...
```

and the break branch is still the same wrapper call:

```lean
exact Or.inr (Or.inr (Or.inl
  (crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS')))
```

### v4.30 edits still required

The restored proof still needs the v4.30 mechanical fixes:

```lean
-- old
exact Nat.zero_le _

-- v4.30-friendly
exact zero_le
```

```lean
step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
  (Dmax := Dmax) (i := i) (j := j) hn0 hS w

step_timer_le_of_InSswap (Rmax := Rmax) (Emax := Emax)
  (Dmax := Dmax) (i := i) (j := j) hn0 hS w
```

```lean
have hval : (D μ).1.rank.val = ceilHalf n - 1 :=
  congrArg (fun r : Fin n => r.val) hμ
```

Also, if the original proof has a raw projection from `Config.step_fst_state`, prefer a normalized state equality first:

```lean
have hfst_state :
    (D.step P μ v μ).1 =
      (transitionPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn0) (D μ, D v)).1 := by
  rw [Config.step_fst_state P D huv]
  change
    (transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn0) (D μ, D v)).1 =
    (transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn0) (D μ, D v)).1
  rfl
```

Then project from `hfst_state`, not from the raw `h_fst`:

```lean
rw [show (D.step P μ v μ).1.timer =
    (transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn0) (D μ, D v)).1.timer from
  congrArg (fun s : AgentState n => s.timer) hfst_state]
```

### Bottom line for timer_drain

Restoring from `4f9167ea5` should be substantially faster than re-proving it, because the main logical blocker was the break-to-CRS theorem interface. The likely remaining proof work is only v4.30 elaboration hygiene and replacing a few broad `simp_all`/raw projection patterns.

---

## 4. Arithmetic / `nlinarith` hole

Target:

```lean
7 * (Rmax + 4) * n * (n - 1) +
  n * (n - 1) +
  4 * Rmax * n * n ≤
18 * Rmax * n * n
```

Hypotheses:

```lean
hn4 : 4 ≤ n
hRmax : n ≤ Rmax
```

### Does the simple `set m := n - 1; have hm : m + 1 = n; nlinarith` work?

I cannot run Lean in this environment, so I cannot literally certify the exact tactic script. Mathematically, yes, that is the right normalization. In Lean, the most robust version is to rewrite `n` to `m + 1`, simplify `(m + 1) - 1`, prove the key linearized bound, and then let `nlinarith` finish.

Try this first:

```lean
by
  set m : ℕ := n - 1 with hmdef
  have hm : m + 1 = n := by
    dsimp [m]
    omega
  rw [← hm] at hn4 hRmax ⊢
  simp only [Nat.add_sub_cancel] at hn4 hRmax ⊢
  nlinarith [hn4, hRmax]
```

If that is still too much for `nlinarith`, use the explicit key estimate:

```lean
by
  set m : ℕ := n - 1 with hmdef
  have hm : m + 1 = n := by
    dsimp [m]
    omega
  rw [← hm] at hn4 hRmax ⊢
  simp only [Nat.add_sub_cancel] at hn4 hRmax ⊢
  have hkey : 29 * m ≤ 7 * Rmax * (m + 2) := by
    nlinarith [hn4, hRmax]
  have hmul : (m + 1) * (29 * m) ≤ (m + 1) * (7 * Rmax * (m + 2)) :=
    Nat.mul_le_mul_left (m + 1) hkey
  nlinarith [hmul]
```

Why this works mathematically:

```text
7*(R+4)*n*(n-1) + n*(n-1) + 4*R*n*n
= 7*R*n*(n-1) + 29*n*(n-1) + 4*R*n*n
```

It is enough to show:

```text
29*(n-1) ≤ 7*R*(n+1)
```

because multiplying by `n` gives:

```text
29*n*(n-1) ≤ 7*R*n*(n+1)
```

and then:

```text
7*R*n*(n-1) + 7*R*n*(n+1) + 4*R*n*n
= 18*R*n*n.
```

With `m = n - 1`, the key estimate becomes:

```text
29*m ≤ 7*R*(m+2)
```

which follows immediately from `4 ≤ m+1` and `m+1 ≤ R`.

### Possible Nat/ring issue

If the final `nlinarith [hmul]` still complains because of `Nat` multiplication normalization, insert one `ring_nf` after the `simp`:

```lean
  ring_nf at hmul ⊢
  nlinarith [hmul]
```

If `ring_nf` refuses because the goal is still over `Nat`, cast the arithmetic lemma to `Int` or prove the bound in `Nat` through the `hkey` multiplication as above. The `m` rewrite is still the right first move; the main problem is avoiding raw `n - 1` in a nonlinear natural-number inequality.

---

## Final actionable summary

1. **Delete the three step-level CRS/ARS theorems only after verifying the pushed tree has no wrapper/internal references.** In the described Q48 state, they are dead.
2. **Keep and repair `PEM_expected_timer_drain`.** It is live through `PEM_expected_median_correct_to_consensus`.
3. **For the five Time.lean holes:** `epidemic_to_consensus`, `allR_to_consensus`, the arithmetic obligation, and `PEM_hConsensusBound_from_bridge` are live in the CRS-only chain. `anyResetSeed_to_consensus` is live only if the bridge target still contains an ARS disjunct; otherwise it is dead.
4. **Restore timer_drain from `4f9167ea5` with wrapper replacement.** The old type mismatch is gone if all break branches call `crs_of_InSswap_break_with_MedC`.
5. **Use the `m := n - 1` arithmetic normalization.** The two-stage `hkey` proof is the safest Lean 4.30 shape for the line-952 arithmetic sorry.
