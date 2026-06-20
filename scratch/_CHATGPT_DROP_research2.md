# Q47/Q49 research2 audit: SSExactMajority time-bound dependencies and timer-drain restoration

Date: 2026-06-20
Branch audited: `scratch`

## Scope and caveat

I audited the accessible `scratch` branch around the time-bound layer and tried to fetch the historical ref requested in Q49:

```text
4f9167ea5
```

The GitHub connector returned `No commit found` for both `fetch_file` and `fetch_commit`, and commit search did not find that SHA. Therefore I cannot honestly claim that I inspected the exact `4f9167ea5` lines 9658--9973. What I could inspect:

- current `SSExactMajority/UpperBound/Time.lean`
- current `SSExactMajority/UpperBound/Time/PhaseProofs.lean`
- current `SSExactMajority/UpperBound/Time/CRSOdd.lean`
- current `SSExactMajority/UpperBound/Time/CRSEven.lean`
- current `SSExactMajority/UpperBound/Time/CRSEvenTimerPos.lean`
- current `SSExactMajority/UpperBound/Time/PolynomialBound.lean`
- current `SSExactMajority/UpperBound/Time/DrainProductive.lean`
- accessible historical commits around `timer_drain`, especially commit `43d0010352bc5e7504b00fd39a2ed98346f18345` and later commits recorded by GitHub search.

The conclusions below are therefore a source-level restoration audit, not a verified build result.

---

# Q49 executive verdict

Yes: the old `PEM_expected_timer_drain` proof is very likely salvageable by replacing the bogus CRS call with `crs_of_InSswap_break_with_MedC`, but I would **not** restore it as a blind one-line patch. The current branch already contains two better, proved descendants of the old strategy:

1. `PEM_expected_timer_drain_poly` in `PolynomialBound.lean`, with target

```lean
IsConsensusConfig D ∨ CorrectResetSeed D ∨
  ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
```

2. `timer_drain_to_zero_productive` in `DrainProductive.lean`, with the stronger/productive target

```lean
IsConsensusConfig D ∨ CorrectResetSeed D ∨
  (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)
```

For the current single remaining `StepProofs` sorry, the best strategy is:

- if the caller at `Time.lean:890` expects the **old weak exit** theorem, port `PEM_expected_timer_drain_poly` almost verbatim;
- if the caller can accept the **productive endpoint**, port `timer_drain_to_zero_productive` instead;
- in either case, every place that previously tried to prove CRS from an `InSswap` break should call:

```lean
crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS'
```

not any timer-specific CRS theorem.

The old exact change:

```lean
-- OLD, invalid when hT : MedianTimerAtLeast 1 D
step_InSswap_break_creates_CorrectResetSeed hn4 hn0 hRmax hS hM hT hS'

-- NEW, type-correct and semantically right
crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS'
```

is mathematically correct. But depending on the old proof's goal nesting, the term must be wrapped in the appropriate `Or` constructors.

---

# 1. Does `crs_of_InSswap_break_with_MedC` match `PEMProtocolCoupled`?

Yes, it should.

In the current source, `PEMProtocolCoupled` is an abbrev:

```lean
abbrev PEMProtocol (n trank Rmax Emax Dmax : Nat) (hn : 0 < n) :
    Protocol (AgentState n) Opinion Output :=
  protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)

abbrev PEMProtocolCoupled (n Rmax Emax Dmax : Nat) (hn : 0 < n) :
    Protocol (AgentState n) Opinion Output :=
  PEMProtocol n Rmax Rmax Emax Dmax hn
```

Therefore:

```lean
PEMProtocolCoupled n Rmax Emax Dmax hn0
```

unfolds to:

```lean
protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
```

If your branch's `crs_of_InSswap_break_with_MedC` is stated directly using `protocolPEM`, then the call should close with one of:

```lean
exact crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS'
```

or, if Lean does not unfold the abbrevs automatically:

```lean
simpa [PEMProtocolCoupled, PEMProtocol] using
  (crs_of_InSswap_break_with_MedC
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn4 hn0 hRmax hS hM hS')
```

The current `scratch` branch already uses `crs_of_InSswap_break_with_MedC` with `PEMProtocolCoupled` in `PolynomialBound.lean` and `DrainProductive.lean`, so definitional equality is not the serious risk.

The serious risk is **import direction**. If the remaining theorem is in `StepProofs.lean`, and `crs_of_InSswap_break_with_MedC` currently lives in a higher file that imports `StepProofs.lean`, then directly importing it may create a cycle. In that case, move the wrapper down next to the timer-specific CRS proofs, or create a lower `CRSBreak.lean` file containing:

```lean
step_InSswap_break_creates_CorrectResetSeed_odd
step_InSswap_break_creates_CorrectResetSeed
step_InSswap_break_creates_CorrectResetSeed_even_timer_pos
crs_of_InSswap_break_with_MedC
```

Then both `StepProofs.lean` and `Time.lean` can import that lower wrapper.

---

# 2. What changes are needed besides the CRS call?

## 2.1 Replace the break branch according to the exact goal shape

There are two common goal shapes.

### Weak-exit timer drain

If the restored theorem's target is:

```lean
Goal D :=
  IsConsensusConfig D ∨ CorrectResetSeed D ∨
    ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
```

then in a proof obligation returning `Goal (D.step P i j)`, the CRS branch is:

```lean
exact Or.inr (Or.inl
  (crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS'))
```

In a proof obligation returning `Inv step ∨ Goal step`, it is:

```lean
exact Or.inr (Or.inr (Or.inl
  (crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS')))
```

but note: for the weak-exit goal, an arbitrary `InSswap` break can also be sent to the exit branch:

```lean
exact Or.inr (Or.inr (Or.inr (fun h => hS' h.1)))
```

This is what `PEM_expected_timer_drain_poly` does in its `hInvStep` for arbitrary scheduler pairs. It reserves the CRS proof for the **chosen median--max descent pair** branch, where a break is treated productively.

### Productive timer drain

If the target is:

```lean
Goal D :=
  IsConsensusConfig D ∨ CorrectResetSeed D ∨
    (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)
```

then an `InSswap` break has no weak exit branch. It must be CRS:

```lean
exact Or.inr (Or.inr (Or.inl
  (crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS')))
```

This is the cleaner high-level theorem and matches `DrainProductive.lean`.

## 2.2 Keep `hT : MedianTimerAtLeast 1` for timer descent; just stop passing it to CRS

The old proof likely uses `hT` in three legitimate places:

1. to initialize the invariant;
2. to show the chosen median has positive timer;
3. in `hDescent`, to split:

```lean
by_cases hTimer2 : 2 <= (D μ).1.timer
· -- timer >= 2: strict timer descent, invariant preserved
· -- timer = 1: chosen median--max step drains to 0, so goal/exit is reached
```

Do not remove `hT`. Only remove it from the CRS creation theorem call.

## 2.3 Ensure the theorem uses the correct median-correct preservation lemma

The current branch has/use variants named:

```lean
step_median_answer_of_InSswap_both
step_median_answer_of_InSswap_both_v2
```

If the restored body came from an older commit, it may call the wrong suffix. This is a simple rename/import issue. The intended proof obligation is:

```lean
have hM' : MedianAnswerCorrect (D.step P i j) :=
  step_median_answer_of_InSswap_both hn0 hn4 hS hS' hM
```

or `_v2` depending on the file.

## 2.4 If the old proof uses `Finite.surjective_of_injective`, check API drift

I saw current code using both styles in different places:

```lean
Finite.injective_iff_surjective.mp hS.toInSrank.ranks_inj
```

and older code may use:

```lean
Finite.surjective_of_injective hInj
```

If v4.30 rejects the latter, replace it with:

```lean
have hsurj : Function.Surjective (fun v => (D v).1.rank) :=
  Finite.injective_iff_surjective.mp hS.toInSrank.ranks_inj
```

This is unrelated to the CRS bug.

## 2.5 Keep the localized transition-unfold proofs, but avoid global `simp_all`

The timer-drain body contains local proofs such as:

```lean
show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
  (D μ, D v)).1.timer = (D μ).1.timer - 1

unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
  phase4_swap phase4_decide phase4_propagate
simp only [hRDapp, hsi, hsv, ne_eq,
  role_settled_ne_resetting,
  not_true_eq_false, not_false_eq_true,
  false_and, and_false, if_false,
  and_self, if_true, h_no_swap, hμ_med, hv_max]
by_cases hpar : n % 2 = 0
· simp only [hpar, if_true]
  split_ifs <;> dsimp only [] <;> omega
· simp only [hpar, if_false]
  split_ifs <;> dsimp only [] <;> omega
```

This pattern is present in current proved files and is much safer in v4.30 than the old large-proof pattern:

```lean
split_ifs <;> simp_all
```

If the restored 310-line body has `split_ifs <;> simp_all` after unfolding the whole transition, replace it with the localized `simp only [...]` style above.

---

# 3. Are the `split_ifs` in timer_drain broken in v4.30?

The evidence says: **the small/local timer-drain `split_ifs` are salvageable and probably already safe**.

The v4.30 disaster mode was the CRS construction proof style: unfold a deeply nested `transitionPEM`, then `split_ifs <;> simp_all` across a huge context. That can explode or produce brittle `change` failures.

Timer drain's transition computations are much narrower. They only need timer equality for the selected median after a median--max interaction. Current proved code uses exactly this style in two places:

1. `timer_ge_two_descent_step`: proves timer drops by one when pre-timer is at least `2`.
2. `PEM_expected_timer_drain_poly` / `timer_drain_to_zero_productive`: handles the `timer = 1` exit by proving post median timer is `0`.

Those proofs still use `split_ifs`, but only after pre-normalizing nearly all relevant branches with known hypotheses (`hRDapp`, settled roles, no-swap, median rank, max rank, timer value). That is the right v4.30-safe style.

So: do not fear `split_ifs` in timer_drain as such. Fear unbounded `simp_all` after a full transition unfold. If the old proof uses `split_ifs <;> dsimp only [] <;> omega` or can be changed to that, it is fine.

---

# 4. Is one-line restoration enough?

Likely **almost**, but not literally guaranteed.

The CRS-call change is the only mathematical/spec correction. The remaining possible compile blockers are ordinary v4.30/API issues:

- theorem suffix/name drift (`step_median_answer_of_InSswap_both` vs `_v2`);
- `Finite.surjective_of_injective` API drift;
- `congr_arg` vs `congrArg` spelling if the restored code is old;
- `simpa [PEMProtocolCoupled, PEMProtocol]` needed around protocol abbrev unfolding;
- replacing large `simp_all` blocks with local `simp only` blocks;
- final arithmetic may need `norm_num`, `omega`, or `ring_nf` adjustment.

None of these indicate a design rewrite is needed.

However, if the old proof's target is the weak exit:

```lean
IsConsensusConfig ∨ CorrectResetSeed ∨ ¬ (InSswap ∧ MedianTimerAtLeast 1)
```

then it is formally salvageable but compositionally less clean. It can exit through `¬live`, which may be circular or unproductive for the later consensus chain. The current `DrainProductive.lean` target is better because it converts timer expiration into the concrete useful endpoint:

```lean
InSswap ∧ MedianAnswerCorrect ∧ maxMedianTimer = 0
```

So the engineering recommendation is:

- for minimal caller compatibility: restore the old weak-exit theorem using `PEM_expected_timer_drain_poly`;
- for the final design: use or port `timer_drain_to_zero_productive`.

---

# 5. Concrete restoration patch sketch

Assume the old proof has:

```lean
set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
set Goal := fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
  ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
set Inv := fun D => InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
```

## 5.1 Arbitrary-step invariant branch

If the old `hInvStep` had:

```lean
intro D ⟨hS, hM, hT⟩ hG i j
by_cases hS' : InSswap (D.step P i j)
· ... preserve Inv or exit timer-live ...
· exact Or.inr (Or.inr (Or.inl
    (step_InSswap_break_creates_CorrectResetSeed hn4 hn0 hRmax hS hM hT hS')))
```

replace with either the productive CRS branch:

```lean
· exact Or.inr (Or.inr (Or.inl
    (crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS')))
```

or, for the weak-exit theorem, the simpler exit branch:

```lean
· exact Or.inr (Or.inr (Or.inr (fun hLive => hS' hLive.1)))
```

The second version is what the current `PEM_expected_timer_drain_poly` architecture uses for arbitrary scheduler pairs.

## 5.2 Chosen median--max descent branch

In the deterministic descent witness, if the chosen median--max step breaks `InSswap`, use CRS:

```lean
by_cases hS' : InSswap (D.step P μ v)
· -- prove invariant and strict maxMedianTimer descent
· right
  exact Or.inr (Or.inl
    (crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS'))
```

For the productive target, the nesting is:

```lean
· exact Or.inr (Or.inr (Or.inl
    (crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS')))
```

## 5.3 Protocol abbrev fallback

If Lean complains about the step protocol not matching:

```lean
have hcrs : CorrectResetSeed (D.step P i j) := by
  subst P
  simpa [PEMProtocolCoupled, PEMProtocol] using
    (crs_of_InSswap_break_with_MedC
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax hS hM hS')
```

or avoid `set P` in the call site and write the step explicitly.

---

# 6. Recommended theorem to restore

If the caller at `Time.lean:890` truly expects the old theorem name/signature `PEM_expected_timer_drain`, restore it as a wrapper around the already-proved polynomial theorem shape, not by resurrecting all 310 historical lines.

Example, if the old expected target is weak-exit:

```lean
 theorem PEM_expected_timer_drain
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (T_timer : ℕ)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (hTimerLo : MedianTimerAtLeast 1 C)
    (hTimerHi : IsTimerBoundedConfig T_timer C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
        ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)) ≤
      ((T_timer * n * (n - 1) : ℕ) : ENNReal) := by
  exact PEM_expected_timer_drain_poly
    hn4 hn0 hRmax T_timer C hSswap hMedCorrect hTimerLo hTimerHi
```

If the old theorem has `T_timer = 7 * (Rmax + 4)` baked in, instantiate the wrapper:

```lean
  simpa using
    (PEM_expected_timer_drain_poly
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax (7 * (Rmax + 4)) C
      hSswap hMedCorrect hTimerLo hTimerHi)
```

If the caller can consume the productive endpoint, prefer:

```lean
exact timer_drain_to_zero_productive
  hn4 hn0 hRmax T_timer C hSswap hMedCorrect hTimerLo hTimerHi
```

This avoids weak `¬live` exits and is the better final design.

---

# 7. Answers to the explicit Q49 questions

## 1. What needs to change besides the CRS call?

Mathematically, nothing major. Engineering-wise:

- wrap the new CRS term in the correct `Or` nesting;
- possibly add `simpa [PEMProtocolCoupled, PEMProtocol]` for protocol abbrev unfolding;
- adjust theorem names (`step_median_answer_of_InSswap_both` vs `_v2`);
- replace any large `split_ifs <;> simp_all` with local `simp only [...]` plus `split_ifs <;> dsimp only [] <;> omega`;
- check `Finite.injective_iff_surjective.mp` vs older finite-surjectivity APIs;
- consider replacing the restored body with a thin wrapper around `PEM_expected_timer_drain_poly` or `timer_drain_to_zero_productive` if those are available in the import graph.

## 2. Are there other v4.30 blockers in the timer_drain body?

Likely only small API/tactic blockers, not design blockers. The current branch demonstrates that the timer-drain split-ifs are manageable in v4.30 when localized. The fragile proof style was the old CRS transition case analysis, not the timer-drain potential proof.

Potential blockers to expect:

- timeout if old code uses `simp_all` globally;
- finite-rank surjectivity API name changes;
- theorem rename/suffix drift;
- final `norm_cast`/arithmetic cleanup.

None require a full rewrite.

## 3. Is the proof salvageable, or does it need full rewrite?

Salvageable.

The minimal salvage is replacing the bad CRS call and doing minor v4.30 cleanup. The robust salvage is to reuse the current proven `PEM_expected_timer_drain_poly`/`DrainProductive` skeleton rather than resurrecting the old 310-line body. If you need the old name because `Time.lean:890` calls it, make `PEM_expected_timer_drain` a wrapper around the proven theorem with the matching target.

My recommendation:

1. First try a wrapper around `PEM_expected_timer_drain_poly` if the target matches.
2. If the target wants productive zero endpoint, use `timer_drain_to_zero_productive`.
3. Only if imports prevent those wrappers, paste the old proof body and replace the CRS call with `crs_of_InSswap_break_with_MedC`, using localized `simp only` for transition timer equalities.

---

# 8. Final restoration strategy

The shortest safe path for the remaining `StepProofs` sorry is probably:

```lean
-- in StepProofs.lean, after importing the file that defines PEM_expected_timer_drain_poly
 theorem PEM_expected_timer_drain ... := by
  simpa [expected target definitions, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (PEM_expected_timer_drain_poly
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax T_timer C hSswap hMedCorrect hTimerLo hTimerHi)
```

If import direction prevents this, move the timer-drain proof itself to a lower module where both `StepProofs.lean` and `Time.lean` can import it. Do not reintroduce dead `CRS_even`/`CRS_odd`/`ARS` dependencies. The one live break-to-reset dependency should be exactly:

```lean
crs_of_InSswap_break_with_MedC
```
