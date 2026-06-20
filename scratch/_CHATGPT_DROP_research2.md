# Q47 / research2 audit: SSExactMajority time-bound sorry dependencies

Date: 2026-06-20
Branch audited: `scratch`

I read the current `scratch` branch files around the time-bound layer, especially:

- `SSExactMajority/UpperBound/Time.lean`
- `SSExactMajority/UpperBound/Time/PhaseProofs.lean`
- `SSExactMajority/UpperBound/Time/CRSOdd.lean`
- `SSExactMajority/UpperBound/Time/CRSEven.lean`
- `SSExactMajority/UpperBound/Time/CRSEvenTimerPos.lean`
- `SSExactMajority/UpperBound/Time/DrainProductive.lean`

I did not run `lake build` in this environment; this is a mathematical/design audit from the source.

## Executive verdict

1. The original `timer_drain -> CRS_even` call with `MedianTimerAtLeast 1` passed into a theorem requiring median `timer = 0` was a real spec/type bug, not merely v4.30 proof noise.

2. The right fix is not to weaken the med-correct live-break conclusion to `ARS`. The mathematically right bridge is:

```lean
crs_of_InSswap_break_with_MedC
  : InSswap D -> MedianAnswerCorrect D ->
    ¬ InSswap (D.step P i j) ->
    CorrectResetSeed (D.step P i j)
```

with the timer split hidden internally. The current `scratch` branch already has this exact wrapper in `PhaseProofs.lean`, splitting even parity into median timer `0` vs `>= 1` and delegating the positive-timer branch to `step_InSswap_break_creates_CorrectResetSeed_even_timer_pos`.

3. The even `timer=0` / `timer>=1` distinction is genuine at the transition-trace level, but it should not be exposed in the high-level progress invariant. It is an implementation-level case split for the proof of the timer-agnostic break-to-CRS theorem.

4. `ARS` is structurally provable without `MedianAnswerCorrect`, but it is dangerous as a direct path-to-consensus target. If `AnyResetSeed` carries no answer correctness, then a theorem named/used as `anyResetSeed_to_consensus` is only sound if it proves a full reset/re-entry/re-computation path independent of the seed answer. It is not sound if it is just epidemic propagation of the seed answer.

5. The deepest design issue I see is not the timer split; it is whether `DecisionProgress` includes `ARS` as a correctness-level terminal progress disjunct. For the median-correct decision chain, `ARS` should be unnecessary. Prefer a CRS-only med-correct chain and reserve `ARS` for a separate reset/recovery subsystem.

6. There is also a global time-bound-spec issue already documented in `Time.lean`: `PEMProtocolCoupled` couples `trank = Rmax`, and `ConcretePEM n n n ...` has linear timer. The paper's O(n) expected parallel-time decision-window argument is for constant `trank` / constant timer budget. The Lean theorem statement must expose `T_timer` or assume `T_timer = O(1)`; otherwise the timer-drain bound scales as `T_timer * n(n-1)` interactions, i.e. `O(T_timer * n)` parallel time.

## A. The timer mismatch in `timer_drain -> CRS_even`

The old shape was mathematically invalid:

```lean
step_InSswap_break_creates_CorrectResetSeed
  ...
  (hT : forall μ, median μ -> timer μ = 0)
  (hS' : ¬ InSswap step)
  : CorrectResetSeed step
```

but `timer_drain` had:

```lean
hT : MedianTimerAtLeast 1 D
-- i.e. forall μ, median μ -> 1 <= timer μ
```

Those hypotheses are incompatible unless the median set is empty, which cannot happen under `InSswap` / `InSrank` with `n > 0`. So the old call was not a proof-engineering issue. It was a real theorem-interface mismatch.

The right abstraction is the timer-agnostic theorem:

```lean
crs_of_InSswap_break_with_MedC
  {D : Config (AgentState n) Opinion n}
  (hS : InSswap D)
  (hM : MedianAnswerCorrect D)
  (hS' : ¬ InSswap (D.step P i j)) :
  CorrectResetSeed (D.step P i j)
```

The current `scratch` branch implements exactly this architecture:

```lean
by_cases hpar : n % 2 = 0
· obtain <μ, hμ_med> := hS.toInSrank.exists_median ...
  by_cases hT0 : (D μ).1.timer = 0
  · build the old universal timer=0 hypothesis from uniqueness of median rank;
    use step_InSswap_break_creates_CorrectResetSeed
  · build MedianTimerAtLeast 1 from uniqueness of median rank and omega;
    use step_InSswap_break_creates_CorrectResetSeed_even_timer_pos
· use step_InSswap_break_creates_CorrectResetSeed_odd
```

This is the clean fix. It also means downstream code should not manually choose between `CRS_even` and `live_break_CRS`; it should call the timer-agnostic `crs_of_InSswap_break_with_MedC`.

## B. Why even `timer=0` and `timer>=1` differ

For odd `n`, there is a unique median rank. In `InSswap`, the median opinion determines the strict majority/tie answer via the sorted-rank invariant, so `opinionToAnswer medianInput = majorityAnswer D`. This is why the odd CRS theorem does not need `MedianAnswerCorrect`: the answer correctness is derived from the input/rank structure.

For even `n`, `ceilHalf n` is the lower median. The lower median's input alone does not determine the majority answer in all cases. In particular, the lower and upper median pair is the tie/strict-majority boundary. Therefore an even CRS proof needs some correctness information about the lower median answer. That is exactly `MedianAnswerCorrect`.

The timer distinction is transition-level:

- In the timer-zero branch, a reset is triggered by a median answer disagreement at the propagation stage. The existing theorem `step_InSswap_break_creates_CorrectResetSeed` assumes all median timers are `0`, then proves that if `InSswap` breaks, the two scheduled agents become Resetting and the reset answer is the median's old answer. `MedianAnswerCorrect` transports that answer to `majorityAnswer`.

- In the positive-timer branch, not every median interaction can reset. The proof has to show that if `InSswap` breaks while the median timer is at least `1`, then the trace classification forces a median--max interaction and the median timer is actually `<= 1`, hence exactly `1`. Then the timer-one trace resets both scheduled agents with `Rmax/L`, and the answer copied from the median is correct by `MedianAnswerCorrect`.

That is why `step_InSswap_break_creates_CorrectResetSeed_even_timer_pos` has this shape:

```lean
(hS : InSswap D)
(hM : MedianAnswerCorrect D)
(hPar : n % 2 = 0)
(hT : MedianTimerAtLeast 1 D)
(hS' : ¬ InSswap (D.step P i j))
: CorrectResetSeed (D.step P i j)
```

It is a real theorem, not a weakened ARS theorem. It proves CRS by a stronger classification of the break step.

## C. Can `live_break_CRS` be proved, or should it be ARS?

With `MedianAnswerCorrect`, `live_break_CRS` should be CRS, not ARS.

Precise theorem to use/keep:

```lean
theorem live_break_CRS
    (hn4 : 4 <= n) (hn0 : 0 < n) (hRmax : n <= Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    (hM : MedianAnswerCorrect D)
    (hT : MedianTimerAtLeast 1 D)
    {i j : Fin n}
    (hS' : ¬ InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)) :
    CorrectResetSeed (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)
```

Implementation:

```lean
by_cases hpar : n % 2 = 0
· exact step_InSswap_break_creates_CorrectResetSeed_even_timer_pos
    hn4 hn0 hRmax hS hM hpar hT hS'
· exact step_InSswap_break_creates_CorrectResetSeed_odd
    hn4 hn0 hRmax hS hpar hS'
```

Even better, do not expose `hT` at all:

```lean
exact crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS'
```

because the wrapper already splits timer `0` vs positive.

Without `MedianAnswerCorrect`, the even case can generally only give structural reset information, i.e. `ARS`, not `CRS`. The roles/resetcount/leader fields do not require answer correctness, but `CorrectResetSeed` does. Thus:

```lean
InSswap D -> ¬ InSswap step -> AnyResetSeed step
```

is plausible and useful as a structural theorem; however,

```lean
InSswap D -> ¬ InSswap step -> CorrectResetSeed step
```

is not plausible in even parity without either `MedianAnswerCorrect` or a theorem proving the lower-median answer from some other invariant.

## D. ARS audit

`ARS` is useful, but it is not a substitute for `CRS` in the correctness chain.

By definition as described in the prompt:

```lean
AnyResetSeed C := exists μ,
  role μ = Resetting ∧ resetcount μ = Rmax ∧ leader μ = L
```

It says nothing about the answer field. Therefore a downstream theorem

```lean
anyResetSeed_to_consensus : ARS C -> expected time to IsConsensusConfig is finite / bounded
```

is only sound if its proof is a full reset/recovery proof. It must not be a mere epidemic propagation proof.

Why: if the seed answer is wrong, propagation can spread the wrong answer. `ARS` alone does not tell you that the seed answer equals `majorityAnswer C`, nor that all Resetting agents agree with the majority. By contrast, `CRS` explicitly carries:

- one Resetting leader with resetcount exceeding nonresetting count,
- correct answer for that witness,
- every Resetting agent has positive resetcount and correct answer.

Those are exactly the correctness facts needed for a direct epidemic-to-consensus route.

So there are two safe designs:

### Safe design 1: remove ARS from the median-correct decision progress chain

Use:

```lean
DecisionProgressMC D :=
  IsConsensusConfig D ∨
  CorrectResetSeed D ∨
  (InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D ∧ TimerBounded D) ∨
  (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)
```

The current `DrainProductive.lean` is close to this design: the productive endpoint is

```lean
IsConsensusConfig D ∨ CorrectResetSeed D ∨
  (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)
```

This is the right shape. It avoids the circular weak exit `¬ live` and avoids ARS.

### Safe design 2: keep ARS, but route it through reset/re-entry

If `ARS` remains in `DecisionProgress`, the downstream theorem must be shaped more like:

```lean
AnyResetSeed C ->
  expected time to (InSrank ∨ InSswap ∨ IsConsensusConfig ∨ CorrectResetSeed) is bounded
```

or:

```lean
AnyResetSeed C ->
  expected time to a clean post-reset/rerank state is bounded,
```

followed by a fresh exact-majority computation. It must not claim that an answerless seed directly implies correct consensus.

## E. DecisionProgress design

The prompt's predicate was:

```lean
DecisionProgress =
  IsConsensusConfig ∨ CRS ∨ ARS ∨
  (InSswap ∧ MedCorrect ∧ TimerAtLeast1 ∧ TimerBounded)
```

This is too coarse for the median-correct timer-drain chain. The fourth disjunct is a working state. If it exits by breaking `InSswap`, then under `MedCorrect` the exit should be `CRS`, not merely `ARS`. If it exits by timer draining, the productive nonterminal endpoint is not `¬ TimerAtLeast1` abstractly; it should be the concrete zero-timer endpoint:

```lean
InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0
```

Then a separate zero-timer/reset-trigger stage can push to either consensus or CRS.

Recommended split:

1. **Median-correct productive drain**

```lean
InSswap ∧ MedianAnswerCorrect ∧ MedianTimerAtLeast 1 ∧ TimerBounded
  --> expected time to
IsConsensusConfig ∨ CorrectResetSeed ∨
  (InSswap ∧ MedianAnswerCorrect ∧ maxMedianTimer = 0)
```

2. **Zero-timer trigger/decision stage**

```lean
InSswap ∧ MedianAnswerCorrect ∧ maxMedianTimer = 0
  --> expected time to IsConsensusConfig ∨ CorrectResetSeed
```

3. **Correct reset epidemic/recovery**

```lean
CorrectResetSeed --> expected time to IsConsensusConfig
```

This is better than putting `ARS` into the same `DecisionProgress` predicate.

## F. Minimal root theorem set

For the 10-sorry dependency graph described in the prompt, the minimal root set is smaller than 10. The real mathematical roots are:

### Root 1: odd break-to-CRS answer correctness

```lean
step_InSswap_break_creates_CorrectResetSeed_odd
  : InSswap D -> n % 2 ≠ 0 -> ¬ InSswap step -> CorrectResetSeed step
```

The structural reset facts are not the hard part. The hard part is the answer-correctness bridge:

```lean
opinionToAnswer (median input) = majorityAnswer D
```

from sorted ranks and odd parity. This is mathematically valid.

### Root 2: even timer-zero break-to-CRS

```lean
step_InSswap_break_creates_CorrectResetSeed
  : InSswap D -> MedianAnswerCorrect D ->
    (forall median, timer = 0) ->
    ¬ InSswap step -> CorrectResetSeed step
```

This is valid, but it should be treated as a helper only. It should not be called from a live-timer proof.

### Root 3: even positive-timer break-to-CRS

```lean
step_InSswap_break_creates_CorrectResetSeed_even_timer_pos
  : InSswap D -> MedianAnswerCorrect D -> n % 2 = 0 ->
    MedianTimerAtLeast 1 D ->
    ¬ InSswap step -> CorrectResetSeed step
```

This is the correct replacement for the old bogus call in `timer_drain`.

### Root 4: timer-agnostic wrapper

```lean
crs_of_InSswap_break_with_MedC
  : InSswap D -> MedianAnswerCorrect D ->
    ¬ InSswap step -> CorrectResetSeed step
```

This wrapper should be the only break-to-CRS theorem used by higher-level expected-time code.

### Root 5: productive timer drain

```lean
timer_drain_to_zero_productive
  : InSswap C -> MedianAnswerCorrect C -> MedianTimerAtLeast 1 C ->
    IsTimerBoundedConfig T_timer C ->
    E[T to consensus ∨ CRS ∨ (InSswap ∧ MAC ∧ maxMedianTimer = 0)]
      <= T_timer * n * (n - 1)
```

This is the right high-level lemma. It uses Root 4 in the `hInvStep` and endpoint cases.

### Root 6: zero-timer stage

A zero-timer stage should connect:

```lean
InSswap ∧ MedianAnswerCorrect ∧ maxMedianTimer = 0
```

to:

```lean
IsConsensusConfig ∨ CorrectResetSeed
```

In the older prompt, this corresponds roughly to `allR_to_consensus` / reset-trigger composition. It should not require `MedianTimerAtLeast 1`.

### Root 7: CRS-to-consensus

```lean
CorrectResetSeed C -> expected time to IsConsensusConfig is bounded / finite
```

This is safe because CRS carries answer correctness.

### Optional root: ARS-to-recovery, not ARS-to-consensus-by-epidemic

Only needed if you keep ARS in the global progress predicate:

```lean
AnyResetSeed C -> expected time to clean reset/re-entry state is bounded
```

Do not use an answerless `ARS` as if it were `CRS`.

## G. Answers to the four explicit questions

### 1. Is the timer=0 vs timer>=1 split genuine?

Yes at the transition-trace level; no at the high-level progress API.

It is genuine because the phase4 propagation traces distinguish median timer zero from timer one/positive cases. In even parity, positive timer reset requires a more constrained median--max classification. But the high-level expected-time proof should hide the split behind:

```lean
crs_of_InSswap_break_with_MedC
```

### 2. Can live_break_CRS be proved, or should it be weakened to ARS?

It can and should be proved as CRS, provided `MedianAnswerCorrect` is available. The current branch's `step_InSswap_break_creates_CorrectResetSeed_even_timer_pos` is exactly the even positive-timer proof, and `crs_of_InSswap_break_with_MedC` combines it with the timer-zero and odd cases.

If `MedianAnswerCorrect` is absent in even parity, then CRS is too strong and the right structural theorem is only ARS.

### 3. Is there a design bug in the dependency chain?

There are two design bugs to avoid:

1. The old direct call from `MedianTimerAtLeast 1` into a timer-zero CRS theorem was a real bug. It is fixed by the timer-agnostic wrapper.

2. `ARS` must not be treated as a direct correctness seed. If `DecisionProgress` includes `ARS`, the downstream proof must be reset/recovery/re-entry, not epidemic propagation of an answer.

There is also a theorem-statement risk: if the final claimed time bound is for `ConcretePEM n n n ...` or any coupled setting with `trank = Rmax >= n`, then the timer-drain term is not O(n) parallel time unless a separate argument removes the linear timer factor. The paper's O(n) expected decision time requires constant timer budget or an explicit `T_timer = O(1)` hypothesis.

### 4. What is the minimal set of sorries that unlocks everything else?

Minimal if you choose the CRS-only median-correct chain:

1. Odd break-to-CRS answer correctness.
2. Even timer-zero break-to-CRS.
3. Even positive-timer break-to-CRS.
4. Timer-agnostic wrapper `crs_of_InSswap_break_with_MedC`.
5. Productive timer drain to `consensus ∨ CRS ∨ zero-timer productive endpoint`.
6. Zero-timer trigger/decision stage to `consensus ∨ CRS`.
7. CRS-to-consensus.
8. Final expected-time composition/arithmetic.

The original ARS theorem is not on the minimal path if the median-correct chain always upgrades a break to CRS. If you keep ARS in `DecisionProgress`, then add a separate ARS-to-reset-recovery theorem, but do not use ARS as a correctness seed.

## H. Recommended Lean-level edits

1. Make higher-level proofs call only:

```lean
crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS'
```

not the parity/timer-specific lemmas.

2. Rename the positive timer bridge if desired:

```lean
live_break_CRS := step_InSswap_break_creates_CorrectResetSeed_even_timer_pos + odd case
```

but prefer the timer-agnostic wrapper.

3. Replace weak exit predicates of the form:

```lean
¬ (InSswap ∧ MedianTimerAtLeast 1)
```

with a productive endpoint:

```lean
InSswap ∧ MedianAnswerCorrect ∧ maxMedianTimer = 0
```

This avoids circular progress reasoning and matches the current `DrainProductive.lean` design.

4. Split `DecisionProgress` into two predicates:

```lean
DecisionProgressMC
ResetRecoveryProgress
```

where `ARS` appears only in reset recovery, not in the med-correct decision chain.

5. In the final theorem statement, expose the timer budget:

```lean
T_timer
```

or state the bound for a protocol family with constant `trank`. Do not silently claim the paper's O(n) expected parallel-time bound for a protocol instance whose timer is linear in `n`.
