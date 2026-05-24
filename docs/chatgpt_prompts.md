# ChatGPT Pro prompts for the time-bound formalization

Three prompts, paste into ChatGPT Pro one at a time (or send via the
chatgpt-bridge).  Each is self-contained and produces a discrete
artifact.

---

## Prompt 1 — Probability foundation decision memo

**Target output**: `docs/TIME_BOUND_PLAN_A.md` (~ 200–400 lines).

```
You are advising a Lean 4 / Mathlib formalization of the
Kanaya-Eguchi-Sasada-Ooshita-Inoue (2025) self-stabilizing exact
majority protocol.  The qualitative half is done: a top-level theorem
`P_EM_solves_SSEM_final` (no external hypotheses, axioms only
`[propext, Classical.choice, Quot.sound]`) states "for n ≥ 4 there
exists a scheduler driving the concrete protocol to consensus."

We now need the *time* half under uniform random scheduling.  The paper's
Theorem 3 lower bound is Ω(n) expected parallel time and Ω(n log n)
parallel time with high probability; §5.2 / Theorem 4 gives O(n)
expected parallel time and O(n log n) parallel time with high
probability for the concrete protocol.

Population-protocol time model (Kanaya §2): scheduler picks an ordered
pair (i, j), i ≠ j, uniformly at random; t sequential picks = t/n
parallel rounds.

Decide and document, for our Lean 4 / Mathlib v4.27.0 codebase:

1. **Probability foundation choice**.  Compare:
   (A) `PMF`-based: each step is a `PMF.uniformOfFinset` on
       off-diagonal pairs; trajectories via `PMF.bind`.  Expected
       hitting time via the tail-sum formula `∑ P[T > t]`.
   (B) `MeasureTheory.ProbabilityTheory.kernel`-based: the protocol is
       a discrete-time Markov kernel on `Config Q Opinion n`; use
       `IsStoppingTime` / `MeasureTheory.integral` for the expectation.
   For each, give the relevant Mathlib namespaces, key lemmas
   (`PMF.bind_apply`, `kernel.iterate`, `ProbabilityTheory.stoppingTime`,
   etc.), and pros/cons for our specific problem (finite state space,
   integer-valued stopping time, need closed-form bounds).  Make a
   recommendation.

2. **Expected hitting time definition**.  Write out the precise Lean
   `noncomputable def expectedHittingTime` for your recommended
   foundation, with all necessary `Classical`/`Decidable` arguments
   spelled out and with a short explanation of why this is the right
   form.  Confirm the definition is well-typed in Mathlib v4.27.0.

3. **`parallelTime` definition**.  Confirm `parallelTime T n = T / n`
   on `ENNReal` is the correct lift of "sequential ÷ n" for our
   `expectedHittingTime` outputs.  Address the `T = ⊤` case.

4. **Statement style for the main theorems**.  Compare:
   - explicit closed-form expected bounds:
     `c * n ≤ parallelTime ...` and `parallelTime ... ≤ C * n`
   - explicit high-probability bounds:
     `c * n * Real.log n` / `C * n * Real.log n`
   - `Asymptotics.IsBigO`-based statements for the corresponding
     expected-time functions or tail bounds
   Recommend one (note: the paper's bounds are quantitative, so
   explicit constants are achievable).

Deliver as a markdown document with the four sections above.  Cite
Mathlib lemma names exactly (no inventing).  Keep recommendations
opinionated — we will follow them.
```

---

## Prompt 2 — Theorem 3 proof strategy

**Target output**: `docs/TIME_BOUND_PLAN_B.md` (~ 200 lines).

```
Same context as Prompt 1.  Now design the Lean 4 / Mathlib proof of
Theorem 3 of Kanaya et al. 2025: any silent self-stabilizing exact
majority protocol requires Ω(n) expected **parallel** time and
Ω(n log n) parallel time with high probability to reach a safe
configuration.

We already have:
- Theorem 2 (space lower bound): `silent SSEM ⇒ ≥ n distinct states`,
  proved as `SSEM.space_lower_bound` in `LowerBound/Space.lean`.
- The uniform random pair-selection model.

Kanaya §5.1 proves this through a two-agent interaction waiting-time
argument, not an Ω(n log n) expected coupon-collector lower bound.  First
check the displayed tail calculation carefully: a single fixed-pair
geometric wait appears to give probability about n^{-α} for waiting
Θ(n² log n) interactions, not probability 1 - O(1/n).  If that reading is
right, say so directly and separate the expected lower-bound proof from the
blocked whp statement.  Then give:

1. **Precise mathematical statement of the geometric waiting-time
   lemma** in standalone form: if a repair requires one unordered pair
   among n agents to interact, and the scheduler samples ordered
   off-diagonal pairs uniformly, then the expected sequential wait is
   n(n-1)/2.  State exactly what the Θ(n² log n) tail actually proves,
   and whether it is strong enough for the paper's whp lower bound.

2. **Lean 4 / Mathlib status**: does Mathlib have any of:
   - Geometric-distribution expectation/tail lemmas over `PMF` or
     `ENNReal`
   - Bernoulli-trial waiting-time lemmas
   - `ProbabilityTheory.HittingTime` lower bounds for discrete chains
   If yes, give exact references.  If no, sketch a standalone proof
   (with concrete Lean tactic sequences) using `Mathlib.Combinatorics`
   / `Mathlib.Analysis.SpecialFunctions.Log` / etc.

3. **Lifting Lemma 4 to Theorem 3**: the precise sequence of
   transformations needed.  Explain how the distinct A-states in a
   silent configuration produce a modified unsafe configuration, why
   silence makes one particular pair interaction necessary, and why
   sequential time / n gives Ω(n) expected parallel time.  For the whp
   part, either give the missing amplification argument or mark it as a
   mathematical blocker.

4. **Anticipated Mathlib gaps**: list everything the proof needs that
   Mathlib does not currently have.  This will become a side-quest of
   PR-able lemmas.

Deliver as markdown.  Be concrete.  Cite Mathlib namespaces exactly.
```

---

## Prompt 3 — §5.2 upper bound phase decomposition

**Target output**: `docs/TIME_BOUND_PLAN_C.md` (~ 300 lines).

```
Same context as Prompts 1 & 2.  Now design the Lean 4 / Mathlib proof
of the O(n) expected parallel time and O(n log n) high-probability
parallel time upper bound for the concrete protocol
`protocolPEM n n n (rankDeltaOSSR n Emax Dmax hn)`.

We already have:
- Qualitative convergence: `P_EM_solves_SSEM_final`.
- Phase decomposition (qualitative):
  Init → InSrank (ranking) → InSswap (swap) → IsConsensusConfig
  (decision).
- Concrete proofs `ranking_field_proof`, `swap_reaches_Sswap_*`,
  `burmanConvergence_concrete` covering each transition.

Kanaya §5.2 proves that a constant-probability O(n)-parallel-time window
reaches the silent target set.  This gives O(n) expected parallel time;
repeating O(log n) windows gives O(n log n) parallel time with high
probability.

Give:

1. **Phase-by-phase parallel-time bound (precise constants where
   possible)**:
   - Phase A (ranking, Burman 2021 §3): expected sequential time
     until `InSrank` reached.
   - Phase B (swap): expected sequential time from `InSrank` until
     `InSswap`.
   - Phase C (decision): expected sequential time from `InSswap` until
     `IsConsensusConfig` *given correct ranking*.
   - Reset cycle: expected number of re-entries before consensus locks.
   For each, state the asymptotic constant + the specific potential
   function (`misorderedCount`, `wrongAnswerCount`, `phiCount`) that
   drives the descent.  Reference the Lean theorem name in our codebase
   for the qualitative descent (we already have all of these as
   deterministic-existence theorems).

2. **Lifting deterministic descent → expected descent under uniform
   scheduling**: the bridging lemma.  Given a potential `φ : Config → ℕ`
   that strictly decreases under *some* scheduler from each non-zero
   configuration, give the precise Lean statement of the expected
   sequential time bound under uniform scheduling.  This is the
   "geometric drift" pattern from population-protocol analysis.

3. **Phase composition**: how to bound `E[T_A + T_B + T_C + reset]`
   given individual phase bounds and the fact that phases are not
   independent (Phase B's behavior depends on Phase A's output, etc.).
   Linearity of expectation applies; provide the precise Lean
   composition lemma signature.

4. **Anticipated Mathlib gaps**: same as Prompt 2.

Deliver as markdown.  Tie every phase to the existing Lean theorem
that proves its qualitative version.
```

---

## Dispatch order

1. Send Prompt 1 first; review the output before proceeding.
2. Send Prompts 2 and 3 in parallel after Prompt 1 lands.

After all three outputs are in, codex starts on sub-tasks A1/A2/A3
(`HANDOFF/inbox/2026-05-18-zinan-019-time-bound-kickoff.md`); Zinan
starts on sub-tasks B1/C1 from the strategy memos.
