# Time-Bound Formalization Plan

This document is the design plan for closing the **time-optimal** half of
Kanaya–Eguchi–Sasada–Ooshita–Inoue (2025), which the rest of the project
has not yet touched.  It is intended to be sufficient for codex + ChatGPT
to begin sub-task work in parallel.

The qualitative half is done (`P_EM_solves_SSEM_final`, unconditional, axioms
`[propext, Classical.choice, Quot.sound]`).  This plan covers what is
needed for the paper's full claim.

## Scope

| Item | Paper | File | Status |
|------|-------|------|--------|
| Random scheduler / parallel-time model | §2 (model section) | `SSExactMajority/Probability/RandomScheduler.lean` | scaffold |
| Expected hitting time on configurations | §2 | `SSExactMajority/Probability/ExpectedTime.lean` | scaffold |
| Theorem 3 — Ω(n) expected / Ω(n log n) whp lower bound | §5.1 | `SSExactMajority/LowerBound/Time.lean` | scaffold |
| §5.2 quantitative — O(n) expected / O(n log n) whp upper bound for P_EM, with constant/externally bounded timer hypothesis | §5.2 | `SSExactMajority/UpperBound/Time.lean` | scaffold |

Detailed subplans:

- `docs/TIME_BOUND_PLAN_A.md` — PMF probability foundation.
- `docs/TIME_BOUND_PLAN_B.md` — lower-bound route and whp blocker.
- `docs/TIME_BOUND_PLAN_C.md` — upper-bound constant-success-window route.

These four scaffold files live **outside the root import graph** for now
(the root `SSExactMajority.lean` does not import them) so the main library
remains `sorry`-free.  They will be wired into the root only when each
theorem closes.  Build them with explicit `lake build` targets, e.g.

```bash
lake build SSExactMajority.LowerBound.Time SSExactMajority.UpperBound.Time
```

## Design decisions

### Decision 1 — probability foundation

Two viable choices in Mathlib:

(A) **`PMF` over the pair-stream**: each step is a draw from
`PMF.uniformOfFinset` on ordered pairs; the trajectory is a sequence of
independent draws.  Use `PMF.bind` for chain composition.  Expected
hitting time computed as a `tsum` over time-indexed bind outputs.

(B) **`MeasureTheory.Probability` + `Kernel`**: model the protocol as a
discrete-time Markov chain `ProbabilityTheory.kernel` on `Config`, then
use the existing `MeasureTheory.IsStoppingTime` infrastructure.

**Recommendation (default): (A)**.  `PMF` is finite-dimensional at each
step (the state space `Config Q Opinion n` is finite for finite `Q`), and
the expected-time `tsum` form interoperates naturally with the existing
`execution` definition.  (B) is more general but pulls in much more
Mathlib machinery for limited gain in this finite setting.

ChatGPT collaboration: ask for a comparison of the two paths *with
explicit Mathlib API references* before committing.  See
`HANDOFF/chatgpt/01-probability-foundation.md`.

### Decision 2 — "parallel time" definition

Kanaya §2: a *parallel round* is `n` consecutive sequential pair-pick
steps.  Parallel time = sequential time ÷ `n`.

Lean form:
```lean
def parallelTime (T : ENNReal) (n : ℕ) : ENNReal := T / n
```
where `T` is the expected sequential hitting time.  This is the form used
by all subsequent statements.

### Decision 3 — uniform pair sampling

Standard population-protocol model: uniform over the `n(n-1)` ordered
pairs `(i, j)` with `i ≠ j`.  Self-pairs `(i, i)` are excluded.

For `n ≥ 2`, define
```lean
noncomputable def uniformPair (n : ℕ) (hn : 2 ≤ n) : PMF (Fin n × Fin n) :=
  PMF.uniformOfFinset
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2))
    (by ... : (Finset.univ.filter ...).Nonempty)
```

### Decision 4 — what "expected time to consensus" measures

Two reasonable choices:

(α) **Expected first-hitting time of `IsConsensusConfig`** — the
deterministic existential convergence already established.

(β) **Expected first-hitting time of `Config.isOutputStable ∧
ExactMajoritySafe'`** — what `SolvesSSEM` actually requires.

These coincide for P_EM (consensus implies output-stable correct), but
(α) is cleaner to reason about.  Use (α) for the canonical definition,
and provide a `theorem hittingTime_isOutputStable_le_hittingTime_consensus`
that bridges to (β).

## Theorem statements (target shape)

### Theorem 3 — Ω(n) expected parallel time lower bound

```lean
theorem time_lower_bound_omega_n_expected
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {P : Protocol Q Opinion Output} {n : ℕ} (hn : 2 ≤ n)
    (hSolves : SolvesSSEM P n)
    (hRandom : RandomStabilizesSSEM P n hn)
    (hSilent : SilentProtocol P n) :
    ∃ C₀ : Config Q Opinion n, ∃ c : ℝ, 0 < c ∧
      ENNReal.ofReal (c * n) ≤
        parallelTime (expectedHittingTime P hn C₀ (fun C => C.isOutputStable P)) n
```
where `c` is a (computable) constant from the proof.  An equivalent
formulation using `Asymptotics.IsBigO` may be preferable for downstream
reuse; see `docs/TIME_BOUND_PLAN.md` "Statement style" below.

The high-probability half of Theorem 3 is a separate target once the
project has a tail-probability API:

```lean
-- target shape, not yet implemented
theorem time_lower_bound_omega_n_log_n_whp : ...
```

### §5.2 quantitative — O(n) expected upper bound for P_EM

```lean
theorem PEM_expected_parallel_time_linear_param
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hTimerConst :
      ∃ K₀ : ℕ, ∀ (C : Config (AgentState n) Opinion n) (μ : Fin n),
        InSswap C →
        (C μ).1.rank.val + 1 = ceilHalf n →
        (C μ).1.timer ≤ K₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C₀ : Config (AgentState n) Opinion n,
        expectedParallelTimeToConsensus
          (PEMProtocol n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C₀ ≤
          ENNReal.ofReal (C * n)
```

`C` is a (computable, hard-coded) constant.  Kanaya §5.2 has explicit
bounds; we should match those for the constant/externally bounded timer
regime.

Important formalization check: the literal current Lean instantiation

```lean
protocolPEM n n n (rankDeltaOSSR n Emax Dmax hn)
```

has median timer range `7 * (n + 4)`.  Kanaya Lemma 10's direct timer-drain
estimate costs `x * (n - 1) / 2` sequential interactions for timer value
`x`; with `x = Θ(n)`, this becomes `Θ(n^3)` sequential / `Θ(n^2)` parallel
for the drain part.  Therefore the direct §5.2 proof gives only a weaker
literal theorem unless we add a new protocol-specific lemma showing that the
`trank = n` timer does not need to drain linearly in `n`.  See
`docs/TIME_BOUND_PLAN_C.md`.

## Proof strategy outline

### Theorem 3 — lower bound

Kanaya §5.1 does not prove an Ω(n log n) expected lower bound. The paper
proves Ω(n) in expectation and Ω(n log n) with high probability:

1. Lemma 4: in a silent configuration with `|Va| ≤ |Vb|`, A-input agents
   have pairwise distinct states.
2. Modify one B-input agent to carry one of those A-states. The modified
   configuration has majority A but still outputs B, hence is not safe.
3. Silence means the modified configuration cannot change toward safety
   until one particular pair of agents interacts.
4. That unordered pair is sampled with probability `2 / (n * (n - 1))`
   per sequential interaction. The expected wait is Ω(n²), giving Ω(n)
   expected parallel time after division by `n`.
5. The geometric tail needs a repair/clarification before it can be
   formalized as a standard whp lower bound.  The paper's displayed
   one-pair calculation gives probability `n^{-α}` for waiting
   `Θ(n² log n)` sequential interactions, not probability `1 - O(1/n)`.
   The expected lower bound is therefore the first Lean target; the whp
   statement should wait for an amplification argument or a clarified
   interpretation of the paper's claim.

### §5.2 quantitative — upper bound

Kanaya §5.2 explicit analysis:

- Phase A (ranking, Burman): O(n) expected parallel time.
- Phase B (swap): O(n) parallel time (each misorder pair fires within
  expected O(n) sequential steps via uniform sampling).
- Phase C / timer / propagation: O(n) expected parallel time with a
  constant success probability per O(n)-time window only under a
  constant/externally bounded median-timer hypothesis.  For literal
  `protocolPEM n n n ...`, the direct timer-drain argument is O(n²)
  parallel.

Total: O(n) expected parallel time. Repeating O(log n) windows gives
O(n log n) parallel time with high probability in the bounded-timer
regime.

The Lean proof composes these phase bounds via `parallelTime` linearity:
`E[T_A + T_B + T_C + …] = E[T_A] + E[T_B] + …` (standard).

## Sub-task breakdown for codex + ChatGPT collab

### Sub-task A — Probability foundation (ChatGPT design + codex implementation)

1. **ChatGPT** (design):
   - Compare PMF vs Kernel for this problem.  Output a decision memo
     `docs/TIME_BOUND_PLAN_A.md` with API references.
   - Draft signatures for `uniformPair`, `stepKernel`, `transitionMatrix`,
     `nthStepDistribution`, `hittingTime`, `expectedHittingTime`,
     `parallelTime`.
2. **codex** (implementation):
   - `Probability/RandomScheduler.lean` — fill the `def`s.
   - `Probability/ExpectedTime.lean` — fill the `def`s.
   - Verify all `def`s elaborate (no `sorry`).

### Sub-task B — Theorem 3 lower bound (Zinan + codex)

1. **Zinan** (Lean / strategy):
   - State `time_lower_bound_omega_n_expected` in
     `LowerBound/Time.lean`.
   - State the probabilistic `RandomStabilizesSSEM` hypothesis; the old
     qualitative `SolvesSSEM` alone is only existential over deterministic
     schedulers and is not enough for expected-time claims.
   - Write the high-level proof skeleton (assumes the geometric
     waiting-time lemma) as target propositions first; theorem proofs are
     added only when the stochastic lemmas are available.
2. **codex** (Mathlib lookup):
   - Find / state / prove the abstract geometric waiting-time lemma using
     existing Mathlib infrastructure. If not present, design a
     standalone proof.
   - Track the whp lower-bound issue in `docs/TIME_BOUND_PLAN_B.md`: the
     one-pair geometric tail in the paper does not by itself give a
     `1 - O(1/n)` lower-bound event.
3. **Zinan** (gluing):
   - Compose Lemma 4's distinct-state argument + geometric waiting time →
     a theorem proving `time_lower_bound_omega_n_expected`.

### Sub-task C — §5.2 quantitative upper bound (Zinan + ChatGPT)

1. **ChatGPT** (strategy):
   - Translate Kanaya §5.2 phase-by-phase analysis into Lean theorem
     statements.  Output `docs/TIME_BOUND_PLAN_C.md` with explicit phase
     decomposition: ranking + swap + decision + reset.
2. **Zinan** (Lean):
   - State `PEM_expected_parallel_time_linear_param`.
   - Keep the literal `ConcretePEM` theorem separate until the `trank = n`
     timer issue is resolved or weakened to O(n²) parallel.
   - Phase decomposition lemmas (one per phase).
3. **Both** (proof):
   - Each phase lemma proven using `parallelTime` linearity + the
     specific phase potential decrease (e.g., misorder count for swap).

## Statement style

`Asymptotics.IsBigO` is the canonical Mathlib idiom for asymptotic bounds.
But the paper's bounds are *quantitative* — explicit constants and
finite-`n` validity.  Use **explicit closed-form** statements (as above)
for the theorems themselves; an `IsBigO`-style corollary can be added
once the explicit bound lands.

## File ownership

| File | Initial owner | Reviewer |
|------|---------------|----------|
| `Probability/RandomScheduler.lean` | codex | Zinan |
| `Probability/ExpectedTime.lean` | codex | Zinan |
| `LowerBound/Time.lean` | Zinan | codex |
| `UpperBound/Time.lean` | Zinan | codex (Mathlib API), ChatGPT (strategy) |
| `docs/TIME_BOUND_PLAN.md` | Zinan | — |
| `docs/TIME_BOUND_PLAN_A.md` | ChatGPT | Zinan |
| `docs/TIME_BOUND_PLAN_C.md` | ChatGPT | Zinan |

## Done criteria

The current scaffold-cleaning stage is "done" when:

- `rg -n "^\s*sorry\s*$" SSExactMajority --glob '!**/.lake/**'` returns
  no matches.
- The time-bound targets build on uisai1:
  `SSExactMajority.Probability.RandomScheduler`,
  `SSExactMajority.Probability.ExpectedTime`,
  `SSExactMajority.LowerBound.Time`,
  `SSExactMajority.UpperBound.Time`.

The full time-optimal half is "done" only later, when:

- theorem proofs of `time_lower_bound_omega_n_expected` and
  `PEM_expected_parallel_time_linear_param` compile, no `sorry`,
  axioms only `[propext, Classical.choice, Quot.sound]`.
- Both files imported into the root `SSExactMajority.lean`.
- `AxiomCheck.lean` extended with `#print axioms` for both.
- README + CHECKPOINT updated.
