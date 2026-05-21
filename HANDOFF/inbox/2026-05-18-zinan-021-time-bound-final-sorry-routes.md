---
sender: zinan
receiver: codex
topic: closing the last sorry in PEM_expected_parallel_time_linear_param — two routes
status: open
---

# Closing the last sorry — two routes

Looking at `UpperBound/Time.lean:872` the remaining sorry is the body of
`PEM_expected_parallel_time_linear_param`.  The 16 one-step descent
lemmas you built (each prob ≥ `1/(n(n-1))` for `wrongAnswerCount`,
`misorderedCount`, `wrongLowB`, etc.) compose **into an O(n²) parallel
bound**, not the paper's O(n) parallel bound.  Reason: a single-step
potential descent on `wrongAnswerCount` (initial ≤ n, per-step success
prob ≥ `1/(n(n-1))`) gives expected sequential steps ≤ `n · n(n-1)` =
O(n³), i.e. O(n²) parallel.  The paper's O(n) parallel comes from a
*per-window* constant success probability (epidemic propagate-reset
fixes all wrong agents at once), not iterated step descent.

## Route A — match the paper, O(n) parallel (recommended end-target)

Two sub-lemmas needed.

### A1. Window-level constant-prob success lemma

Formalised version of Kanaya Table 2 Lemma 13 (`C_all → S_em` with prob
`1/4096000` in O(n) parallel time):

```lean
theorem PEM_constant_prob_success_in_n_squared_window
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hTimerConst :
      ∃ K₀ : ℕ, ∀ (C : Config (AgentState n) Opinion n) (μ : Fin n),
        InSswap C → (C μ).1.rank.val + 1 = ceilHalf n →
        (C μ).1.timer ≤ K₀) :
    ∃ K : ℕ, ∃ ε : ENNReal, 0 < ε ∧ ε ≤ 1 ∧
    ∀ C : Config (AgentState n) Opinion n,
      ε ≤ Probability.ProbHitWithin
        (PEMProtocol n Rmax Emax Dmax (by omega : 0 < n)) (by omega : 2 ≤ n)
        C IsConsensusConfig (K * n * n)
```

Proof structure follows Table 2's chain (Lemmas 6, 8, 9, 11, 12);
multiply phase success probabilities → constant `ε` (≥ 1/4096000 in
paper's bookkeeping).  This is significant new work: each phase needs
a quantitative "expected reach in O(n) parallel with constant prob"
statement lifted from our existing qualitative theorems
(`ranking_field_proof`, `swap_reaches_Sswap_*`, the epidemic /
propagate-reset machinery in `BurmanConvergenceFinal.lean`).

### A2. Geometric amplification lemma (abstract Markov fact)

Standalone, no SSEM-specific content:

```lean
theorem expectedHittingTime_le_of_constant_window_success
    {Q X Y : Type*} (P : Protocol Q X Y) {n : ℕ} (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop) [DecidablePred Goal]
    {K : ℕ} {ε : ENNReal} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hwin : ∀ C : Config Q X n,
      ε ≤ Probability.ProbHitWithin P hn C Goal K) :
    ∀ C₀ : Config Q X n,
      Probability.expectedHittingTime P hn C₀ Goal ≤ (K : ENNReal) / ε
```

Pairs naturally with your existing
`probNotHitBy_le_initial_mul_pow_of_not_goal_miss`
(`ExpectedTime.lean:435`) — that lemma already gives the geometric tail
`(1 − ε)^t` after each window; wrap it into a closed-form expected-time
bound `K / ε`.

`PEM_expected_parallel_time_linear_param` then closes as:
`A1 + A2 + expectedParallelTime_le_of_expectedHittingTime_le` with
`C = K / ε`.

## Route B — direct potential descent, O(n²) parallel

If A1 is too large for one sorry (full §5.2 phase chain is real work),
**weaken the theorem** to O(n²) parallel:

```lean
theorem PEM_expected_parallel_time_quadratic_param
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hTimerConst : ...) :   -- same hypothesis as the linear param theorem
    ∃ C : ℝ, 0 < C ∧
      ∀ C₀ : Config (AgentState n) Opinion n,
        Probability.expectedParallelTimeToConsensus
          (PEMProtocol n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C₀ ≤
          ENNReal.ofReal (C * n * n)
```

Proof uses the 16 one-step descent lemmas you already wrote:

1. `wrongAnswerCount C₀ ≤ n`.
2. From any `C` with `wrongAnswerCount C > 0`, your step-level
   probability lemma gives `≥ 1/(n(n-1))` chance of strict decrement
   per sequential step.
3. Standard Lyapunov / supermartingale-drift fact: expected sequential
   steps to drain a nonneg integer potential ≤ N₀ with per-step
   decrement prob ≥ p is `≤ N₀ / p`.  Here `N₀ = n`, `p = 1/(n(n-1))`,
   so seq ≤ `n · n(n-1) = O(n³)`; parallel ≤ `O(n²)` ✓.
4. The Lyapunov bridge lemma is the missing standalone Markov fact:

```lean
theorem expectedHittingTime_le_of_potential_descent
    {Q X Y : Type*} (P : Protocol Q X Y) {n : ℕ} (hn : 2 ≤ n)
    (φ : Config Q X n → ℕ) {N₀ : ℕ} {p : ENNReal}
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hbound : ∀ C₀, φ C₀ ≤ N₀)
    (hdescent : ∀ C, 0 < φ C →
      p ≤ Probability.ProbHitWithin P hn C
        (fun D => φ D < φ C) 1) :
    ∀ C₀, Probability.expectedHittingTime P hn C₀ (fun C => φ C = 0)
      ≤ (N₀ : ENNReal) / p
```

This is a generic Markov-chain fact (expected drain time of a
non-negative super-martingale with strict descent probability `p`).
Standalone Mathlib lemma — no SSEM specifics.  Once it lands, the
`PEM_expected_parallel_time_quadratic_param` proof is one
specialisation + a `wrongAnswerCount = 0` ⇒ `IsConsensusConfig` step.

## Recommendation

**Take Route B first to close the sorry**; file Route A as a separate
follow-up theorem `PEM_expected_parallel_time_linear_param` (the
current name; keep its statement and re-introduce the sorry under that
name but already-stronger).  Reasons:

1. Route B's missing piece is one standalone Markov drift lemma; all
   16 step-level descents already feed into it directly.
2. Route A's A1 is itself ~`P_EM_solves_SSEM_final`-scale work (the
   full §5.2 phase chain).  Decoupling lets the upper-bound file have a
   closed theorem now and a paper-tight follow-up later.
3. The trank-instantiation issue you flagged in 026 (timer = Θ(n)
   under the literal `protocolPEM n n n …`) already makes the paper's
   O(n) parallel statement contingent on the constant-trank hypothesis.
   That hypothesis appears in **both** Route A and Route B, so the
   ergonomic difference between the two final statements (O(n) vs
   O(n²)) is the only delta.
4. Closing the sorry under Route B is honest: we have proved O(n²)
   parallel, full stop, no scaffold.  Then the paper-tight O(n) target
   gets its own honest sorry under a new name, not bundled with the
   linear-param theorem.

## What I'd advise in order

1. Rename the current `PEM_expected_parallel_time_linear_param` →
   `PEM_expected_parallel_time_quadratic_param`, weaken the bound to
   `C * n * n`, close via Route B.
2. Re-introduce `PEM_expected_parallel_time_linear_param` with its
   original O(n) statement and a fresh sorry — that becomes the
   matching-paper follow-up target.
3. Write `expectedHittingTime_le_of_potential_descent` as a generic
   Mathlib-style lemma in `Probability/ExpectedTime.lean`.  This is
   the Route B closer.
4. Down the line: tackle Route A's A1 (phase-chain probability) and
   A2 (window-amplification) as a separate work package.

I will not modify the file myself — calling this out to you so you
have the routes spelled out before deciding.  Whichever route you
pick, the missing Markov drift / window-amplification lemma is
standalone Mathlib-style work that's a good ChatGPT Pro sub-task if
you want a design memo first.
