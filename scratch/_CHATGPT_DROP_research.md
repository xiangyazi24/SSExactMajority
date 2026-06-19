# Research note: RC drain and phase potentials for Kanaya et al. exact-majority formalization

Context: Lean 4 v4.30 + Mathlib, formalizing Kanaya–Eguchi–Sasada–Ooshita–Inoue 2025, *Time- and Space-Optimal Silent Self-Stabilizing Exact Majority in Population Protocols*.

Target theorem, in interaction steps:

```lean
-- informal target
from all-Resetting agents with correct answers + bounded state,
E[ hitting_time IsConsensusConfig ] ≤ 3 * Rmax * n^2
```

The paper’s global convention is a complete graph uniform scheduler; one ordered pair interacts per step, and “parallel time” is interactions divided by `n`. Thus an `O(n)` parallel-time statement corresponds to `O(n^2)` interactions. The target above is an interaction-count bound, and it is much coarser than the paper’s asymptotic statement when `Rmax = Θ(log n)`.

## Executive summary

1. The theorem

```lean
expectedHittingTime_le_of_multiplicative_drift
```

that returns roughly

```lean
Φ0 * (1-q)⁻¹
```

is the wrong tool for the reset-count potential `Φ = Σ 3^rc`. Since `Φ0 ≤ n * 3^Rmax`, this gives an exponential-in-`Rmax` bound.

2. The paper’s polynomial reset-count drain bound comes from the **logarithmic** form of multiplicative drift, equivalently:

```text
multiplicative drift → E[Φ_t] decays exponentially
→ Markov gives P(hit within K) ≥ 1/2 for K = O(n log Φ0)
→ geometric window lemma gives E[T] ≤ 2K.
```

So yes: your proposed “multiplicative drift + Markov + window_mul_inv” repair is correct. It is equivalent to the standard multiplicative-drift theorem `E[T] ≤ O((log Φ0)/(1-q))`.

3. For phases 2–5, do not use a raw counter with a single-good-pair lower bound unless you can tolerate `O(n^3)`. Use **rate-weighted additive potentials**: potential drop size is the reciprocal of the current success probability lower bound. This gives `O(n^2)` interaction bounds for ranking, swap, decision, and epidemic-style consensus.

4. For the theorem `≤ 3 * Rmax * n^2`, a safe Lean plan is:

```text
RC drain         ≤ 2 * Rmax * n^2
post-RC phases   ≤ 1 * Rmax * n^2
---------------------------------
total            ≤ 3 * Rmax * n^2
```

assuming `n ≥ 2` and `Rmax ≥ 1` or a small constant lower bound such as `Rmax ≥ 4` depending on how many post-RC subphase contracts you allocate separately.

## 1. Reset-count drain: why additive drift on `Φ` is too weak

The reset-count potential is

```text
Φ(C) = Σ agents v, 3^(resetcount(v)).
```

The paper-style one-step estimate is

```text
E[Φ(C_{t+1}) | C_t = C] ≤ (1 - 2/(3n)) * Φ(C)
```

as long as some reset count is still positive / some Resetting drain remains.

Let

```text
q = 1 - 2/(3n).
```

Your current theorem gives approximately

```text
E[T] ≤ Φ0 / (1-q) = Φ0 * (3n/2).
```

But if initially all agents may have reset count at most `Rmax`, then

```text
Φ0 ≤ n * 3^Rmax.
```

So this bound is exponential in `Rmax`:

```text
E[T] ≤ (3/2) * n^2 * 3^Rmax.
```

This is mathematically valid but useless for the intended theorem.

## 2. Correct RC-drain argument: multiplicative drift as a half-window

Iterating the multiplicative drift gives

```text
E[Φ_t] ≤ q^t * Φ0.
```

Before the RC drain has finished, `Φ_t ≥ 1` because some positive reset count remains. Hence by Markov:

```text
P(T_RC > t) = P(Φ_t ≥ 1) ≤ E[Φ_t] ≤ q^t * Φ0.
```

Choose `K` such that

```text
q^K * Φ0 ≤ 1/2.
```

Then

```text
P(T_RC ≤ K) ≥ 1/2.
```

A geometric-window/restart lemma gives

```text
E[T_RC] ≤ K / (1/2) = 2K.
```

This is exactly the “Markov then window_mul_inv” route. It avoids conditional-probability infrastructure if stated as a Markov-chain kernel/window theorem.

### Tight scale

Because

```text
-log q ≥ 1-q = 2/(3n)
```

or more directly `(1 - 2/(3n))^K ≤ exp(-2K/(3n))`, a sufficient window is

```text
K ≥ (3n/2) * log(2Φ0).
```

Using

```text
Φ0 ≤ n * 3^Rmax,
```

this gives

```text
K = O(n * (log n + Rmax)).
```

When `Rmax = 60 log n`, this is `O(n Rmax)` interactions, i.e. `O(Rmax)` parallel time.

### Coarse Lean-friendly window

For your target, use the much coarser window

```text
K_RC = Rmax * n^2.
```

It is enough to prove

```text
q^(Rmax*n^2) * n * 3^Rmax ≤ 1/2.
```

This is weaker than the sharp estimate but often much easier to use in a downstream theorem.

A clean approach is to prove a reusable inequality such as

```lean
lemma rc_window_decay
    (hn : 2 ≤ n) (hR : 1 ≤ Rmax) :
    (1 - (2 : ℝ) / (3*n)) ^ (Rmax * n^2) * (n * 3^Rmax : ℝ) ≤ 1 / 2 := ...
```

If this is arithmetically annoying, use an intermediate bound with `Real.exp`:

```text
(1 - 2/(3n))^(Rmax*n^2)
  ≤ exp(-(2/(3n)) * Rmax*n^2)
  = exp(-(2/3) Rmax*n).
```

Then show this dominates `n * 3^Rmax`. Since the final theorem is coarse, assuming `n ≥ 3`, `Rmax ≥ 1`, or the paper’s actual `Rmax = 60 log n` will make the inequality straightforward.

## 3. Lean theorem shapes for RC drain

Avoid proving only the additive-drift consequence. Add one of these two theorems.

### Version A: half-window theorem

```lean
theorem hitProb_ge_half_of_multiplicative_drift
    {Config : Type*}
    (step : Config → ProbabilityMass Config)
    (target : Config → Prop)
    (Φ : Config → ℝ)
    (q : ℝ) (K : ℕ)
    (C0 : Config)
    (hΦ_nonneg : ∀ C, 0 ≤ Φ C)
    (h_not_target_ge_one : ∀ C, ¬ target C → 1 ≤ Φ C)
    (h_drift : ∀ C, ¬ target C →
      expectedNext step Φ C ≤ q * Φ C)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hwindow : q^K * Φ C0 ≤ 1/2) :
    hitProbWithin step target C0 K ≥ 1/2 := ...
```

Then:

```lean
theorem expected_hitting_time_le_of_half_window
    (K : ℕ)
    (hwin : ∀ C, StartRegion C → hitProbWithin step target C K ≥ 1/2) :
    expectedHittingTime step target C0 ≤ 2*K := ...
```

The second theorem is the usual geometric-window lemma. It can be proved by bounding the tail:

```text
P(T > mK) ≤ (1/2)^m,
E[T] = Σ_t P(T > t) ≤ K * Σ_m (1/2)^m = 2K.
```

### Version B: logarithmic multiplicative drift

Alternatively prove directly:

```lean
theorem expected_hitting_time_le_of_log_multiplicative_drift
    (Φ : Config → ℝ)
    (Φ0_bound : Φ C0 ≤ Φmax)
    (hΦ_nonneg : ∀ C, 0 ≤ Φ C)
    (h_not_target_ge_one : ∀ C, ¬ target C → 1 ≤ Φ C)
    (h_drift : ∀ C, ¬ target C → expectedNext step Φ C ≤ q * Φ C)
    (hq : 0 ≤ q ∧ q < 1) :
    expectedHittingTime step target C0 ≤
      someConstant * Real.log Φmax / (1 - q) := ...
```

This is sharper but introduces logs and real arithmetic. The half-window theorem is usually easier for Lean and enough for `3 * Rmax * n^2`.

## 4. Post-RC phases: use rate-weighted additive potentials

A generic deterministic-descent lemma of the following kind is useful:

```lean
theorem expected_time_le_of_potential_drift
    {Config : Type*}
    (target : Config → Prop)
    (V : Config → ℝ)
    (hV_nonneg : ∀ C, 0 ≤ V C)
    (hV_zero : ∀ C, target C → V C = 0)
    (h_drift : ∀ C, ¬ target C →
      expectedNext step V C ≤ V C - 1) :
    expectedHittingTime step target C0 ≤ V C0 := ...
```

For phases where a transition succeeds with probability at least `p(C)` and decreases a counter by one, define `V` so that the drop in `V` equals at least `1/p(C)`.

This is the standard rate-weighted potential trick.

## 5. Dormant / delaytimer / Reset phase

The exact potential depends on your encoded transition rules. A robust contract is:

```lean
structure DormantContract where
  V : Config → ℝ
  V_bound : ∀ C, AllDormantRC0 C → V C ≤ Rmax * n^2
  drift : ∀ C, AllDormantRC0 C → ¬ ResetDone C →
    expectedNext step V C ≤ V C - 1
```

A plausible concrete potential is based on total remaining delaytimer mass:

```text
D(C) = Σ agents delaytimer(v).
```

If a positive timer decreases whenever that agent participates, then when `p` agents have positive timers, the probability some positive-timer agent participates is at least

```text
2p/n   -- for ordered complete scheduler
```

and `D` decreases by at least one. A rate-weighted version can give

```text
O(n * D0) ≤ O(Rmax * n^2)
```

when `D0 ≤ Rmax * n`.

For the final theorem, this phase can be absorbed into the `Rmax * n^2` post-reset budget.

Lean contract theorem:

```lean
theorem dormant_expected_le
    (hn : 2 ≤ n)
    (hD : ∀ v, delaytimer v ≤ Rmax) :
    expectedHittingTime step ResetDone C ≤ Rmax * n^2 := ...
```

If the protocol has a stronger rule causing every interaction to reduce a global timer, use the simpler potential `maxDelay` or `sumDelay` and a direct deterministic descent.

## 6. Ranking phase potential

If the formal ranking subprotocol is treated as a black-box imported theorem from the silent self-stabilizing ranking protocol, use that contract. The paper explicitly uses such ranking-protocol results. In Lean, a black-box contract is often the cleanest first milestone.

If proving from your simplified “binary tree Settled recruits Unsettled” rules, use a rate-weighted potential.

Let

```text
s(C) = #Settled agents,
u(C) = n - s(C).
```

If any Settled–Unsettled interaction recruits one Unsettled agent, then the success probability is at least

```text
p_s = 2 * s * (n-s) / (n*(n-1)).
```

Define

```text
V_rank(s) = Σ_{i=s}^{n-1} n*(n-1) / (2*i*(n-i)).
```

When `s` increases to `s+1`, `V_rank` decreases by

```text
n*(n-1) / (2*s*(n-s)) = 1 / p_s.
```

Thus the expected drift is at least one.

Bound:

```text
V_rank(1)
= Σ_{i=1}^{n-1} n(n-1)/(2 i(n-i))
= (n-1) * H_{n-1}
≤ n^2
```

using the crude bound `H_{n-1} ≤ n`.

Lean definitions:

```lean
def rankPot (n s : ℕ) : ℚ :=
  ∑ i in Finset.Icc s (n-1),
    (n*(n-1) : ℚ) / (2 * i * (n-i))
```

Suggested lemmas:

```lean
lemma rankPot_step_drop
    (hs : 1 ≤ s) (hsn : s < n) :
    rankPot n s - rankPot n (s+1) =
      (n*(n-1) : ℚ) / (2*s*(n-s)) := ...

lemma rankPot_bound_n2
    (hn : 2 ≤ n) :
    rankPot n 1 ≤ (n^2 : ℚ) := ...

theorem ranking_expected_le_n2
    (hn : 2 ≤ n) :
    expectedHittingTime step RankingDone C ≤ n^2 := ...
```

Caveat: if the actual binary-tree recruitment rule allows only a subset of Settled agents to recruit, replace `2*s*(n-s)` by the correct lower bound. If only `frontier(C)` agents can recruit, use

```text
p = 2 * frontier(C) * unsettled(C) / (n(n-1))
```

and define the reciprocal-sum potential accordingly. If the only available lower bound is `frontier ≥ 1`, this gives `O(n^2 log n)` or worse; in that case, use the paper’s ranking theorem as a contract instead of reproving it from a naive frontier count.

## 7. Swap/sort phase potential

This phase has a clean potential.

Let

```text
q(C) = # mispositioned A-agents
     = # mispositioned B-agents.
```

A correct swap can occur between any mispositioned A and any mispositioned B. In the ordered scheduler, there are at least

```text
2*q^2
```

good ordered pairs. Hence

```text
p_q ≥ 2*q^2 / (n*(n-1)).
```

Define

```text
V_swap(q) = Σ_{i=1}^{q} n*(n-1)/(2*i^2).
```

When `q` decreases by one, `V_swap` drops by exactly the reciprocal of the lower-bound success probability. Expected drift is at least one.

Bound:

```text
Σ_{i=1}^{q} 1/i^2 ≤ 2
```

using

```text
1/i^2 ≤ 1/(i*(i-1)) for i ≥ 2,
Σ_{i=2}^{q} 1/(i*(i-1)) = 1 - 1/q ≤ 1.
```

Therefore

```text
V_swap(q) ≤ n*(n-1) ≤ n^2.
```

Lean definitions:

```lean
def swapPot (n q : ℕ) : ℚ :=
  ∑ i in Finset.Icc 1 q,
    (n*(n-1) : ℚ) / (2*i*i)
```

Suggested lemmas:

```lean
lemma swapPot_step_drop
    (hq : 1 ≤ q) :
    swapPot n q - swapPot n (q-1) =
      (n*(n-1) : ℚ) / (2*q*q) := ...

lemma sum_inv_sq_le_two (q : ℕ) :
    (∑ i in Finset.Icc 1 q, (1 : ℚ) / (i*i)) ≤ 2 := ...

lemma swapPot_bound_n2
    (hn : 2 ≤ n) :
    swapPot n q ≤ (n^2 : ℚ) := ...

theorem swap_expected_le_n2
    (hn : 2 ≤ n) :
    expectedHittingTime step SwapDone C ≤ n^2 := ...
```

This is likely the easiest post-RC phase to formalize completely.

## 8. Decision and consensus potential

There are two useful patterns.

### Direct geometric waiting

If one particular ranked/median agent must interact, or one of at least `g ≥ 1` ordered pairs triggers decision, then

```text
p ≥ 1/(n(n-1))
```

or better, and

```text
E[T_decision] ≤ n(n-1) ≤ n^2.
```

Use a one-state potential:

```text
V_decide(C) = n(n-1)
```

before the decision event, `0` after.

### Epidemic propagation

If one or more agents know the final output and it must spread, let

```text
i(C) = # informed agents.
```

Good ordered pairs are informed–uninformed pairs, so

```text
p_i ≥ 2*i*(n-i)/(n*(n-1)).
```

Use the same potential as ranking:

```text
V_epi(i) = Σ_{s=i}^{n-1} n*(n-1)/(2*s*(n-s)) ≤ n^2.
```

Lean definitions:

```lean
def epidemicPot (n i : ℕ) : ℚ :=
  ∑ s in Finset.Icc i (n-1),
    (n*(n-1) : ℚ) / (2*s*(n-s))
```

If the hypothesis already says all agents have correct answers and only silence/consensus configuration remains, the direct geometric waiting contract may suffice.

## 9. Final composition theorem

Use sequential hitting-time composition. A convenient theorem shape is:

```lean
theorem expected_hitting_time_seq_le
    (A B C : Config → Prop)
    (hAB : ∀ C0, A C0 → E[T_B from C0] ≤ TAB)
    (hBC : ∀ C1, B C1 → E[T_C from C1] ≤ TBC) :
    ∀ C0, A C0 → E[T_C from C0] ≤ TAB + TBC := ...
```

Then instantiate:

```lean
RCDrained
DormantDone / ResetDone
RankingDone
SwapDone
DecisionDone
IsConsensusConfig
```

For the advertised bound, avoid proving a tight theorem for every subphase. Package the post-RC phases into one contract:

```lean
theorem postReset_expected_le
    (hn : 2 ≤ n) (hR : 4 ≤ Rmax) :
    E[T_postReset_to_consensus] ≤ Rmax * n^2 := by
  -- combine dormant, ranking, swap, decision/consensus,
  -- each ≤ n^2 or dormant ≤ Rmax*n^2 depending on your rules.
```

Then:

```lean
theorem allResetting_to_consensus_expected_le
    (hn : 2 ≤ n) (hR : 1 ≤ Rmax)
    (hRC : E[T_RC] ≤ 2 * Rmax * n^2)
    (hPost : E[T_postReset] ≤ Rmax * n^2) :
    E[T_consensus] ≤ 3 * Rmax * n^2 := by
  nlinarith
```

If `postReset_expected_le` needs `Rmax ≥ 4` because it sums four `≤ n^2` subphases, state the final theorem with that stronger assumption or prove `Rmax ≥ 4` from the protocol definition, e.g. `Rmax = 60 * Nat.log2 n` under the paper’s parameter regime.

## 10. Minimal Lean implementation plan

Recommended order:

1. Add the half-window theorem for multiplicative drift.
2. Prove the coarse RC window inequality for `K = Rmax*n^2`.
3. Derive

```lean
rcDrain_expected_le : E[T_RC] ≤ 2 * Rmax * n^2
```

4. Add the generic rate-weighted potential theorem.
5. Formalize `swapPot` first; it has the cleanest combinatorics.
6. Either import/axiomatize as a contract the ranking theorem from the paper’s ranking subroutine, or prove the `rankPot` theorem if your rule really gives `2*s*(n-s)` good ordered pairs.
7. Add direct geometric or epidemic potential for decision/consensus.
8. Compose phases.

## 11. Direct answers to the prompt

### How does the paper get `O(n*Rmax)` for RC drain?

Yes: it is the logarithmic/multiplicative-drift use of `Φ = Σ 3^rc`, not the additive bound `Φ0/(1-q)`. One way to formalize it is exactly:

```text
multiplicative drift
→ E[Φ_K] ≤ q^K Φ0
→ Markov: P(not drained by K) ≤ q^K Φ0
→ choose K = O(n Rmax) so failure ≤ 1/2
→ repeated windows: E[T] ≤ 2K = O(n Rmax).
```

The more standard theorem is the multiplicative-drift expected-time theorem

```text
E[T] ≤ O((log Φ0)/(1-q)).
```

The window proof is simpler to connect to your existing `window_mul_inv` style lemma.

### What additive potential works for phases 2–5?

Use rate-weighted potentials:

- Dormant/reset: timer-mass or a contract potential bounded by `Rmax*n^2`.
- Ranking: `Σ_{i=s}^{n-1} n(n-1)/(2*i*(n-i))`, if any settled recruits any unsettled; otherwise use the paper’s ranking theorem as a contract.
- Swap: `Σ_{i=1}^{q} n(n-1)/(2*i^2)`, where `q` is the number of misplaced A-agents, equal to misplaced B-agents.
- Decision: direct geometric waiting potential `≤ n^2`.
- Consensus propagation: epidemic potential `Σ_{i=infected}^{n-1} n(n-1)/(2*i*(n-i))`.

These are exactly the kind of potentials that fit a Lean theorem of the form

```lean
expected_time_le_of_potential_drift
```

with one-step drift at least `1` until the target is reached.
