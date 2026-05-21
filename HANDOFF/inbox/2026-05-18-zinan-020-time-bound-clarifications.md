---
sender: zinan
receiver: codex
topic: time-bound — three concrete clarifications after re-reading the paper
status: open
---

# Three concrete clarifications

I read all 14 pages of `papers/kanaya2025.pdf` (§5.1 and §5.2 carefully).
Three things to feed back on the BC plan.

## 1. The whp lower bound IS provable — contrapositive form

You flagged in `docs/TIME_BOUND_PLAN_B.md` that the paper's geometric
tail gives `n^{-α}` for the long-wait event, not `1 - O(1/n)`, and
called this a formalization blocker.

The paper's calculation does support a matching whp lower bound, but
only in the **contrapositive** form.  Two distinct formulations:

- **Direct form** (what your blocker flag assumes "whp lower bound"
  means): `∀ protocol P, P[time ≥ Ω(n log n)] ≥ 1 - O(1/n)`.  Not
  proved by the paper.
- **Contrapositive form** (what the paper actually proves): no
  protocol `P` has `P[time ≤ T] ≥ 1 - O(1/n)` for any
  `T = o(n log n)`.  Equivalently: if a protocol stabilizes in `T`
  parallel time whp, then `T = Ω(n log n)`.

The math:

- Paper: `P[u-w not interacted by T_α = α n(n-1)/2 log n - 1] > n^{-α}`.
- With `α = 1`: `P[wait > T_1] > 1/n`.
- Now suppose for contradiction a protocol stabilizes by `T_1` whp,
  i.e., `P[time ≤ T_1] ≥ 1 - O(1/n)`, equivalently
  `P[time > T_1] ≤ O(1/n)`.
- But silence + Lemma 4 + the constructed unsafe `C'` give
  `P[time > T_1] ≥ P[u-w not interacted by T_1] > 1/n`, contradicting
  `≤ O(1/n)` for large `n`.
- Therefore no protocol stabilizes by `T_1 = Ω(n² log n)` sequential
  whp.  Divided by `n`: no protocol stabilizes by `Ω(n log n)`
  parallel whp.

This *is* a "matching whp lower bound" in the randomized-algorithms
sense (it negates the matching whp upper bound).  The paper's English
phrasing ("Ω(n log n) with probability 1 − O(1/n)") is sloppy, but the
math is right.

**Suggested formulation in Lean**:

```lean
/-- No silent SSEM protocol stabilizes in o(n log n) parallel time
with high probability.  This is the matching contrapositive form of
the whp lower bound proved in Kanaya §5.1. -/
theorem no_silent_protocol_stabilizes_o_n_log_n_whp
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {P : Protocol Q Opinion Output} {n : ℕ} (hn : 5 ≤ n) (hodd : n % 2 = 1)
    (hSolves : SolvesSSEM P n)
    (hSilent : SilentProtocol P n) :
    ∀ T : ℕ, T < (n - 1) / 2 * Nat.log n →
      ∃ C₀ : Config Q Opinion n,
        (Probability.probHitBy P (by omega) C₀
          (fun C => C.isOutputStable P) T : ENNReal) < 1 - 1 / n
```

Constants tweakable.  Drop the `time_lower_bound_omega_n_log_n_whp`
target as currently stated; replace with the contrapositive.  The
expected form (`time_lower_bound_omega_n_expected`) you already have
stays as is.

## 2. Timer-parameter issue: confirmed

I checked `SSExactMajority/Protocol/Transition.lean:278`.  Signature is

```lean
def protocolPEM (n : ℕ) (trank Rmax : ℕ) (rankDelta : ...) : Protocol _ _ _
```

In `transitionPEM_prePhase4` (line 32–47), `trank` flows into
`timer := 7 * (trank + 4)` directly.

Our ultimate theorem `P_EM_solves_SSEM_final` instantiates as
`protocolPEM n n n (rankDeltaOSSR n Emax Dmax hn)` — the second `n` is
`trank`, so timer init = `7 * (n + 4) = Θ(n)`, **not** the `O(1)`
the paper requires.

This is fine for the qualitative theorem (existence of converging
schedule) but breaks the §5.2 quantitative analysis (which needs
`trank · n²` total interactions to dominate the timer drain).

Your fix in 026 — "state the upper-bound scaffold with an explicit
constant/externally bounded timer hypothesis" — is the right call.
The right concrete instantiation:

```lean
-- For the §5.2 upper bound: trank is a fixed constant ≥ s_rank / n.
-- Burman 2021 §3 gives s_rank = O(n), so trank = ⌈s_rank / n⌉ = O(1).
-- For the Lean target, pin trank to any explicit constant ≥ that ceiling.

theorem P_EM_expected_parallel_time_linear
    {n : ℕ} [Inhabited (Fin n × Fin n)] (hn : 2 ≤ n)
    {Emax Dmax : ℕ} (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    {trank : ℕ} (htrank : trankBoundConst ≤ trank)   -- constant, not n
    (htrank_bound : trank ≤ trankBoundConst + 1) :   -- bounded above too
    ∃ C : ℝ, 0 < C ∧
      ∀ C₀ : Config (AgentState n) Opinion n,
        (Probability.expectedParallelTimeToSilent
          (protocolPEM n trank n (rankDeltaOSSR n Emax Dmax (by omega : 0 < n)))
          hn C₀).toReal ≤ C * n
```

where `trankBoundConst` is a hard-coded `ℕ` derived from the Burman
constant.  Burman 2021 Theorem 4.3 (their Lemma 3) gives the constant.

A follow-up project: prove `s_rank_le_const_mul_n` to obtain a
specific `trankBoundConst` value.  Until then, leave it as a `ℕ`
parameter with the explicit hypothesis.

## 3. Lemma 4 already exists in our codebase

In `docs/TIME_BOUND_PLAN_B.md` "Open Gaps" you wrote:

> Need a Lean version of Lemma 4 as a reusable theorem, not only the
> final `SSEM.space_lower_bound`.

It's already there.  `SSExactMajority/LowerBound/Space.lean:38`:

```lean
theorem silent_config_A_agents_distinct
    {n : ℕ} (P : Protocol Q Opinion Output)
    (C : Config Q Opinion n)
    (hSilent : C.isSilent P)
    (hSafe : ExactMajoritySafe' P C ...)
    (hSolves : SolvesSSEM P n)
    (hVa : (C.agentsWithInput .A).card ≤ (C.agentsWithInput .B).card)
    (hn : n ≥ 2)
    (u v : Fin n)
    (huA : C.inputOf u = .A) (hvA : C.inputOf v = .A)
    (hne : u ≠ v) :
    C.stateOf u ≠ C.stateOf v
```

This is the exact form your modified-`C'` construction needs.  No
new lemma required; thread this directly into the lower-bound proof.

## §5.2 upper-bound roadmap (Table 2 of the paper)

For the BC C-side of your work, the paper's Table 2 gives the full
roadmap:

| Step | Time | Success prob | Lemma |
|------|------|-------------:|-------|
| `C_all → S_rank` | O(n) | 1/10 | Lemma 6 |
| `S_rank → T_swap ∪ S_tim` | O(n) | 1/20 | Lemma 8 |
| `T_swap → S_dec` | O(n) | 1/8 | Lemma 9 |
| `S_dec → S_tim` | O(n) | 1/1280 | Lemma 11 |
| `S_tim → S_em` | O(n) | 1/2 | Lemma 12 |
| `C_all → S_em` | O(n) | 1/4096000 | Lemma 13 |

The chain: each O(n) window has constant success prob ≥ 1/4096000.
Repeat → expected `4096000 · O(n) = O(n)` window time; geometric
amplification over `log n` windows gives `1 - (1 - 1/4096000)^{log n}
= 1 - 1/n^c` for some c > 0.

Phase-by-phase decomposition is well-aligned with our existing
qualitative theorems:

- Lemma 6 (`C_all → S_rank`): our `ranking_field_proof`.
- Lemma 8 (`S_rank → T_swap`): our `swap_reaches_Sswap_*`.
- Lemma 9 (`T_swap → S_dec`): existing decision-phase machinery.
- Lemmas 10/11/12/13: timer/epidemic/silent re-entry in
  `BurmanConvergenceFinal.lean`.

So the qualitative pieces all exist; the upper-bound work is
specifically lifting "exists schedule reaching X in finitely many
steps" → "expected sequential time ≤ c · n under uniform random".

The bridging lemma you sketched in `docs/TIME_BOUND_PLAN_C.md`
("lifting deterministic descent → expected descent") is the key
abstraction.  Keep going.

## Blockers — none new

Both flagged "blockers" in 026 have resolutions:

- whp lower bound: use the contrapositive formulation (§1 above).
- timer parameter: keep `trank` constant in the upper-bound theorem
  (§2 above).

Lemma 4 is already done (§3).  Onward.
