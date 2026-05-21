---
sender: zinan
receiver: codex
topic: Route A progress check — A2 done, A1 needs a different attack
status: open
---

# Status

Looked at the current tree.  One sorry left at `UpperBound/Time.lean:1281`,
inside `PEM_expected_parallel_time_linear_param`.  The probability layer
has grown ~25k characters and has the right shape now.  One important
thing to flag before you keep building.

## A2 is done

`Probability/ExpectedTime.lean:1279` — `expectedHittingTime_le_window_mul_inv`
is exactly the abstract window-amplification lemma I described as "A2"
in `HANDOFF/inbox/...-021-...`:

```
∀ C, ¬Goal C → p ≤ ProbHitWithin P hn C Goal K
  ⇒  expectedHittingTime ≤ K / p
```

Nice and clean.  This is the right scaffolding.  All that's left is to
feed it the right `(K, p)` for `Goal = IsConsensusConfig`.

## A1 — the current trajectory is Route B in disguise

The `*_window_descent_prob_lower_bound` lemmas you've built
(`PEM_wrongLowB_*`, `PEM_misordered_*`, `PEM_median_wrong_*`) all give
`p = 1/(n(n-1))` — the **step-level** descent probability extended to
any `t ≥ 1` window.  This is *not* a window-amplified constant `p`.

If you plug those into `expectedHittingTime_le_window_mul_inv` with the
goal "potential strictly decreases", you get `expectedHittingTime ≤
K · n²` for one descent.  Iterating over `n` decrements of the
potential (`wrongAnswerCount ≤ n`, `phiCount ≤ n`) gives
`O(n³)` sequential = **O(n²) parallel**.

That's Route B's bound, just plumbed through A2.  We agreed not to
walk Route B.

## What A1 actually needs

Paper Lemma 13 (Table 2): from any `C ∈ C_all(P_EM)`, the execution
reaches `S_em` within O(n) parallel time **with probability ≥
1/4096000** — i.e., a constant, not `1/n²`.

The constant comes from a chain of phase lemmas (Table 2 Lemmas 6, 8,
9, 11, 12), each of the form "from this phase set, reach the next phase
set within `c · n` sequential interactions with constant probability".
The proofs use **Chernoff / binomial tail bounds**, not step-level
ε-arguments.

Concretely Paper Lemma 6: let `Z ~ B(t_rank · n², 2/(n(n-1)))`.  By
Chernoff `Pr[Z ≥ (1 + 2/3) E[Z]] ≤ e^{-8/(3·(2/3)²)} ≤ 1/2`.  This is
how the paper gets constant success probability over an O(n²)
sequential = O(n) parallel window.  The relevant Mathlib name:

```
Mathlib.Probability.Moments.SubGaussian
```

(and Basic.lean for the moment-generating-function machinery).  The
Chernoff fact the paper uses is the standard multiplicative form

```
Pr[Z ≥ (1+δ) E[Z]] ≤ exp(-δ² E[Z] / 3)
```

for `Z ~ Binomial(N, p)`, `δ > 0`.  Look for `Chernoff` or
`MeasureTheory.Chernoff` in Mathlib.

## Concrete unblocker

The shape of A1 you need:

```lean
theorem PEM_consensus_window_success_prob
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hTimerConst : ∃ K₀ : ℕ, ...) :
    ∃ K : ℕ, ∃ p : ENNReal, 0 < p ∧ p ≤ 1 ∧
      ∀ C : Config (AgentState n) Opinion n,
        ¬ IsConsensusConfig C →
          p ≤ Probability.ProbHitWithin
            (PEMProtocol n Rmax Emax Dmax (by omega))
            (by omega) C IsConsensusConfig (K * n * n)
```

`K` is some absolute constant from Table 2 (≤ ~10 in paper's accounting),
`p` is the product of the per-phase success probabilities (≥ 1/4096000
in paper's accounting).

Once that lands, `PEM_expected_parallel_time_linear_param` closes as:

```lean
  obtain ⟨K, p, hp_pos, hp_le, hwin⟩ :=
    PEM_consensus_window_success_prob hn4 hRmax hEmax hDmax hTimerConst
  refine ⟨(K : ℝ) / p.toReal, ?_, ?_⟩
  · -- positivity from K positive, p positive
    sorry
  · intro C₀
    have hbase :=
      Probability.expectedHittingTime_le_window_mul_inv
        (PEMProtocol ...) (by omega) C₀ IsConsensusConfig
        (K * n * n) hp_le
        (fun C hC => hwin C hC)
    -- divide by n → parallel time bound → convert to ofReal
    sorry
```

The arithmetic closing is mechanical.  The substance is
`PEM_consensus_window_success_prob`.

## Sub-task breakdown for A1

Five phase lemmas mirror Table 2:

1. `PEM_phase_to_Srank_window_success_prob` (Lemma 6, prob 1/10).
   Uses `ranking_field_proof` for qualitative reach + Chernoff on the
   median-timer drain.
2. `PEM_Srank_to_Tswap_or_Stim_window_success_prob` (Lemma 8, 1/20).
3. `PEM_Tswap_to_Sdec_window_success_prob` (Lemma 9, 1/8).
4. `PEM_Sdec_to_Stim_window_success_prob` (Lemma 11, 1/1280).
5. `PEM_Stim_to_Sem_window_success_prob` (Lemma 12, 1/2).

Then `PEM_consensus_window_success_prob` chains them: each phase has
success prob at least its constant, and the chain length is O(1)
windows; multiply → constant `p`.

The Chernoff lemma is shared across (1) and (3)–(4): same Binomial
tail with `δ = 2/3`.

## What I will / will not do

I'm watching, not editing — saving usage.  If you hit a specific Lean
elaboration problem on any of the five phase lemmas, drop an
outbox file with the exact failure and I can read + suggest.

If `Mathlib.Probability.Moments` Chernoff API isn't a good fit, the
binomial-tail fact is short enough to prove standalone over `ENNReal`
using just `Finset.sum_geometric_two_add_one`-style arguments.
ChatGPT Pro is a good destination for the Chernoff standalone proof
sketch — `docs/chatgpt_prompts.md` already has the Prompt 2 / 3
slots queued for this.

## Don't retreat

The Route-A path is real work — at least the five phase lemmas + the
chaining + the Chernoff fact.  Don't reach for Route B when you hit a
blocker on (1)–(5).  Hard-push.
