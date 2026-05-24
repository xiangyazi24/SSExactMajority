---
sender: zinan
receiver: codex
topic: Prove PEM_consensus_window_success_prob — the last sorry in the time-bound layer
status: open
---

# Context

The final theorem `PEM_expected_parallel_time_linear_param` is now **sorry-free**.
It reduces entirely to one lemma:

```lean
theorem PEM_consensus_window_success_prob
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hTimerConst :
      ∃ K₀ : ℕ, ∀ (C : Config (AgentState n) Opinion n) (μ : Fin n),
        InSswap C →
        (C μ).1.rank.val + 1 = ceilHalf n →
        (C μ).1.timer ≤ K₀) :
    ∃ c : ℕ, 0 < c ∧
      ∀ C : Config (AgentState n) Opinion n,
        ¬ IsConsensusConfig C →
          pemTable2SuccessProb ≤
            Probability.ProbHitWithin
              (PEMProtocol n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (c * n * n)
```

Location: `SSExactMajority/UpperBound/Time.lean:3725–3759`

`pemTable2SuccessProb = 1/(10*20*8*1280*2) = 1/4096000` (defined at line 3583).

## What this says

From any non-consensus configuration, within `c·n²` sequential interactions
under uniform random scheduling, the protocol reaches `IsConsensusConfig`
with probability at least `1/4096000`.

## Available infrastructure

### Phase composition (already proved, lines 3613–3724)

`pem_table2_phase_window_to_ProbHitWithin` chains 5 `probReached` hypotheses:

```
hRank : ∀ C₀, 1/10 ≤ probReached P hn2 C₀ SrankPhase tRank
hSwap : ∀ C, SrankPhase C → 1/20 ≤ probReached P hn2 C SswapPhase tSwap
hDec  : ∀ C, SswapPhase C → 1/8  ≤ probReached P hn2 C SdecPhase tDec
hTim  : ∀ C, SdecPhase C → 1/1280 ≤ probReached P hn2 C StimPhase tTim
hSem  : ∀ C, StimPhase C → 1/2   ≤ probReached P hn2 C IsConsensusConfig tSem
```

→ `pemTable2SuccessProb ≤ ProbHitWithin P hn2 C₀ IsConsensusConfig (tRank+tSwap+tDec+tTim+tSem)`

### Phase definitions (Sets.lean)

- `InSrank` — all agents settled, ranks bijective
- `InSswap` — extends InSrank, A-inputs have lower ranks than B-inputs
- `InStim` = `IsConsensusConfig` — InSswap ∧ all answers correct
- `MedianAnswerCorrect` — median-rank agents carry correct answer (Time.lean:55)

### probReached lemmas (ExpectedTime.lean)

- `probReached_zero_of_goal` — at step 0, if goal holds, probReached = 1 (NEW)
- `probReached_add_ge_mul` — 2-phase composition: p·q ≤ probReached(t+k)
- `probReached_one_lower_bound_of_pairSet` — 1-step bound from good-pair count
- `probReached_one_lower_bound_of_step` — 1-step bound from single pair witness

### Step-level probability bounds (Time.lean, lines 836–3575)

Many `probReached` one-step bounds exist:
- `PEM_misordered_*` — swap phase good-pair counts
- `PEM_wrongLowB_*` — wrong-side-B descent bounds
- `PEM_median_wrong_*` — median decision descent
- `PEM_richResetSeed_*` — reset seed propagation
- `PEM_correctResetSeed_*` — reset correctness

These give `1/(n(n-1))` per-step probabilities. Over `O(n²)` steps they give
constant probability — BUT the existing proofs chain them into Route-B (O(n²)
parallel) not Route-A (O(n) parallel).

## What you need to do

### First: verify the statement

Read `SSExactMajority/UpperBound/Time.lean:3725–3759` and confirm:
1. The statement matches the paper's Table 2 claim.
2. The hypotheses are sufficient (especially `hTimerConst`).
3. The conclusion type is compatible with `pem_table2_phase_window_to_ProbHitWithin`.

### Then: prove it

**Route A (preferred):** Use `pem_table2_phase_window_to_ProbHitWithin` with
4 real phases + 1 trivial identity phase:

1. SrankPhase = `InSrank`, tRank = c₁·n², prob ≥ 1/10
2. SswapPhase = `InSswap`, tSwap = c₂·n², prob ≥ 1/20
3. SdecPhase = `InSswap ∧ MedianAnswerCorrect`, tDec = c₃·n, prob ≥ 1/8
4. StimPhase = `IsConsensusConfig`, tTim = c₄·n², prob ≥ 1/1280
5. (identity) tSem = 0, prob 1 (use `probReached_zero_of_goal`)

The hard part is proving the 4 non-trivial phase bounds. Each needs:
- A count of "good pairs" whose interaction advances the phase
- An accumulation argument: over O(n²) steps, enough good pairs fire with constant probability

The accumulation can use:
- Geometric tail: `(1 - 2/(n(n-1)))^t` for a single pair in t steps
- Or: existing `probReached_one_lower_bound_of_pairSet` + `ProbHitWithin_ge_one_sub_pow`

### Build

```bash
# from SSExactMajority project root on uisai1:
lake build SSExactMajority.UpperBound.Time
```

Currently builds with 1 sorry (the target). When you close it, zero sorry.

## Communication

Write results to `HANDOFF/outbox/2026-05-19-codex-028-window-proof.md`.
