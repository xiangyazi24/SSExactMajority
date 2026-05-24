---
sender: zinan
receiver: codex
topic: Corrected non-vacuous targets — PEM_consensus_window_success_prob_v2 and PEM_expected_parallel_time
status: open
---

# Context

Good catch on the vacuous hTimerConst. I've added corrected (non-vacuous)
theorem statements alongside the old ones.

## New targets (with sorry)

### Window hypothesis v2

```lean
theorem PEM_consensus_window_success_prob_v2
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∃ c : ℕ, 0 < c ∧
      ∀ C : Config (AgentState n) Opinion n,
        ¬ IsConsensusConfig C →
          pemTable2SuccessProb ≤
            Probability.ProbHitWithin
              (PEMProtocol n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (c * Rmax * n * n)
```

Key difference from v1: no `hTimerConst` hypothesis. Window size is
`c * Rmax * n * n` (not `c * n * n`). The `Rmax` factor absorbs the
timer-drain cost.

### Time bound

```lean
theorem PEM_expected_parallel_time
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C₀ : Config (AgentState n) Opinion n,
        Probability.expectedParallelTimeToConsensus
          (PEMProtocol n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C₀ ≤
          ENNReal.ofReal (C * Rmax * n)
```

Bound is `O(Rmax * n)`:
- Rmax = O(1) → O(n) (paper's claim)
- Rmax = n → O(n²) (our literal instantiation)

## What to work on

The time bound follows from the window hypothesis v2 by the same
arithmetic as before (just substitute `c * Rmax * n * n` for the window
size `K`). So the real target is `PEM_consensus_window_success_prob_v2`.

The proof strategy is the same as outlined in inbox 023: five-phase
Table 2 composition. The timer drain (Phase 4: Sdec → Stim) now has
window size O(Rmax * n²) sequential instead of O(n²), which is where
the Rmax factor enters.

Build: `lake build SSExactMajority.UpperBound.Time` on uisai1.
PATH needs `$HOME/.elan/bin`.
