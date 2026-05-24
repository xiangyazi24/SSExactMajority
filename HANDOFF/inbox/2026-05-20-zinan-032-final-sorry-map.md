# Final Sorry Map — 4 sorry's, 3 critical

**Date:** 2026-05-20
**Status:** End-to-end theorem `PEM_end_to_end_ProbHitWithin` type-checks.
ProbHitWithin(consensus, (22Rmax+4)n²) ≥ 1/16 from IsInitialConfig.

## Architecture

```
Phase A: any → InSrank ∧ timer∈[2, 7(Rmax+4)]     [sorry 1: ranking E[T]]
         ProbHitWithin ≥ 1/2 via Markov

Phase B: InSrank+timer≥2 → InSswap+timer∈[1,K]     [sorry 3: swap ProbHitWithin]
         ProbHitWithin ≥ 1/4 (timer union bound + swap E[T])

Phase C: InSswap+timer≥1+timer≤K → consensus       [sorry 2: consensus E[T]]
         ProbHitWithin ≥ 1/2 via Markov

Chain:   ProbHitWithin_add_ge_mul × 2
Product: (1/2) · (1/4) · (1/2) = 1/16 ✓
```

## Sorry Locations (SSExactMajority/UpperBound/Time.lean)

### Sorry 1 — `PEM_ranking_expected_hitting_time` (line ~5868)
```
E[T to InSrank ∧ timer≥2 ∧ timer≤K from IsInitialConfig] ≤ Rmax·n²
```
HARDEST. Requires: ranking protocol potential descent under random scheduler.
Key: binary-tree recruitment (rankDeltaOSSR), collision detection, reset mechanism.
Potential: number of unsettled agents + collision count.

### Sorry 2 — `hBound` in swap helper (line ~5889)
```
Σ n²/(k+1)² ≤ 2n² (ENNReal arithmetic)
```
NON-CRITICAL (not in main chain). Pure arithmetic via telescoping.

### Sorry 3 — `PEM_swap_ProbHitWithin_InSswap` (line ~5937)
```
ProbHitWithin(InSswap∧timer≥1∧timer≤K, 4n²) ≥ 1/4 from InSrank+timer≥2
```
Requires: union bound on ProbHitWithin + Markov on timer decrements.
ProbHitWithin(InSswap ∨ ¬InSrank) ≥ 1/2 (from existing swap E[T]).
P(¬InSrank) ≤ δ < 1/4 (Markov: expected timer decrements / timer_initial).
Difference: ≥ 1/2 - 1/4 = 1/4.

### Sorry 4 — `PEM_consensus_expected_hitting_time` (line ~5912)
```
E[T to consensus from InSswap+timer≥1+timer≤K] ≤ 10·Rmax·n²
```
Codex working on it. Decision phase: PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le.
Propagation: CorrectResetSeed descent + nonResettingCount.
Compose via expectedHittingTime_add_le.
