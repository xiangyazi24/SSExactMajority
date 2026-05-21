# Sorry Map — 4 remaining sorry's in Time.lean

**From:** Zinan  
**Date:** 2026-05-20  

## Sorry locations (all in SSExactMajority/UpperBound/Time.lean)

### 1. `PEM_ranking_expected_hitting_time` (line ~5855)
```
∀ C₀, IsTimerBoundedConfig (7*(Rmax+4)) C₀ →
  expectedHittingTime P C₀ InSrank ≤ (Rmax * n * n : ℕ)
```
**Math:** From any config with bounded timers, E[T to all-settled-with-distinct-ranks] ≤ Rmax·n².
**Approach:** Use `expectedHittingTime_le_of_variable_descent` with potential = misorderedCount or number of unsettled agents. The ranking protocol (`rankDeltaOSSR`) settles agents via binary-tree recruitment and resolves rank collisions via reset.
**Codex assignment: YES**

### 2. `PEM_swap_expected_hitting_time` (line ~5868)
```
∀ C, InSrank C →
  expectedHittingTime P C InSswap ≤ (2 * n * n : ℕ)
```
**Math:** From InSrank, E[T to InSswap (wrongLowBCount = 0)] ≤ 2n².
**CRITICAL ISSUE:** InSrank is NOT invariant under PEMProtocolCoupled. `phase4_propagate` can set agents to Resetting when median timer reaches 0. So `PEM_swap_phase_expected_until_swap_or_exit_le_sum` gives E[T to InSswap ∨ ¬InSrank], NOT E[T to InSswap].
**Analysis:** From InSrank, rankDeltaOSSR is identity (both Settled, distinct ranks). Timer decrement requires the specific (median, highest-rank) pair to interact. Timer starts at 7*(Rmax+4). During expected ~1.6n² swap steps, expected timer decrements ≈ 3.2. Timer reaches 0 with probability ≈ exp(-Ω(Rmax)). For formalization, need one of:
  a) Chebyshev bound on timer decrements during swap window (cleanest)
  b) Direct ProbHitWithin argument: P(swap before reset AND within 4n²) ≥ 1/2
  c) Coupling: run swap and timer as independent processes, bound their race
**Zinan assignment: YES**

### 3. `PEM_consensus_expected_hitting_time` (line ~5881)
```
∀ C, InSswap C →
  expectedHittingTime P C IsConsensusConfig ≤ (10 * Rmax * n * n : ℕ)
```
**Math:** From InSswap, E[T to consensus] ≤ 10·Rmax·n². Combines decision (Lemma 9) + propagation (Lemma 11).
**Available tools:** `PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le` (decision one-step), `expectedHittingTime_add_le` (strong Markov).
**Codex assignment: YES**

### 4. `PEM_end_to_end_expected_parallel_time` (line ~5894) — final sorry
Chain construction + conversion from ProbHitWithin to expectedParallelTime. The chain `hChain` is already built (ProbHitWithin ≥ 1/8). Need to convert to expected parallel time using `pem_table2_window_to_expectedParallelTime` or similar.
**Zinan assignment: YES** — straightforward once bounds 1-3 are proved.

## Build command
```
~/.openclaw/workspace/scripts/remote-build.sh SSExactMajority --file SSExactMajority/UpperBound/Time.lean
```

## STRICT: NO AXIOM, NO SORRY (except current 4 placeholders)
