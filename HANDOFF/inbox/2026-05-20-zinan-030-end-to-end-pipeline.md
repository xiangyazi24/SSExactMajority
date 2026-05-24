# End-to-End Time Bound: 3 Expected Hitting Time Bounds

**From:** Zinan  
**Date:** 2026-05-20  
**Priority:** HIGH — this is the last step to close the full O(Rmax·n) formalization

## Current State

- 0 sorry, 0 custom axiom, build clean on uisai1
- Top-level theorems (`PEM_expected_parallel_time`, `PEM_consensus_ProbHitWithin_from_phases`) are **conditional** on phase probability hypotheses
- All composition infrastructure proved: `ProbHitWithin_add_ge_mul`, strong Markov, variable-rate descent, Markov inequality
- **What's missing:** 3 unconditional expected hitting time bounds that feed into the existing composition theorem

## Target: `PEM_consensus_ProbHitWithin_from_expected_phases` (Time.lean:4288)

This theorem converts 3 E[T] bounds into the full ProbHitWithin ≥ 1/8 chain. It needs:

### Bound 1 — Ranking Phase
```
∀ C₀, expectedHittingTime (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C₀ InSrank ≤ MRank
```
**Math:** From any initial config, E[T to reach InSrank] ≤ O(Rmax·n²).
Paper: Lemma 6. Potential: misorderedCount or number of unsettled agents.
**Available tools:** `expectedHittingTime_le_of_variable_descent`, `expectedHittingTime_le_of_potential_descent`.
**Challenge:** Need to identify the right potential function and show one-step descent probability.

### Bound 2 — Swap Phase
```
∀ C, InSrank C → expectedHittingTime (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C InSswap ≤ MSwap
```
**Math:** From InSrank, E[T to reach InSswap] ≤ O(n²).
Paper: Lemma 8. Potential: wrongLowBCount.
**Available tools:** `PEM_swap_phase_expected_until_swap_or_exit_le_sum` (ALREADY PROVED) — but targets InSswap ∨ ¬InSrank, not InSswap alone.
**Key question:** Is InSrank invariant under PEMProtocolCoupled? If yes, ¬InSrank never happens and the existing theorem directly gives E[T to InSswap]. Check whether propagate-reset can trigger from InSrank.
**Alternative:** If InSrank is NOT invariant, use strong Markov: E[T to InSswap] ≤ E[T to InSswap ∨ ¬InSrank] + sup_{¬InSrank} E[T to InSrank] · P(exit to ¬InSrank) / P(exit to InSswap).

### Bound 3 — Decision + Propagation (combined)
```
∀ C, InSswap C → expectedHittingTime (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C IsConsensusConfig ≤ MConsensus
```
**Math:** From InSswap, E[T to consensus] ≤ O(Rmax·n²).
Paper: Lemmas 9 + 11 combined. Potential: wrongAnswerCount + timer-based bounds.
**Available tools:** `PEM_decision_phase_probReached_lower_bound`, various one-step descent lemmas, `expectedHittingTime_add_le`.
**Challenge:** Combines decision (wrong answers decrease) and propagation (correct answer spreads). May need strong Markov composition.

## Composition Pipeline (already proved)

Once the 3 bounds are proved:
```
[Bound 1, 2, 3]
  → PEM_consensus_ProbHitWithin_from_expected_phases  (Time.lean:4288)
  → ProbHitWithin ≥ (1/2)³ = 1/8
  → pem_table2_window_to_expectedParallelTime         (Time.lean:4328)
  → E[T_parallel] ≤ O(Rmax·n)
```

## Window Parameters

For `PEM_consensus_ProbHitWithin_from_expected_phases`:
- MRank: E[T] bound for ranking → tRank = 2*MRank (Markov doubles)
- MSwap: E[T] bound for swap → tSwap = 2*MSwap
- MConsensus: E[T] bound for consensus → tConsensus = 2*MConsensus
- Need: 2*M ≤ t + 1, so set t = 2*M

Paper windows: tRank = 2·Rmax·n², tSwap = 4·n², tConsensus = 20·Rmax·n².
So: MRank ≤ Rmax·n², MSwap ≤ 2·n², MConsensus ≤ 10·Rmax·n².

## Build & File Instructions

- NEVER run `lake build` locally (Mac mini 8GB → freeze)
- Remote build: `~/.openclaw/workspace/scripts/remote-build.sh SSExactMajority`
- Single file: `~/.openclaw/workspace/scripts/remote-build.sh SSExactMajority --file SSExactMajority/UpperBound/Time.lean`
- All new theorems go in `SSExactMajority/UpperBound/Time.lean`
- Read `~/.openclaw/workspace/formalization-playbook.md` for proof standards

## Task Split (Proposed)

- **Codex:** Bound 1 (ranking E[T]) and Bound 3 (consensus E[T]) — these need new potential arguments
- **Zinan:** Bound 2 (swap E[T]) — closest to done, need to resolve InSrank invariant question
- **Joint:** Final wiring into end-to-end theorem

## STRICT: NO AXIOM, NO SORRY
