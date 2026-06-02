# SSExactMajority — Project Understanding

## What's proved (0 sorry, 0 axiom, 0 error)

### Theorem 4 (Correctness)
P_EM_solves_SSEM_final: P_EM is a self-stabilizing silent exact majority protocol.
- From ANY initial configuration, ∃ deterministic schedule reaching consensus
- Consensus is output-stable and correct (majority output)
- #print axioms: {propext, Classical.choice, Quot.sound}

### Finite Expected Time
PEM_expected_time_finite: E[T to consensus] < ⊤ from any initial config.
PEM_expected_parallel_time_finite: E[parallel time] < ⊤.

### Sub-phase polynomial bounds
- Timer drain: E ≤ 7(Rmax+4)·n(n-1)
- CRS descent: E ≤ n²(n-1), nRC non-increasing under CRS
- allR → Phase1Goal: E ≤ Rmax·n²
- allR → consensus: E ≤ Rmax·n² + B (B finite)

## What's NOT proved (the O(n) parallel time bound)

Paper Theorem 4 claims O(n) expected parallel time. This requires:

### hPropagationLive (Time.lean:6381)
From InSswap + MAC + timer∈[1,7(Rmax+4)] + ¬consensus:
  probReached to consensus within 20·Rmax·n² ≥ 1/1280

### Why it's hard
Phase1Goal → consensus has no polynomial bound. The sub-phases
(ranking, swap, decision) each have or exit conditions that trigger
Propagate-Reset. The paper (Lemmas 6-12) proves each cycle succeeds
with constant probability using Chernoff bounds on:
- Coupon collector for epidemic (Lemma 1)
- Binary tree ranking convergence (Lemma 3)
- Timer reaching 0 without reset (Lemma 10)

### What would unblock it
1. Formalize one-way epidemic O(n log n) ProbHitWithin bound
2. Formalize ranking O(n²) ProbHitWithin bound from FreshRankingStart
3. Prove each restart cycle succeeds with constant probability
4. Compose via ProbHitWithin_add_ge_mul → hPropagationLive
5. Plug into PEM_expected_parallel_time_from_phase_bounds (sorry-free)

## Architecture
- 63 files, ~62,000 lines of Lean 4
- Convergence/ (40K lines): BurmanProof, BurmanConvergenceFinal
- UpperBound/Time/ (15K lines): ranking bounds, CRS, timer drain
- Probability/ (5K lines): expected hitting time framework
- Protocol/ (800 lines): transition function definitions
