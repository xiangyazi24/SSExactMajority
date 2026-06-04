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

## [2026-06-04] Audit-critical structural facts (verified)
- **Correctness is FULLY FORMALIZED (not cited).** `P_EM_solves_SSEM_final` proves `SolvesSSEM (protocolPEM n n n …)` with NO external hypotheses; `#print axioms` = `{propext, Classical.choice, Quot.sound}` only. Ranking convergence is proven by `ranking_field_proof` + `burmanConvergence_concrete` (~32k lines of Burman mechanism). The ONLY thing cited from Burman [12] is the ranking EXPECTED-TIME bound `srank=O(n)` ([12] Thm 4.3), which enters the PARALLEL-TIME keystone as the `h12*` hypotheses. We formalize the renewal/window composition that lifts "ranking O(n) expected" to "PEM O(n) expected".
- **Rmax = n in the formalization, NOT the papers 60 log n.** Forced by `CorrectResetSeed` requiring `nonResettingCount < resetcount` (resetcount:=Rmax, count up to n-1 ⟹ Rmax≥n). This is a DETERMINISTIC reset model vs the papers PROBABILISTIC one (epidemic w.h.p. ⟹ 60 log n suffices). Preserves correctness + O(n) EXPECTED time; sacrifices space-optimality + possibly w.h.p. O(n log n). Decision (accept variant vs reprove faithful) pending Xiang.
- **trank ⟂ Rmax.** Median-timer param (trank, →1 for O(n) time) is independent of reset-counter param (Rmax). The generic-trank O(n)-time work holds under any Rmax choice.
