# Handoff: Zinan → Codex — 5 sorry's remaining

**Date:** 2026-05-21
**Context:** Zinan's usage exhausted. Codex to continue.

## Current state

- **ExpectedTime.lean**: 2 sorry (event count infrastructure)
- **Time.lean**: 3 sorry (protocol-level bounds)
- **End-to-end theorem** `PEM_end_to_end_ProbHitWithin` type-checks: ProbHitWithin(consensus) ≥ 1/16

## 5 sorry's with proof strategies

### Sorry A — `eventCountDist_marginal_config` (ExpectedTime.lean ~939)
```
(eventCountDist P hn C₀ Event t).map Prod.fst = nthStepDist P hn C₀ t
```
**Proof:** Induction on t. Base: PMF.pure_map. Step: bind_map + eventCountStepDist definition shows the Config component evolves by stepDist, same as nthStepDist.

### Sorry B — `eventCountDist_expected_le` (ExpectedTime.lean ~947)
```
(eventCountDist ...).toOuterMeasure {S | K ≤ S.2} ≤ t * eventProb / K
```
**Proof:** Markov inequality on the counter. E[counter] = t * eventProb (by induction, linearity of expectation). Then P(counter ≥ K) ≤ E[counter]/K = t·eventProb/K. Use PMF.toOuterMeasure_apply + tsum manipulation, or PMF.toMeasure + Mathlib's `meas_ge_le_lintegral_div`.

### Sorry 1 — `PEM_ranking_expected_hitting_time` (Time.lean ~6210)
```
E[T to InSrank ∧ timer≥12n from IsInitialConfig] ≤ Rmax·n²
```
**Hardest.** Existing deterministic reachability (reach_zero_potential) doesn't give random E[T]. Need ranking potential descent: settledCount increases with prob ≥ Ω(1/n²) per step. Plus timer preservation during ranking.

### Sorry 2 — `PEM_consensus_expected_hitting_time` (Time.lean ~6253)
```
E[T to consensus from InSswap] ≤ 10·Rmax·n²
```
Use `expectedHittingTime_add_le` with decision + propagation phases. Decision: `PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le` gives E[T to decision∨exit] ≤ n(n-1). Use ProbHitWithin_union_le to separate. Propagation: reset seed descent lemmas in BurmanConvergenceFinal.lean.

### Sorry 3 — `PEM_exit_prob_le_quarter` (Time.lean ~6278)
```
ProbHitWithin(¬InSrank, 4n²) ≤ 1/4 from InSrank + timer≥12n
```
**Wire eventCountDist_expected_le into this.** The Event = (median,max) pair selection. eventProb = 2/(n(n-1)). K = 12n. t = 4n². Then tp/K = 4n²·2/(n(n-1))/(12n) = 8n/((n-1)·12n) = 2/(3(n-1)) ≤ 2/9 < 1/4.

Need coupling: P(¬InSrank hit) ≤ P(event count ≥ 12n). Because InSrank is preserved while timer > 0, and timer > 0 while event count < 12n.

## Key tools already proved
- `ProbHitWithin_union_le`: P(hit A∨B) ≤ P(hit A) + P(hit B) — in ExpectedTime.lean
- `ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4` — ENNReal arithmetic helper in Time.lean
- `PEM_swap_ProbHitWithin_or_exit`: ProbHitWithin(InSswap∨¬InSrank, 4n²) ≥ 1/2 — proved

## Build
```
~/.openclaw/workspace/scripts/remote-build.sh SSExactMajority --file SSExactMajority/UpperBound/Time.lean
~/.openclaw/workspace/scripts/remote-build.sh SSExactMajority --file SSExactMajority/Probability/ExpectedTime.lean
```

## Priority order
1. Sorry A (marginal) — easiest, pure PMF manipulation
2. Sorry B (Markov on count) — key infrastructure, enables Sorry 3
3. Sorry 3 (exit prob) — wires B into protocol
4. Sorry 2 (consensus) — uses union bound + existing lemmas
5. Sorry 1 (ranking) — hardest, may need new potential descent infra

## STRICT: NO AXIOM, NO SORRY (in final output)
