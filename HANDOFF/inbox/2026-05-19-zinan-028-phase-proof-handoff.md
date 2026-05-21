---
sender: zinan
receiver: next-session
topic: Close 4 standalone phase probability theorems
status: open
---

# State

- Time.lean: 4 sorry (standalone phase theorems)
- ExpectedTime.lean: 0 sorry
- Build: clean
- Architecture: fully proved
- File size: ~5400 lines Time.lean, ~2800 lines ExpectedTime.lean

# The 4 sorry's

All in Time.lean, each is a `probReached` or `ProbHitWithin` lower bound:

1. `PEM_rank_phase_probReached_lower_bound` (~line 4994) — Lemma 6
2. `PEM_swap_phase_probReached_lower_bound` (~line 5010) — Lemma 8
3. `PEM_decision_live_phase_probReached_lower_bound` (~line 5026) — Lemma 9
4. `PEM_propagation_live_phase_probReached_lower_bound` (~line 5052) — Lemma 11

# Proof order

Lemma 11 depends on 8 and 9. So: 6 (independent) → 8 → 9 → 11.

# Proof strategy per phase

Each phase proof follows the paper's template:
1. Compute expected time via good-pair counting (harmonic sum or coupon collector)
2. Apply Markov inequality: P(T ≤ 2E[T]) ≥ 1/2
3. For non-absorbing targets: multiply by timer survival probability (Chernoff/Markov on median-timer decrement count)
4. For absorbing target (Phase 4): use ProbHitWithin_le_probReached_of_absorbing

# Missing Lean tools

1. **Expected time from potential descent**: E[T] ≤ Σ 1/p(k) where p(k) is step-descent probability at potential k. Ripple has drift tools but in Kernel framework.

2. **Markov inequality for hitting time**: E[T] ≤ M → ProbHitWithin(2M) ≥ 1/2. We have expected time tools but not this specific conversion.

3. **Timer survival**: P(Binomial(4n², 2/(n(n-1))) < 28) ≥ 1/2. Needs Markov on binomial or Chernoff from Ripple.

4. **Conditional probability / joint event**: P(decision complete ∧ timer alive at t) = P(timer alive) · P(decision | timer alive). The joint-event tool `probReached_ge_of_nthStepDist_subset` exists but needs the concrete event formalization.

# Available tools

- One-step descent probReached bounds: lines 869-1714
- Propagation tools: lines 3083-3616
- Phase composition: lines 5055-5150
- probReached_mono_goal, ProbHitWithin_mono_time
- ProbHitWithin_le_probReached_of_absorbing
- ProbHitWithin_ge_one_sub_pow_of_ProbHitWithin_one_lower_bound (geometric tail)
- ProbHitWithin_ge_one_sub_pow_of_local_one_lower_bound (live-region geometric)
- Ripple: Chernoff (Concentration.lean), Janson geometric (JansonGeometric.lean)

# Paper reference

Kanaya et al. 2025, Section 5.2, Lemmas 6-12, Table 2.
Paper PDF: projects/SSExactMajority/papers/kanaya2025.pdf pages 9-11.
