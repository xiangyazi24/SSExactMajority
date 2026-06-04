# Codex task (uisai1): selection-count cylinder lemma (instantiate lemma-2's hypothesis)

DisruptionTail.lean's tail bound is CONDITIONAL on a cylinder hypothesis: under the uniform random
ordered-pair scheduler, a fixed agent a is selected on a fixed set of r time-steps with probability
(2/n)^r. Instantiate it (regime-independent — pure scheduler probability).

## Goal
Connect the per-step scheduler measure to the K-step selection-count distribution. Under the scheduler
that at each step picks an ordered pair (i,j), i≠j, uniformly from the n(n-1) off-diagonal pairs:
- per step, P(agent a ∈ {i,j}) = 2(n-1)/(n(n-1)) = 2/n, INDEPENDENT across steps (product measure).
- ⟹ for any fixed r-subset of [0,K) of time indices, P(a selected at all those r steps) = (2/n)^r.
- ⟹ P(selectionCount a K ≥ r) ≤ choose(K, r) · (2/n)^r  (union over r-subsets).

Target lemma (the cylinder hypothesis DisruptionTail needs):
```
theorem selectionCount_tail_le_choose
  (a : Fin n) (K r : ℕ) :
  <scheduler-measure of> {ω | r ≤ selectionCount (sched ω) a K}
    ≤ (Nat.choose K r : ENNReal) * (((2:ENNReal) * (n:ENNReal)⁻¹) ^ r)
```

## Approach
- Find how the repo models the random scheduler's K-step measure (the execution/path distribution).
  Likely stepDist composed K times, OR a product PMF over schedulers. Look in ExpectedTime.lean /
  DriftHittingTime.lean for the path-measure object (the same one ProbHitWithin/stepDist use).
- Per-step selection indicator: P(a selected at step t) = 2/n, a function of the step's pair only.
  Independence across steps = the product structure of the path measure.
- Union bound over the choose(K,r) size-r subsets of time indices; each subset's all-selected event
  has measure (2/n)^r by independence.
- Wire the result to match DisruptionTail's cylinder hypothesis exactly (check its precise statement
  and the measure object it uses — selectionCount / DetScheduler / the path PMF).

## FIRST sub-goal
Identify the repo's K-step scheduler/path measure object and prove the per-step selection probability
= 2/n with cross-step independence. Then the choose-union tail. If the repo genuinely lacks a path
product-measure exposing per-step pairs, BUILD the minimal one (a PMF over (Fin n × Fin n) lists /
the product of uniform off-diagonal-pair PMFs) and relate selectionCount to it. Report the exact
object used.

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide. Grind or precise obstruction to HANDOFF/outbox/codex-cylinder-report.md.
- New file SSExactMajority/Probability/SelectionCount.lean (or extend DisruptionTail if cleaner).
  Self-verify lake env lean. NEVER lake build.
