# Codex task (uisai1): bridge — execution/ProbHitWithin measure ↔ schedulerPrefixPMF cylinder

Connect lemma 2 to the RENEWAL measure. We have (SelectionCount.lean) the cylinder
P_schedulerPrefixPMF[agent a selected on T] = (2/n)^|T|. We need the disruption tail in terms of the
EXECUTION/ProbHitWithin measure (what the renewal uses, built from stepDist/nthStepDist over uniformPair).

## The bridge to prove
The execution is a DETERMINISTIC function of (initial config C₀, scheduler-pair sequence σ), and the
scheduler picks σ as iid uniform off-diagonal pairs. So for any event E that depends ONLY on σ (the
scheduler prefix) — e.g. "agent a is selected on time-set T", "selectionCount a K ≥ r" — the execution
measure and schedulerPrefixPMF agree:
   P_execution[E(σ)] = P_schedulerPrefixPMF[E].
Concretely, give a tail bound usable by the renewal. Target:
```
theorem disruption_ProbHitWithin_le_choose
  (C₀) (K r : ℕ) (hcert : <disruption within K ⟹ some agent selectionCount ≥ r over the σ prefix>) :
  Probability.ProbHitWithin P hn C₀ DisruptionPredicate K
    ≤ (n : ENNReal) * (Nat.choose K r) * ((2 * (n:ENNReal)⁻¹) ^ r)
```
Route: ProbHitWithin(D) ≤ P_execution[high σ-load] (via disruption_before_K_implies_high_load, the
certificate already in DisruptionTail) = P_schedulerPrefixPMF[high load] (the BRIDGE: execution
σ-marginal = schedulerPrefixPMF) ≤ n·choose·(2/n)^r (selectionCount_tail_le_choose).

## The hard part: the σ-marginal bridge
How does the repo build the execution/ProbHitWithin measure? It composes stepDist (uniformPair-based).
You likely need to augment the chain to TRACK the scheduler prefix (analogous to hitFlagDist tracking
the hit flag — see ExpectedTime.lean hitFlagDist/hitTwoFlagDist), then show its σ-projection =
schedulerPrefixPMF, and the disruption/selection events are σ-measurable. Reuse the hitFlagDist_map_fst
style projection lemmas. If a full measure-equality is heavy, it SUFFICES to prove the one-directional
bound P_execution[D] ≤ P_schedulerPrefixPMF[high load] needed above.

## FIRST sub-goal
Establish the σ-marginal bridge (execution measure agrees with schedulerPrefixPMF on σ-events), OR the
one-sided bound that ProbHitWithin(D) ≤ schedulerPrefixPMF[high load]. Report the exact construction
used and any genuine obstruction (e.g. the execution measure doesn't expose σ — then build the
σ-tracking augmentation).

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide. Grind or precise obstruction to HANDOFF/outbox/codex-bridge-report.md.
- New file SSExactMajority/Probability/SchedulerBridge.lean (or extend SelectionCount). Self-verify
  lake env lean. NEVER lake build.
