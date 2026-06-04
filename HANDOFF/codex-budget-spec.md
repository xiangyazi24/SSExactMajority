# Codex task (uisai1): reset-budget potential — bound TOTAL resets (the self-stab crux)

Blueprint (docs/OPTIMAL_BOUND_COMPLETION.md): global supermartingale ψ = φ_progress +
W·resetBudget, clean negative drift via the augmented-potential trick, feeding the PROVEN
expectedHittingTime_le_of_drift. The one missing protocol fact:

A `resetBudget : Config → ℕ` such that:
1. resetBudget is bounded by an explicit poly on IsBoundedConfig (target O(n) or O(n+Emax)).
2. resetBudget does NOT increase on any step on IsBoundedConfig (the key — it's a budget).
3. At each FRESH-RESET step (collision: same-rank Settled pair → Resetting; error: errorcount=0
   Unsettled pair → Resetting), resetBudget strictly DECREASES (the reset resolves an inconsistency).

NEW file SSExactMajority/UpperBound/Time/ResetBudget.lean.

## Investigate (report precisely)
What monotone quantity is RESOLVED by a reset? Candidates:
- collision reset resolves a DUPLICATE rank → #rank-collisions = #{(a,b): a≠b, both Settled, same rank}
  decreases. Bound ≤ n². 
- error reset resolves a detected inconsistency (errorcount mechanism) → some error-count sum.
Look at rankDeltaOSSR / transitionPEM collision + error-monitoring branches (Protocol/RankDelta.lean,
Convergence/BurmanProof.lean) to find the EXACT quantity each reset branch decreases.

## FIRST sub-goal
Define resetBudget (best candidate) and prove ONE of {1,2,3} cleanly — ideally (2) non-increase or
(3) strict-decrease-at-collision. Report which you proved and the exact obstruction for the rest.
This is exploratory on the genuine crux — be quantitative about what each reset branch changes.

## HARD RULES
- NO sorry/axiom/native_decide. Report exact obstruction for unproven parts.
- ONLY ResetBudget.lean. Self-verify lake env lean. NEVER lake build. Report findings precisely
  (which quantity, what each reset branch does to it, what you proved).
