# Error-reset budget report

## Structural quantity

Read:

- `HANDOFF/codex-errbudget-spec.md`
- `rankDeltaOSSR` Part 4 in `SSExactMajority/Protocol/RankDelta.lean`
- `ErrorTimeoutPairs` in `SSExactMajority/UpperBound/Time/GlobalDrift.lean`

The current formalization does not contain an explicit wrong-pointer /
wrong-rank / parent-child predicate for the error branch.  Part 4 detects a
timed-out Unsettled endpoint: after the earlier `rankDeltaOSSR` branches are
not taken, an endpoint with `role = Unsettled` has its `errorcount`
decremented, and if the post-decrement counter is `0` then both endpoints are
put into `Resetting/L/Rmax`.  The global predicate `ErrorTimeoutPairs` matches
this as `Unsettled ∧ errorcount ≤ 1`, after excluding Resetting/collision and
both recruitment directions.

I therefore defined:

- `structuralErrorAgents C := { w | (C w).role = Unsettled ∧ (C w).errorcount ≤ 1 }`
- `structuralErrorBudget C := (structuralErrorAgents C).card`

This is not the raw errorcount sum.  It is exactly the endpoint-level timeout
condition used by the error-monitoring branch.

## Branch effects

- Error reset: if neither endpoint is already Resetting, neither recruitment
  direction is enabled, and at least one endpoint is in `structuralErrorAgents`,
  then `rankDeltaOSSR` makes both endpoints Resetting.  `transitionPEM`
  preserves those roles through prePhase4 and skips Phase 4 because the pair is
  not both Settled.  In the config step, the timed-out endpoint is removed from
  `structuralErrorAgents`, the other scheduled endpoint is also Resetting, and
  every other agent is unchanged.  Hence `structuralErrorBudget` strictly drops.

- `resetOSSR`: follower reset re-enters as `Unsettled` with
  `errorcount = Emax`.  Proved `resetOSSR_not_structural_error_of_Emax_gt_one`:
  under the standard `1 < Emax` regime, this fresh Unsettled endpoint is not in
  `structuralErrorAgents`.  If `Emax ≤ 1`, the formal statement intentionally
  does not claim this.

- Collision reset: existing `resetBudget_strict_decrease_at_collision` remains
  the collision-side strict-drop theorem.  I did not prove a combined weighted
  `budgetTot`; I used the allowed option (a), a separate strict drop for the
  error-reset structural budget.

## Lean additions

In `SSExactMajority/UpperBound/Time/ResetBudget.lean`:

- `structuralErrorAgents`
- `structuralErrorBudget`
- `structuralErrorBudget_le_linear`
- `resetOSSR_not_structural_error_of_Emax_gt_one`
- `transitionPEM_prePhase4_roles`
- `rankDeltaOSSR_error_timeout_roles`
- `transitionPEM_error_timeout_roles`
- `structuralErrorBudget_strict_decrease_of_endpoint_reset`
- `structuralErrorBudget_strict_decrease_at_error`

## Verification

Ran:

```bash
lake env lean SSExactMajority/UpperBound/Time/ResetBudget.lean
```

Result: passed with no output.

Also checked `ResetBudget.lean` for `sorry`, `axiom`, and `native_decide`;
none were present.
