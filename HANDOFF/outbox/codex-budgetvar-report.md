## 2026-06-03 codex budget variation

Read:

- `HANDOFF/codex-budgetvar-spec.md`
- `SSExactMajority/Protocol/RankDelta.lean`
- `SSExactMajority/Protocol/Transition.lean`
- `SSExactMajority/UpperBound/Time.lean` for `IsBoundedConfig`

Budget used:

- `budgetTot C := resetBudget C + structuralErrorBudget C` (unweighted).

Lean additions in `SSExactMajority/UpperBound/Time/ResetBudget.lean`:

- `budgetTot`
- `offdiagPairsIncident`, `offdiagPairsIncident_card_le`
- `resetBudget_le_add_single_changed`
- `resetBudget_le_add_two_changed`
- `resetBudget_step_le_add_two_changed`
- `structuralErrorBudget_le_of_endpoint_imp`
- `structuralErrorBudget_step_le_of_endpoint_imp`
- `budgetTot_step_le_add_two_changed_of_endpoint_imp`
- recruit branch:
  `rankDeltaOSSR_recruit_ab_roles`,
  `rankDeltaOSSR_recruit_ab_child_rank`,
  `rankDeltaOSSR_recruit_ba_roles`,
  `rankDeltaOSSR_recruit_ba_child_rank`,
  `transitionPEM_recruit_ab_not_unsettled`,
  `transitionPEM_recruit_ba_not_unsettled`,
  `structuralErrorBudget_le_at_recruit_ab`,
  `structuralErrorBudget_le_at_recruit_ba`,
  `budgetTot_le_add_two_at_recruit_ab`,
  `budgetTot_le_add_two_at_recruit_ba`
- settled-distinct phase4 entry:
  `transitionPEM_settled_distinct_not_unsettled`,
  `structuralErrorBudget_le_at_settled_distinct`

Also added root wrapper `ResetBudget.lean` importing the real module, so the
literal handoff check command can be run from the project root after producing
the module olean.

Formal quantitative facts:

- If one endpoint is the only role/rank-relevant changed endpoint, new ordered
  same-rank settled pairs are incident to that endpoint, hence at most
  `2*(n-1)`.
- Any off-diagonal `Config.step` changes only two endpoints, hence
  `resetBudget (step) ≤ resetBudget C + 2*(n-1)+2*(n-1)`.
- If every post-step `Unsettled ∧ errorcount≤1` endpoint was already such an
  endpoint before the step, then `structuralErrorBudget` is non-increasing.
- For the full PEM recruit branches, both post-transition endpoints are not
  `Unsettled`; therefore `structuralErrorBudget` is non-increasing, and the
  formal combined bound is
  `budgetTot (step) ≤ budgetTot C + 2*(n-1)+2*(n-1)`.
- For Settled/Settled distinct-rank interactions (the decision/swap/propagate
  entry, excluding collision), both post-transition endpoints are not
  `Unsettled`; therefore `structuralErrorBudget` is non-increasing.

Branch conclusions:

- Recruit: yes, on a general `IsBoundedConfig`, recruit can create a same-rank
  Settled pair.  `IsBoundedConfig` bounds only
  `timer/resetcount/errorcount/delaytimer/children`; it does not assert rank
  uniqueness.  `rankDeltaOSSR` assigns the child rank
  `2*parent.rank.val + parent.children + 1`; if any bystander is already
  Settled at that rank, the new child collides with it.  Exact raw recruit
  increase is `2*m`, where `m` is the number of pre-existing Settled agents at
  the child rank, so the per-recruit maximum is `2*(n-1)` ordered pairs.
  Full PEM may subsequently swap endpoint states, decide answers, or propagate
  reset; swap/decide preserve the rank multiset and propagation reset only
  removes Settled endpoints, so the same exact conceptual max remains
  `2*(n-1)`.  The Lean file currently proves the child-rank equation,
  structural non-increase, and the conservative full-step combined bound
  `+4*(n-1)`.
- Wake-up: a Resetting leader waking through `resetOSSR` becomes Settled at
  rank 0 and can create rank-0 collisions.  One waking leader can add at most
  `2*(n-1)`.  Two leaders waking in the same interaction can add at most
  `4*n-6` ordered pairs.  A follower wake becomes Unsettled with
  `errorcount = Emax`; under `1 < Emax` it is not a structural-error agent
  (`resetOSSR_not_structural_error_of_Emax_gt_one`).
- Timer/resetcount drain inside `propagateReset`: no new Settled endpoint and
  no new low-error Unsettled endpoint; budgets are non-increasing unless the
  step is actually a wake-up, covered above.
- Decision/swap: rankDelta is identity on Settled distinct ranks.  Swap only
  permutes endpoint states; decide only changes answers.  `resetBudget` is
  unchanged, and `structuralErrorBudget` is formally non-increasing.
- Propagate without reset: only answer/timer changes, so both budgets are
  unchanged.  Propagate with disagreement reset sends Settled endpoints to
  Resetting, so `resetBudget` is non-increasing and `structuralErrorBudget`
  is non-increasing.
- Dormant follower: while dormant it remains Resetting; when it wakes as a
  follower, it becomes Unsettled with `errorcount = Emax`, so for `1 < Emax`
  it does not create a structural-error agent.  It cannot increase
  `resetBudget`.  Dormant leader wake is the wake-up case above.

Consequence:

- Clean global monotonicity of `resetBudget` is false on general
  `IsBoundedConfig`: recruit and leader wake-up can create same-rank Settled
  pairs.
- A bounded-compensator argument is needed.  Recruits contribute at most
  `2*(n-1)` per recruit; wake-up leaders contribute at most `2*(n-1)` for one
  leader or `4*n-6` if two leaders wake together.  The global number of
  recruit creations still needs to be charged to a separate ranking/entry
  count, not to `IsBoundedConfig` alone.

Verification:

```bash
PATH=$HOME/.elan/bin:$PATH lake env lean SSExactMajority/UpperBound/Time/ResetBudget.lean
PATH=$HOME/.elan/bin:$PATH lake env lean -o .lake/build/lib/lean/SSExactMajority/UpperBound/Time/ResetBudget.olean -i .lake/build/lib/lean/SSExactMajority/UpperBound/Time/ResetBudget.ilean SSExactMajority/UpperBound/Time/ResetBudget.lean
PATH=$HOME/.elan/bin:$PATH lake env lean ResetBudget.lean
rg -n "sorry|axiom|native_decide" ResetBudget.lean SSExactMajority/UpperBound/Time/ResetBudget.lean
```

The Lean check passed.  The forbidden-construct grep had no matches.
