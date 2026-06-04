## 2026-06-03 codex collisionBank

Implemented:

- `SSExactMajority/UpperBound/Time/CollisionBank.lean`
- root wrapper `CollisionBank.lean` for the literal check command

Definitions:

- `unsettledAgents C := Finset.univ.filter (fun w => (C w).1.role = .Unsettled)`
- `unsettledCount C := (unsettledAgents C).card`
- `collisionBank C := resetBudget C + 2 * n * unsettledCount C`

Lemma status:

- PROVED `collisionBank_le : collisionBank C ≤ 3 * n * n`.
- PROVED `collisionBank_strict_decrease_at_collision` for the concrete coupled
  PEM step using `rankDeltaOSSR`; it reuses
  `resetBudget_strict_decrease_at_collision` and proves `unsettledCount`
  unchanged because the two collision endpoints move `Settled -> Resetting`.
- PROVED `collisionBank_nonincrease_at_recruit`.  Formal shape: one recruited
  endpoint starts `Unsettled`, is not `Unsettled` afterward, and every other
  agent preserves role/rank.  The file proves the needed reset-budget bound
  directly as `resetBudget_le_add_single_role_rank_changed`, giving
  `resetBudget C' ≤ resetBudget C + 2*(n-1)`, while the unsettled slack drops
  by exactly `2*n`.
- PROVED `collisionBank_nonranking_unchanged` and
  `collisionBank_nonincrease_nonranking`: if all agents preserve role/rank,
  then both `sameRankSettledPairs` and `unsettledCount` are unchanged, hence
  the bank is unchanged.

Additional exact wake accounting:

- PROVED `collisionBank_eq_add_two_n_of_single_unsettled_wake`.  If one
  non-Settled, non-Unsettled endpoint wakes into `Unsettled` and every other
  role/rank is unchanged, then
  `collisionBank C' = collisionBank C + 2*n`.
- Interpretation for `resetOSSR` follower wake:
  `resetOSSR Emax hn s` with `s.leader = .F` creates an `Unsettled` follower
  and does not create same-rank Settled pairs.  Therefore the collision-bank
  increase is exactly `+2*n` per woken follower.  If two followers wake in the
  same transition, the exact contribution is `+4*n`.  This is the epoch term;
  no bound is attempted here.

Verification:

```bash
PATH=$HOME/.elan/bin:$PATH lake env lean SSExactMajority/UpperBound/Time/CollisionBank.lean
PATH=$HOME/.elan/bin:$PATH lake env lean -o .lake/build/lib/lean/SSExactMajority/UpperBound/Time/CollisionBank.olean -i .lake/build/lib/lean/SSExactMajority/UpperBound/Time/CollisionBank.ilean SSExactMajority/UpperBound/Time/CollisionBank.lean
PATH=$HOME/.elan/bin:$PATH lake env lean CollisionBank.lean
rg -n "sorry|axiom|native_decide" CollisionBank.lean SSExactMajority/UpperBound/Time/CollisionBank.lean
```

All Lean checks passed.  The forbidden-construct grep had no matches.
