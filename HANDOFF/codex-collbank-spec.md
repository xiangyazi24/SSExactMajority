# Codex task (uisai1): collisionBank amortized potential (ChatGPT-validated design)

NEW file SSExactMajority/UpperBound/Time/CollisionBank.lean. Import ResetBudget (reuse
sameRankSettledPairs / resetBudget). This is the amortized bank-account potential that makes the
collision side MONOTONE under recruit (the 2n·unsettled slack pre-pays recruit-created collisions).

## Definitions
- `unsettledCount C := (Finset.univ.filter (fun w => (C w).1.role = .Unsettled)).card`
- `collisionBank C := resetBudget C + 2 * n * unsettledCount C`   (resetBudget = sameRankSettledPairs.card)

## Prove (the validated chain)
1. `collisionBank_le : collisionBank C ≤ 3 * n * n` (resetBudget ≤ n², unsettledCount ≤ n).
2. `collisionBank_strict_decrease_at_collision`: same-rank Settled pair (i,j) collision step ⟹
   collisionBank strictly drops. (resetBudget strictly drops by ≥1 — reuse
   resetBudget_strict_decrease_at_collision; unsettledCount UNCHANGED: collision sends Settled→Resetting,
   not Unsettled. So collisionBank drops.)
3. `collisionBank_nonincrease_at_recruit` (THE KEY): a recruit step (Settled+Unsettled → new Settled
   at child rank) ⟹ collisionBank C' ≤ collisionBank C. Mechanism: unsettledCount drops by exactly 1
   (the recruited agent Unsettled→Settled), so 2n·unsettled drops by 2n; resetBudget rises by at most
   2(n-1) < 2n (new Settled creates ≤2(n-1) ordered same-rank pairs). Net ≤ 0. (Reuse cxbv's
   budgetTot_le_add_two_at_recruit_ba / the recruit creation bound in ResetBudget.lean if it fits;
   otherwise prove resetBudget(recruit) ≤ resetBudget + 2(n-1) directly.)
4. `collisionBank_nonincrease_nonranking`: branches not touching ranking roles/ranks (propagate-no-reset,
   timer/decision) leave sameRankPairs and unsettledCount unchanged ⟹ collisionBank unchanged.
5. REPORT: characterize the resetOSSR follower-wake branch (Resetting→Unsettled): quantify the
   collisionBank INCREASE (+2n per woken follower). This is the epoch term — report it precisely, do
   NOT try to bound it here (it needs the irreversible epoch measure, separate task).

## HARD RULES
- NO sorry/axiom/native_decide. Prove 1-4; report 5 precisely + any obstruction. ONLY CollisionBank.lean.
  Self-verify lake env lean. NEVER lake build. Report each lemma PROVED/BLOCKED.
