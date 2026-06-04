# Codex task (uisai1): combined-budget variation across ALL branches

Strict-drops DONE (ResetBudget.lean): resetBudget (collision, ≤n²) and structuralErrorBudget
(error, ≤n) each strictly drop at their reset. To close "total resets bounded" for the global
supermartingale, characterize how the budgets change on the NON-reset branches.

budgetTot C := resetBudget C + structuralErrorBudget C  (or weighted — your call; report which).

## Investigate per-branch (transitionPEM / rankDeltaOSSR), report EXACTLY:
For each non-reset transition branch — recruit, wake-up, timer-drain, decision/swap, propagate,
dormant-follower — state whether it can INCREASE resetBudget (create a new same-rank Settled pair)
or structuralErrorBudget (create an Unsettled with errorcount≤1), and by how much per step.

KEY question: does RECRUIT (Settled+Unsettled → new Settled at child rank) ever create a
same-rank-Settled pair on a general IsBoundedConfig (i.e. assign a rank already held by another
Settled)? If yes, resetBudget is NOT globally monotone — but the TOTAL increase may still be
bounded (recruits ≤ n total, each +≤? pairs). Quantify the per-recruit max increase.

## Deliverable (prove what's clean, report the rest)
- Per-branch budget-change lemmas you can prove (e.g. recruit_resetBudget_le_succ,
  wake_structuralErrorBudget_le, etc.) — ideally `budgetTot (step) ≤ budgetTot C + c` for an
  explicit small c per branch, OR `≤ budgetTot C` (non-increase) where it holds.
- A REPORT: which branches are non-increasing, which can increase + by how much + bounded by what
  global count (recruits ≤ n, etc.). This decides: clean non-increase vs bounded-compensator.

## HARD RULES
- NO sorry/axiom/native_decide. ONLY ResetBudget.lean. Self-verify lake env lean. NEVER lake build.
  Be quantitative per branch.
