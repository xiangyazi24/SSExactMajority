# Codex task (uisai1): error-reset budget — close the self-stab crux

Collision half DONE (ResetBudget.lean): resetBudget=#same-rank-Settled-pairs ≤n², strict drop at
collision (resetBudget_strict_decrease_at_collision). Need the ERROR-reset branch handled so the
TOTAL-reset-bounded fact closes (feeds the global supermartingale ψ=φ_progress+W·budget → drift theorem).

Obstruction (your prior finding): error reset = rankDeltaOSSR Part 4 (Unsettled, errorcount→0 ⟹
Resetting); but resetOSSR re-initializes a fresh Unsettled with errorcount=Emax, so a naive global
errorcount-sum is NOT monotone.

## Investigate + prove (in ResetBudget.lean, you own it)
The re-injection (errorcount:=Emax) happens INSIDE a reset (resetOSSR), which is itself a
collision/error event. So a LEXICOGRAPHIC or WEIGHTED budget should work:
   budgetTot C := W * resetBudget C + structuralErrorBudget C
where structuralErrorBudget counts the STRUCTURAL inconsistencies an error reset resolves (NOT the
raw errorcount — the actual wrong pointer / wrong rank / parent-child violation the error monitoring
detects). KEY question to answer precisely: what STRUCTURAL inconsistency does the error-reset branch
resolve, and is it re-created by resetOSSR? If resetOSSR's fresh-Unsettled does NOT create a new
structural inconsistency (it just re-enters ranking with errorcount=Emax but no wrong pointer), then
structuralErrorBudget is non-increasing and drops at each error reset.

## FIRST sub-goal
Identify the exact structural quantity the error-monitoring branch checks (read rankDeltaOSSR Part 4
+ the error-detection predicate in Protocol/RankDelta.lean / BurmanProof.lean). Define
structuralErrorBudget; prove EITHER (a) it strictly drops at an error reset, OR (b) the weighted
budgetTot = W*resetBudget + structuralErrorBudget is non-increasing on IsBoundedConfig and strictly
drops at BOTH reset types. Report exactly what each branch does to the chosen quantity + obstruction.

## HARD RULES
- NO sorry/axiom/native_decide. ONLY ResetBudget.lean. Self-verify lake env lean. NEVER lake build.
  Report precisely (the structural quantity, branch-by-branch effect, what proved, what blocks).
