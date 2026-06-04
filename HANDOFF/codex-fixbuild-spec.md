# Codex task (uisai1): fix DrainProductive olean build + verify the hRank12-eliminated assembly

CRITICAL: `lake build SSExactMajority.UpperBound.Time.DrainProductive` FAILS at
DrainProductive.lean:255:16 "typeclass instance problem is stuck" — even though `lake env lean` on the
file passes. (Env-vs-build discrepancy; likely Finset.le_sup instance inference in the hTimer0 `hle`
proof inside MAClive_to_consensus_or_crs.) Until DrainProductive.olean builds, OptimalWindows.lean
(which now imports it for the hRank12-eliminated PEM_expectedParallelTime_optimal) cannot verify.

## TASK
1. FIX the typeclass-stuck at DrainProductive.lean:255 (the `hle : (if … then (D μ).1.timer else 0) ≤
   maxMedianTimer D` proof). Make it robust — e.g. provide the function explicitly:
   `Finset.le_sup (f := fun μ => if (D μ).1.rank.val + 1 = ceilHalf n then (D μ).1.timer else 0)
   (Finset.mem_univ μ)` after `unfold maxMedianTimer`, or use the `Finset.le_sup_of_le (Finset.mem_univ μ)
   (by simp [maxMedianTimer, hμ])` pattern that the same file's hNonincrease uses successfully. Check for
   any OTHER env-vs-build issues by actually running `lake build` (not just `lake env lean`).
2. BUILD the olean: `lake build SSExactMajority.UpperBound.Time.DrainProductive` — must SUCCEED
   (no timeout/kill; it is slow due to maxHeartbeats 16M on timer_drain_to_zero_productive — let it run).
3. VERIFY the assembly: `lake build SSExactMajority.UpperBound.Time.OptimalWindows` (build the olean,
   not just lake env lean) — confirm 0 sorry/axiom, hRank12 gone from PEM_expectedParallelTime_optimal,
   hypotheses [12]-only (h12ranking, h12resetDuration, h12rank, h12reRank).
4. If both build clean, commit [Xiang-proxy] + push. If a real proof gap surfaces (not just elaboration),
   report it precisely.

## HARD RULES (automode, no effort cap)
- NO sorry/axiom/native_decide. The fix is elaboration-robustness, not weakening. Verify with `lake build`
  (the olean), NOT just `lake env lean`. Report precisely (built clean / proof gap at X).
- Append to HANDOFF/outbox/codex-fixbuild-report.md.
