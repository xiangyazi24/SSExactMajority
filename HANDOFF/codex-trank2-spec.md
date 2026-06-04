# Codex task (uisai1): COMPLETE the trank=O(1) tightening → O(n) expected (build-verified)

The optimal-bound structure is DONE+build-verified (c416d2d, full lake build 2606 jobs, [12]-only,
0 sorry/axiom). The trank tightening is IN PROGRESS — there are UNCOMMITTED edits in
SSExactMajority/UpperBound/Time/OptimalWindows.lean generalizing Rmax→C_rank in OW_globalWindow /
OW_rankBound (h12ranking ≤ C_rank·n² instead of Rmax·n²). COMPLETE it to E[parallel] ≤ O(n).

## Steps (cxtr's scope; build on the uncommitted C_rank start)
1. Finish the C_rank generalization: OW_rankBound / h12ranking ≤ C_rank·n² (C_rank an explicit O(1)
   constant = [12]'s true ranking constant), threaded through OW_globalWindow + PEM_expectedParallelTime_optimal.
2. Generalize the median-timer bound from 7(Rmax+4) to a parameter T_timer (= 7(trank+4), O(1) with
   trank=O(1)): generalize IsTimerBoundedConfig usage + timer_drain_to_zero_productive (→ T_timer·n(n-1))
   + MAClive_to_consensus_or_crs (→ T_timer·n(n-1)+n(n-1)) + swap_live_to_cons_or_crs_or_break +
   OW_consensusBound. If these are baked to PEMProtocolCoupled (trank=Rmax), generalize to
   PEMProtocol n trank Rmax with trank=O(1) — or, if the windows are uniform in the timer bound, just
   parameterize the bound.
3. With C_rank=O(1), T_timer=O(1), and the cited [12] T_reset/T_rank/T_rerank = O(n²) seq, the final
   OW_globalWindow = O(n²) seq ⟹ E[parallel] = OW_globalWindow·16/n = O(n).

## CRITICAL
- Verify via FULL `lake build` (the olean), NOT just lake env lean (env≠build bit us — DrainProductive
  had a build-only typeclass-stuck that lake env lean missed). Specifically `lake build
  SSExactMajority.UpperBound.Time.OptimalWindows` AND `lake build` (full) must succeed.
- Keep [12]-only hypotheses, 0 sorry/axiom. If a window genuinely can't be made trank-uniform without a
  big structural re-param, report the precise scope rather than half-doing it.
- Commit [Xiang-proxy] + push when the full build is clean. Append to HANDOFF/outbox/codex-trank2-report.md.
