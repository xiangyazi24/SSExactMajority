# Codex task (uisai1) cxg CONTINUATION: finish generic-trank → genuine O(n)

GREEN LIGHT from your own probe: NO window has a semantic trank=Rmax dependency. Every blocker is just
that helper/support lemmas are stated with PEMProtocolCoupled. So this is a mechanical (large) port. Drive
it all the way to the instantiated O(n) theorem. NO effort cap. Single coherent line, you own GenericTrank.lean.

## Goal (terminal condition)
A theorem, FULL `lake build`-verified, 0 sorry/axiom/admit/native_decide, stating O(n) EXPECTED parallel
time for the PAPER protocol PEMProtocol n trank Rmax with trank=1, T_timer=35 — i.e. instantiate the
generic keystone at trank=1 so OW_globalWindow = O(n^2) sequential / E[parallel] = O(n).

## Order of work (each layer in GenericTrank.lean, lake build the olean after each)
1. Port the coupled HELPER layers to generic PEMProtocol n trank Rmax (cap K, side cond 7(trank+4)≤K where needed):
   - srank/timer-failure support: srankMedianMaxEvent / hit-count stack behind
     PEM_srank_or_timer_failure_prob_le_quarter_short35.
   - decision-timing support: live_exit_ProbHitWithin_le_bad + its support invariant (from DecisionTiming.lean).
   - step helpers: step_rank_preserved_of_InSswap, step_timer_le_of_InSswap, crs_of_InSswap_break_with_MedC.
   The n≤Rmax conditions are genuine reset-count assumptions — KEEP them as hypotheses (they are O(1)-compatible
   constraints on n, not trank=Rmax). If ANY step genuinely needs trank=Rmax, STOP and report exactly which.
2. Port the windows on top: PEM_srank_or_timer_failure_prob_le_quarter_short35, decision_before_timer_zero,
   timer_ge_two_descent_step, PEM_expected_timer_drain_poly, timer_drain_to_zero_productive,
   MAClive_to_consensus_or_crs, swap_live_to_cons_or_crs_or_break — all over PEMProtocol n trank Rmax.
3. Port the keystones over the generic protocol: OW_rankBound, OW_consensusBound, and a generic
   PEM_expectedParallelTime_optimal_generic. The [12] citation hypotheses (h12ranking/h12rank/h12reRank,
   CRSResetDuration12) get RESTATED over PEMProtocol n trank Rmax — keep them as hypotheses (scope A: we cite
   [12], do not prove it). The constant trank assumption enters as trank=O(1) (concretely trank=1).
4. Instantiate trank=1, T_timer=35 (note 7*(1+4)=35 exactly = the MedianTimerAtLeast 35 floor; OW_consensusBound
   needs exactly this). Produce PEM_expectedParallelTime_optimal_On : E[parallel] ≤ O(n).
5. Convergence/citation: keep every convergence/citation assumption explicitly about PEMProtocol n trank Rmax
   (or supply BurmanConvergence trank Rmax ... as a hypothesis). Do NOT pull in the coupled (trank=Rmax)
   Burman concrete proof into the O(n) theorem.

## HARD RULES
- One writer, one file: GenericTrank.lean only. Do NOT touch Time.lean / OptimalWindows.lean / Audit.lean /
  the root SSExactMajority.lean. Import what you need from them.
- Verify EACH layer via `lake build SSExactMajority.UpperBound.Time.GenericTrank` (the olean), NOT just lake env lean.
- Do NOT break b0bee4b (the O(n log n) build). Run full `lake build` only at the very end, after all layers land.
- NO sorry/axiom/admit/native_decide anywhere. Report precisely to HANDOFF/outbox/codex-generic-report.md after
  each major layer (helpers done / windows done / keystones done / instantiated O(n) build-verified).
- Commit after each layer that lake-builds clean: `git commit` with [Xiang-proxy] tag describing the layer.
