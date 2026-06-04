# Codex task (uisai1): generic-trank re-parameterization (steps 1-2) → toward genuine O(n)

cxti scoped it: to get GENUINE O(n) (not O(n log n)), the phase-window stack must be over the GENERIC
protocol PEMProtocol n trank Rmax Emax Dmax (trank a free parameter) with timer cap K (7(trank+4)≤K),
NOT PEMProtocolCoupled (trank=Rmax). The window PROOFS are already "uniform in the timer cap" (cxt2),
so this is mostly mechanical: swap PEMProtocolCoupled→PEMProtocol n trank Rmax, replace the 7(Rmax+4)
timer cap by a parameter K with side-condition 7(trank+4)≤K, re-verify.

## THIS task: steps 1-2 (foundation). New file SSExactMajority/UpperBound/Time/GenericTrank.lean
1. `generic_timer_preservation`: PEMProtocol n trank Rmax Emax Dmax hn step preserves
   IsTimerBoundedConfig K, given 7*(trank+4) ≤ K. (Generalize PEMProtocolCoupled_preserves_timer_bounded.)
2. Re-state + prove (over PEMProtocol n trank Rmax, cap K, 7(trank+4)≤K) the phase windows that are
   currently PEMProtocolCoupled-specific. Start with the ones whose proofs are timer-cap-uniform:
   decision_window, PEM_srank_or_timer_failure_prob_le_quarter_short35, decision_before_timer_zero,
   timer_ge_two_descent_step, PEM_expected_timer_drain_poly, timer_drain_to_zero_productive,
   MAClive_to_consensus_or_crs, swap_live_to_cons_or_crs_or_break.
   For each: if the existing proof only uses the timer CAP (not trank=Rmax specifically), the
   re-statement is mechanical (change protocol instance + cap parameter). If a proof genuinely needs
   trank=Rmax (e.g. uses an Rmax-specific lemma), REPORT which and why.

## METHOD
- Work in the NEW file (GenericTrank.lean) so you don't break the build-verified b0bee4b. Import what
  you need. Where a window's proof is literally the same modulo the protocol instance + cap, restate it
  and prove by reduction to / adapting the existing PEMProtocolCoupled proof if possible.
- Verify EACH lemma via `lake build` of GenericTrank (the olean), not just lake env lean.

## FIRST sub-goal + report
Do step 1 (generic_timer_preservation) + the FIRST window (decision_window generic). Report whether the
window proofs are cleanly timer-cap-uniform (so the rest is mechanical) or hit trank=Rmax dependencies
(report which). This determines the realistic scope of the full O(n).

## HARD RULES (automode, no effort cap)
- NO sorry/axiom/native_decide. Verify via lake build. Don't break b0bee4b. Report precisely.
  Append to HANDOFF/outbox/codex-generic-report.md.
