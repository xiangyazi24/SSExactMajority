# Codex task (uisai1): trank=O(1) protocol instantiation — the REAL O(n) (not O(n log n))

cxt2 generalized the bound to T_timer (committed b0bee4b, build-verified) BUT it is still O(n log n)
for the real protocol: PEM_expectedParallelTime_optimal is over PEMProtocolCoupled (trank=Rmax), whose
median timer is set to 7(trank+4)=7(Rmax+4). hTimerStep (preservation of IsTimerBoundedConfig T_timer)
then forces T_timer ≥ 7(Rmax+4)=O(log n), so OW_globalWindow = O(n log n) parallel. To get the paper's
HEADLINE O(n) EXPECTED, the protocol must run at trank=O(1) (timer 7(O(1)+4)=O(1) ⟹ T_timer=O(1)).

## SCOPE FIRST (investigate + report precisely — this determines feasibility)
1. Is PEMProtocolCoupled hard-wired trank=Rmax, or is the underlying PEMProtocol n trank Rmax Emax Dmax
   parameterized by an independent trank? (Time.lean:43 has PEMProtocol with separate trank.)
2. Are the Kanaya windows (swap_live_to_cons_or_crs_or_break, decision_window, timer_drain_to_zero_
   productive, MAClive_to_consensus_or_crs, decision_before_timer_zero) and the [12] citations
   (h12ranking/h12resetDuration/h12rank/h12reRank) + the convergence (burmanConvergence_concrete,
   P_EM_consensus_reachable) UNIFORM in trank, or do they bake trank=Rmax? cxt2 said the drain/window
   stack is "uniform in the timer cap" — check whether they are uniform in trank too (so trank=O(1)
   instantiates directly) or are PEMProtocolCoupled-specific.
3. The paper: trank is a constant with srank ≤ trank·n, trank=O(1) (srank = [12] silence time = O(n)
   parallel). So a specific O(1) trank works. Identify what constraint trank must satisfy in the Lean
   lemmas (e.g. trank ≥ 35 for the median-timer≥35 entry? trank ≥ some constant for the windows?).

## ATTEMPT (if uniform) OR REPORT SCOPE (if structural)
- If the chain is trank-uniform: instantiate trank = an explicit O(1) constant (satisfying the Lean
  constraints + the paper's srank≤trank·n), apply the T_timer-uniform theorem with T_timer=7(trank+4)=O(1),
  giving E[parallel] = O(n). Discharge hTimerStep / the timer invariants for that instance. Verify via
  FULL lake build. Commit [Xiang-proxy] + push.
- If NOT uniform (windows/convergence baked to trank=Rmax): report the EXACT list of lemmas needing
  re-statement/re-proof for trank=O(1), with a realistic assessment. Do NOT half-do it or fake O(n).

## HARD RULES (automode)
- NO sorry/axiom/native_decide. O(n) must be GENUINE (T_timer=O(1) for the actual instantiated protocol,
  not a free parameter that can't be O(1)). Verify via FULL lake build. Do not break b0bee4b.
  Append to HANDOFF/outbox/codex-trankinst-report.md.
