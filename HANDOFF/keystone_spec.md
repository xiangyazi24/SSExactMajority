# Faithful reset->silence composition at trank=1, wiring the proven answer-epidemic bridge

## Why
OptimalWindows.lean has CRSResetCompletion12.resetReach (line ~499) whose ProbHitWithin TARGET is
EpidemicPhiGoal directly. Its own docstring admits "the reset-counter dormancy race is internal to this
cited window rather than an exposed invariant" — i.e. it OVER-CITES [12]: it asks [12] to deliver the
PEM-specific answer-epidemic completion. We now have that completion PROVEN as
answer_epidemic_bridge_from_fresh_resetting (AnswerEpidemicBridge.lean), so we replace the over-citation
with a FAITHFUL weaker citation + our proof.

The counterexample bare_epidemicRegion_can_wake_counterexample (OptimalWindows.lean ~line 431) shows a bare
EpidemicRegion target is insufficient (a drained all-Resetting state wakes). Our bridge requires hFresh
(role=Resetting AND delaytimer=Dmax for ALL agents) precisely to rule that out. The reset mechanism literally
re-seeds delaytimer:=Dmax, so a FRESH reset seed is a faithful [12] deliverable.

## Task (NEW file SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean — you own it)
Work over PEMProtocol n 1 (trank=1, timer=35) — NOT PEMProtocolCoupled. import OptimalWindows and
AnswerEpidemicBridge.

### Step 1 — faithful fresh-reset-seed contract
Define a Prop-structure CRSReset12Faithful (n Rmax Emax Dmax : N) (hn) (p_reset : ENNReal) (C_reset K_reset : N)
with the constant fields (resetProb_pos/le_one, resetConstant_pos, resetWindow_quadratic: K_reset <= C_reset*n*n)
and the faithful reach field:
  freshSeedReach :
    forall (hn2 : 2 <= n) (C : Config (AgentState n) Opinion n),
      IsTimerBoundedConfig (7*(1+4)) C -> CorrectResetSeed C ->
        p_reset <=
          Probability.ProbHitWithin (PEMProtocol n 1 Rmax Emax Dmax hn) hn2 C
            (fun D => EpidemicRegion (majorityAnswer C) D
              AND (forall a : Fin n, (D a).1.role = .Resetting AND (D a).1.delaytimer = Dmax)) K_reset
This is the legitimate [12] citation: the reset+ranking completes to a FRESH reset seed in the epidemic region.
Doc-comment it clearly as the [12]-cited reset-completion (target = fresh epidemic-region reset seed, NOT the
PEM answer-epidemic completion).

### Step 2 — compose with the proven bridge
Prove faithful_reset_to_phiGoal:
  given CRSReset12Faithful (delivering the fresh seed w.p. p_reset within K_reset) and the standard epidemic
  hypothesis epidemicFast (StandardEpidemicFastHypothesisPEM, pE) and the tail hypothesis on K_bridge
  (drainNoWakeTail n K_bridge Dmax <= pE/2) and 0 < Dmax, hDmax: n <= Dmax,
  then from any CorrectResetSeed start C with IsTimerBoundedConfig (7*5) C,
    p_reset * (pE/2) <=
      Probability.ProbHitWithin (PEMProtocol n 1 Rmax Emax Dmax hn) hn2 C
        (fun D => EpidemicPhiGoal (majorityAnswer C) D AND AllAgentsResetting D)
        (K_reset + K_bridge)
Proof: chain freshSeedReach (reaches fresh seed D in EpidemicRegion) with
answer_epidemic_bridge_from_fresh_resetting applied AT the intermediate config (its hFresh = the freshness in
the seed target, its hRegion = the EpidemicRegion in the seed target), via
Probability.ProbHitWithin_add_ge_mul (the same multiply-and-add lemma used by CRS_to_silence_faithful_product).
Mind majorityAnswer: the bridge needs m = majorityAnswer C and EpidemicRegion m at the intermediate config;
the seed target already fixes m = majorityAnswer C, so it threads. If majorityAnswer changes between C and the
intermediate D, state the needed majorityAnswer-stability as an explicit hypothesis (do NOT silently assume).

## HARD RULES
New file is yours; do NOT edit OptimalWindows / AnswerEpidemicBridge / DrainNoWake* (read-only, import them).
Iterate lake build SSExactMajority.UpperBound.Time.OptimalWindowsFaithful until clean. No sorry/axiom/native_decide.
p_reset, pE, the tail bound, majorityAnswer-stability may remain clearly-labeled HYPOTHESES. Commit clean with
[Xiang-proxy]. Report theorem names + file:line to HANDOFF/outbox/cxfix-report.md.
