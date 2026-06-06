# Make epidemicFast cleanly faithful (independent ChatGPT audit main blocker)

## Why
Independent audit found StandardEpidemicFastHypothesisPEM is over-strong: as stated it asserts the FULL PEM
(which can wake agents) reaches EpidemicPhiGoal w.p. pE from EpidemicRegion. But the standard one-rumor
epidemic argument only holds while the all-Resetting mechanics stay active (no wake). The faithful citation
is: the epidemic succeeds UNLESS a wake interrupts it. Target should be EpidemicPhiGoal OR SomeAgentAwake.
The bridge already subtracts the no-wake tail, so the final conclusion is UNCHANGED.

## Verified math (the implication is identical, so the bridge re-derives trivially)
Old: EpidemicPhiGoal m D -> (Target D OR Bad D), Target = EpidemicPhiGoal AND AllAgentsResetting, Bad = SomeAgentAwake.
New: (EpidemicPhiGoal m D OR SomeAgentAwake D) -> (Target D OR Bad D). Proof: if SomeAgentAwake -> Bad (Or.inr);
if EpidemicPhiGoal -> by_cases on Bad: Bad -> Or.inr; not Bad -> Or.inl <hGoal, not_someAgentAwake...>. Same shape,
just one extra top-level rcases on the OR. Bridge conclusion pE/2 <= ProbHitWithin Target K is unchanged.

## Edits (files you authored: AnswerEpidemicBridge.lean + OptimalWindowsFaithful.lean — both yours)
1. AnswerEpidemicBridge.lean: change StandardEpidemicFastHypothesisPEM target from
   (EpidemicPhiGoal m) to (fun D => EpidemicPhiGoal m D OR SomeAgentAwake D).
2. Re-derive answer_epidemic_bridge_from_fresh_resetting: hEpidemic now bounds
   ProbHitWithin (fun D => EpidemicPhiGoal m D OR SomeAgentAwake D) K; update hGoalToTargetOrBad/hGoalLeOr to
   start from that disjunction (add the top-level rcases). The rest (subtract hBad via
   ProbHitWithin_left_ge_of_or_ge_add_and_right_le) is unchanged; conclusion identical.
3. (ChatGPT minor point 3) Strengthen CRSReset12Faithful.freshSeedReach precondition from
   IsTimerBoundedConfig (7*(1+4)) C to WellFormed 1 Rmax Emax Dmax C. Then in faithful_reset_to_phiGoal /
   crsReset12Faithful_to_generic pass WellFormed.1 (= IsTimerBoundedConfig 35) where the bridge needs the
   timer bound. Keep all downstream (PEM_expectedParallelTime_On_faithful) building.
4. Thread the new epidemicFast type through faithful_reset_to_phiGoal, crsReset12Faithful_to_generic,
   PEM_expectedParallelTime_On_faithful (only the hypothesis TYPE changes; conclusions unchanged).

## Documentation (no proof, just a precise comment) for the [12] fresh-seed citation
Add a doc-comment on CRSReset12Faithful explaining WHY the fresh target (all agents role=Resetting,
delaytimer=Dmax simultaneously) is what [12]+PEM reset mechanics deliver: processAgent sets delaytimer:=Dmax
on reset (oldRc>0 branch) and recruitment assigns delaytimer:=Dmax to newly-Resetting agents, so when the
reset epidemic completes every agent has been freshly reset to Dmax. State plainly this simultaneous-fresh
event is the cited [12] stopping time.

## HARD RULES
Iterate lake build SSExactMajority.UpperBound.Time.OptimalWindowsFaithful (imports the bridge) until clean.
No sorry/axiom/native_decide. The cited hypotheses stay labeled hypotheses. Commit clean with [Xiang-proxy].
Report updated theorem names + confirmation that PEM_expectedParallelTime_On_faithful conclusion is unchanged,
to HANDOFF/outbox/cxfix-report.md.
