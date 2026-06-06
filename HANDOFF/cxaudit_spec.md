# Independent adversarial audit — you did NOT write this code. Try to break it.

A formalization in this repo claims to prove O(n) expected parallel time for a self-stabilizing exact-majority
population protocol (Kanaya et al.). The keystone is SSEM.PEM_expectedParallelTime_On_faithful in
SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean. Your job is to find any way this proves LESS than
it claims, or is unsound. Be adversarial. Do not assume it is correct.

## Specifically hunt for (report each with file:line + concrete reasoning)
1. HIDDEN AXIOMS/SORRY: run, for the keystone and its key deps, fresh #print axioms from rebuilt oleans:
   create a scratch file importing OptimalWindowsFaithful and `#print axioms PEM_expectedParallelTime_On_faithful`,
   `#print axioms answer_epidemic_bridge_from_fresh_resetting`, `#print axioms drain_probHitWithin_le_choose_unconditional`,
   `#print axioms faithful_reset_to_phiGoal`, `#print axioms crsReset12Faithful_to_generic`. Anything beyond
   {propext, Classical.choice, Quot.sound} (e.g. sorryAx, ofReduceBool, trustCompiler) is a finding. Build with
   /data/home/xhuan5/.elan/bin/elan run leanprover/lean4:v4.30.0 lake env lean <scratch>.
2. VACUITY: is the hypothesis bundle of PEM_expectedParallelTime_On_faithful JOINTLY SATISFIABLE for some
   actual n>=4? In particular do hTail (drainNoWakeTail n K_bridge Dmax <= pE/2), epidemicFast (target now
   EpidemicPhiGoal OR SomeAgentAwake at window K_bridge), and hBridgeWindow (K_bridge <= C_bridge*n*n) admit a
   common K_bridge? Or could two premises be mutually contradictory, making the theorem vacuously true?
3. CIRCULARITY: does any premise (h12ranking, h12rank, h12reRank, CRSReset12Faithful.freshSeedReach, epidemicFast)
   already assert the final consensus/expected-time conclusion, or something equivalent to it?
4. DEGENERATE DEFINITIONS: read the actual defs and check none is trivialized:
   - Probability.expectedParallelTimeToConsensus, Probability.ProbHitWithin, Probability.expectedHittingTime
   - EpidemicPhiGoal, SomeAgentAwake, AllAgentsResetting, EpidemicRegion, IsConsensusConfig, CorrectResetSeed
   - drainNoWakeTail (= n * choose K Dmax * (2/n)^Dmax ?), OW_globalWindow, PEM_trank1_timer
   - PEMProtocol n 1 Rmax Emax Dmax — is this the REAL protocol transition, or a coupled/trivial variant?
   Flag any definition that makes the bound trivially true (e.g. a goal predicate that always holds, a window
   that is infinite, a protocol that immediately consensus-es).
5. THE O(n) CLAIM: does the conclusion bound (OW_globalWindow ... * ((p_reset*(pE/2))*128inv)inv / n) actually
   represent O(n) parallel time? Is OW_globalWindow genuinely O(n^2) (check OW_globalWindow_trank1_quadratic) and
   the probability factor a positive constant? Or is there a hidden n-dependence in the "constants"?

## Output
Write findings to HANDOFF/outbox/cxaudit-report.md: a numbered list, each item = {severity: blocker/concern/ok,
file:line, what, why}. End with a one-line verdict: SOUND / SOUND-BUT-CONDITIONAL / UNSOUND, and if conditional,
the exact premises it is conditional on. Do NOT edit any .lean file — this is read-only analysis. Do NOT commit.
