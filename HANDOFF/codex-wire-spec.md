# Codex task (uisai1): wire EpidemicMechanics into CRS_to_silence (discharge epidemic hyps)

Make CRS_to_silence_of_rank12 FAITHFUL: discharge its epidemic hypotheses (hInvStep/hNonincrease/hGood/
hAnsInv) using the PROVEN EpidemicMechanics theorems, leaving ONLY [12] reset+rank durations cited.

## Available PROVEN (EpidemicMechanics.lean, committed cf54fd1)
- epidemicRegion_answerInv : EpidemicRegion m C → EpidemicAnswerInv m C
- epidemicRegion_phiCount_nonincrease (carries: endpoints stay Resetting through the step)
- epidemicRegion_step_closed
- epidemicRegion_phiPair_descent (guard: hr₀_role, hr₁_role — the rankDeltaOSSR output keeps both
  endpoints Resetting)

## The guard threading (the integration)
The proven mechanics carry a "endpoints stay Resetting through this step" guard (a Resetting rc=0 agent
can wake via processAgent→resetOSSR). Under (A) this guard is supplied by a CITED [12] reset-duration
invariant: while in the reset window (rc not yet drained / [12] Lemma 1-2), agents stay Resetting.
State that as a cited hypothesis:
```
(hStayResetting : ∀ C, <reset-window/EpidemicRegion> C → ∀ p ∈ phiNonPhiPairs C,
    <rankDeltaOSSR output keeps p.1,p.2 Resetting>)   -- [12] Lemma 1-2 form
```
Then the guarded epidemicRegion_phiPair_descent / _phiCount_nonincrease discharge UNGUARDED versions
over the reset window, which discharge CRS_to_silence's hInvStep/hNonincrease/hGood with Inv:=EpidemicRegion m.

## Target
```
theorem CRS_to_silence_faithful  -- only [12] reset+rank cited, epidemic PROVEN
  (h12resetDuration : <CITED [12] L1-2: stay-Resetting window of length T_reset>)
  (h12rank : <CITED [12] L3: EpidemicPhiGoal → reach InSswap+phiCount=0 in T_rank w.p. rankProb>) :
  ∀ C, IsTimerBoundedConfig _ C → CorrectResetSeed C →
    (const : ENNReal) ≤ ProbHitWithin P hn2 C OW_silenceEndpoint (T_reset + T_rank)
```
by instantiating CRS_to_silence_of_rank12 with Inv:=EpidemicRegion (majorityAnswer C), discharging
hAnsInv/hInvStep/hNonincrease/hGood from EpidemicMechanics (+ hStayResetting for the guard), and
hEpidemicSum from phiNonPhiPairs_card=2k(n-k) coupon sum. hResetInv (CRS → EpidemicRegion(majorityAnswer))
proven from CorrectResetSeed structure.

## FIRST sub-goal
hResetInv (CorrectResetSeed C → EpidemicRegion (majorityAnswer C) C) + discharge hNonincrease/hGood via
the guarded EpidemicMechanics under h12resetDuration. Report any guard that can't be supplied by the
cited [12] reset-duration (i.e. a genuinely un-citable protocol gap).

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide (h12resetDuration, h12rank = [12] citations OK). Grind or precise
  obstruction to HANDOFF/outbox/codex-wire-report.md. Edit OptimalWindows.lean / EpidemicMechanics.lean.
  Self-verify lake env lean. NEVER lake build.
