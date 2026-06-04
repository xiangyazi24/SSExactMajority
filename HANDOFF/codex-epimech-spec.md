# Codex task (uisai1): discharge the epidemic mechanics from transitionPEM (bottoming-out)

CRS_to_silence_of_rank12 ASSUMES the epidemic mechanics (hInvStep/hNonincrease/hGood/hAnsInv) as
hypotheses. PROVE them from the actual transitionPEM, so the chain bottoms out at protocol facts.

## The region (post-clear, spreading)
After Propagate-Reset clears non-median answers to ϕ, the productive region is:
  EpidemicRegion m C := (∀ w, (C w).1.role = .Resetting) ∧ (∀ w, (C w).1.answer = m ∨ (C w).1.answer = .phi)
  ∧ <m = majorityAnswer C is present on ≥1 agent>  (answers in {m, ϕ}, all Resetting).
In this region the epidemic branch (Protocol/Transition.lean:51-54: ϕ-endpoint adopts non-ϕ partner's
answer) is ONE-WAY: non-ϕ (=m) overwrites ϕ; ϕ never overwrites m. So:

## Prove from transitionPEM (the EpidemicBound hypotheses, now as theorems)
1. `epidemicRegion_step_closed`: EpidemicRegion m C → ∀ i j, EpidemicRegion m (C.step P i j) ∨ phiCount=0.
   (All-Resetting closure: in this region no recruit/collision fires — all Resetting → only the
    propagateReset/epidemic branch. Answers stay in {m,ϕ}. NOTE the region-DURATION closure — staying
    all-Resetting — is [12]'s reset Lemma 1-2, may be a remaining cited hyp; but the answer/role
    structure WITHIN reset is protocol-provable.)
2. `epidemicRegion_phiCount_nonincrease`: in EpidemicRegion, phiCount(step) ≤ phiCount (one-way: ϕ→m only).
3. `epidemicRegion_phiPair_descent`: a (ϕ, m) ordered pair step strictly decreases phiCount (ϕ adopts m).
4. `epidemicRegion_answerInv`: EpidemicRegion m C → EpidemicAnswerInv m C (answers in {m,ϕ}).
These discharge hAnsInv/hInvStep(role+answer part)/hNonincrease/hGood for CRS_to_silence_of_rank12.

## Key: unfold transitionPEM in the all-Resetting case
With both endpoints Resetting (or one Resetting), Part 1 (propagateReset) fires, NOT recruit/collision/
error. propagateReset does the answer epidemic (lines 51-54) + rc drain. Show it's one-way on answers.
Reuse propagateReset_answer_preserved (RankDelta:165), transitionPEM_prePhase4_propagate_answer,
phase4_propagate_no_reset_of_eq_answer (BurmanConvergenceFinal).

## FIRST sub-goal
epidemicRegion_phiCount_nonincrease + epidemicRegion_phiPair_descent (the one-way epidemic, items 2-3)
from transitionPEM. These are the core protocol facts. If the all-Resetting region doesn't cleanly
force the epidemic branch (e.g. rc=0 agents wake mid-reset), report the EXACT transition obstruction.

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide. Grind or precise obstruction to HANDOFF/outbox/codex-epimech-report.md.
- New file SSExactMajority/UpperBound/Time/EpidemicMechanics.lean. Self-verify lake env lean. NEVER lake build.
