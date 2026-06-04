# Codex task (uisai1): discharge hRank12 — cite ONLY [12] reset+rank, PROVE the rest

OW_consensusBound is proven modulo hRank12, but hRank12 over-bundles: it ASSUMES restart-branch →
OW_silenceEndpoint (InSswap ∧ ResAns(majority) ∧ phiCount=0) w.p.1/2, which folds in Kanaya's epidemic
+ correctness. Under (A) only [12]'s reset+rank are citable; the epidemic/silence/decision are Kanaya's
and must be PROVEN. Refactor hRank12 into a FAITHFUL form: cited [12] durations + proven Kanaya pieces.

## Goal: replace hRank12 by hRank12_faithful that cites ONLY [12]
Decompose the CorrectResetSeed branch (the productive one):
  CRS C  --[12 reset duration: stays in reset/epidemic mode ≥ T_reset]-->  epidemic drains phiCount→0
  (EpidemicBound, supply its region from the [12] reset invariant)  --[12 rank: reach InSswap]-->
  InSswap ∧ phiCount=0 ∧ ResAns(majority)  =OW_silenceEndpoint  --isConsensusConfig_of_InSswap_phiCount_zero-->  consensus.
So:
```
theorem CRS_to_silence_of_rank12
  (h12reset : <CITED: from CRS, stays reset-mode ≥ T_reset / reaches dormant — [12] Lemma 1-2 form>)
  (h12rank  : <CITED: from dormant+phiCount=0+correct, reach InSswap+phiCount=0 in T_rank w.p. ≥1/2 — [12] Lemma 3>) :
  ∀ C, IsTimerBoundedConfig _ C → CorrectResetSeed C →
    (1/2 : ENNReal) ≤ ProbHitWithin P hn2 C OW_silenceEndpoint (T_reset + T_rank)
```
where the EPIDEMIC (phiCount→0) and the answer-correctness preservation (ResAns through reset+rank)
are PROVEN here (from EpidemicBound + answer-preservation lemmas: propagateReset_answer_preserved,
transitionPEM_prePhase4_propagate_answer, the ResAns-preservation in BurmanConvergenceFinal), NOT
assumed. The exit branch (¬live) is handled by the OUTER renewal (re-rank via h12rank back to live, retry)
— it does NOT need to reach silence directly.

## FIRST sub-goal
Prove CRS_to_silence_of_rank12: from CorrectResetSeed, compose the PROVEN epidemic (phiCount→0) +
answer-preservation + the silence link, citing ONLY [12]'s reset+rank durations (h12reset, h12rank).
The key proof content: (1) under CRS, the epidemic region holds long enough (from h12reset) to drain
phiCount→0 [use EpidemicBound]; (2) ranking preserves phiCount=0 ∧ ResAns(majority) [answer-preservation];
(3) silence link. If answer-preservation across ranking genuinely fails (ranking re-introduces phi or
wrong answers), report the EXACT obstruction.

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide (h12reset, h12rank = explicit [12] citations OK; epidemic/correctness
  must be PROVEN, not assumed). Grind or precise obstruction to HANDOFF/outbox/codex-discharge-report.md.
  Edit OptimalWindows.lean / a helper file. Self-verify lake env lean (project root). NEVER lake build.
