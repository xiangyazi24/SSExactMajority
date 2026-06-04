# Codex task (uisai1): ASSEMBLE OW_consensusBound under (A) — renewal + silence link

The integrating step. KEY UNBLOCK: the consensus-isolation cxcons flagged is RESOLVED by an EXISTING
lemma: `isConsensusConfig_of_InSswap_phiCount_zero` (BurmanConvergenceFinal:3443) — InSswap ∧
phiCount=0 ⟹ IsConsensusConfig. So reaching InSswap with phiCount=0 IS consensus.

## Renewal structure for OW_consensusBound (target: explicit poly E[T to consensus])
Prove via `expectedHittingTime_le_window_mul_inv` (E[T]≤K·p⁻¹), p=const, from InSswap+timer+bounded:
- swap window `swap_live_to_cons_or_crs_or_break`: ProbHitWithin(cons ∨ CorrectResetSeed ∨ exit) ≥ 1/4.
- cons branch: done. CRS branch (CorrectResetSeed = correct answer seeded): the correct opinion
  epidemically drains phiCount→0 (use EpidemicBound `epidemic_phi_pair_mass`/the descent — supply its
  region from the CRS/reset invariant), then re-rank to InSswap (CITE [12] ranking time as hypothesis
  hRank12), then `isConsensusConfig_of_InSswap_phiCount_zero` ⟹ consensus. exit branch: re-rank (hRank12)
  back to InSswap+timer, retry.
- So from InSswap+timer, within K=O(poly) steps reach consensus w.p. ≥ const (the 1/4 swap × the
  CRS→consensus path which is deterministic-ish once correct-seeded). window_mul_inv ⟹ E[T] ≤ K/const.

## Cited hypotheses (scope A — state as explicit hypotheses, NOT sorry/axiom)
- hRank12 : ∀ C (dormant/CRS/exit, bounded), E[T to (InSswap ∧ phiCount=0) ∨ consensus ∨ <exit>] ≤ poly
  (this packages [12]'s Optimal-Silent-SSR ranking time + the epidemic; supply the epidemic from
  EpidemicBound and the ranking as the [12] citation). Choose the cleanest hypothesis form that the
  renewal consumes; document it.

## Available PROVEN/EXISTING (use, don't reprove)
isConsensusConfig_of_InSswap_phiCount_zero (3443), isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero
(DecisionReach:63), swap_live_to_cons_or_crs_or_break, decision_window, EpidemicBound lemmas,
expectedHittingTime_le_window_mul_inv, ProbHitWithin_ge_half_of_expectedHittingTime_le,
probReached_add_add_add_add_ge_mul5, PEM_CRS_to_allR_or_break.

## FIRST sub-goal
Prove OW_consensusBound MODULO the single cited hypothesis hRank12 (the [12] ranking+epidemic return).
i.e. close OW_consensusBound's sorry by reducing it to hRank12 + the proven swap window + the silence
link + window_mul_inv. Report the exact hRank12 form you needed. If the renewal still can't isolate the
per-cycle consensus probability even WITH the silence link, report the precise remaining obstruction.

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide (hRank12 = explicit hypothesis OK). Grind or precise obstruction to
  HANDOFF/outbox/codex-assemble-report.md. Edit OptimalWindows.lean (or OptimalWindowsA.lean).
  Self-verify lake env lean (project root). NEVER lake build.
