# Codex task (uisai1): ELIMINATE hRank12 from OW_consensusBound (all pieces now proven)

Codex usage reset. timer_drain_to_zero_productive + MAClive_to_consensus_or_crs are PROVEN by Opus in
DrainProductive.lean (verify: lake env lean SSExactMajority/UpperBound/Time/DrainProductive.lean clean).
ALL pieces to eliminate hRank12 now exist:
- decision_before_timer_zero (DecisionTiming.lean): InSswap ∧ MedianTimerAtLeast 35 →
  ProbHitWithin(DecisionProductiveTarget) ≥ 1/4 in decisionWindow n. DecisionProductiveTarget =
  (InSswap∧MAC∧timer≥1) ∨ cons ∨ CRS.
- MAClive_to_consensus_or_crs (DrainProductive.lean): InSswap∧MAC∧timer≥1 (+bounded) →
  E[T to cons∨CRS] ≤ 7(Rmax+4)·n(n-1) + n(n-1). [Markov → ProbHitWithin ≥1/2 in 2·that]
- CRS_to_silence_faithful (OptimalWindows.lean): CorrectResetSeed → OW_silenceEndpoint (modulo
  h12reset:CRSResetDuration12, h12rank). isConsensusConfig_of_InSswap_phiCount_zero: silence→consensus.
- crs_of_InSswap_break_with_MedC, h12reRank ([12] re-rank exit→live).

## TASK
Restructure OW_consensusBound (entry MedianTimerAtLeast 35, matching OW_rankBound's output) to ELIMINATE
hRank12, via expectedHittingTime_le_window_mul_inv (or _of_invariant): from any bounded non-consensus C,
ProbHitWithin(consensus) ≥ const in K=poly, by:
- live (InSswap∧timer≥35): decision_before_timer_zero → productive; the (InSswap∧MAC∧timer≥1) branch →
  MAClive (Markov) → cons∨CRS; cons→consensus (or wrongAnswerCount=0 silence); CRS→CRS_to_silence_faithful
  →OW_silenceEndpoint→consensus (isConsensusConfig_of_InSswap_phiCount_zero). Compose via probReached_..._ge_mul.
- exit/¬live → h12reRank → live, retry.
Hypotheses must be [12]-ONLY: h12reset (CRSResetDuration12), h12rank, h12reRank. DROP hRank12.
Update PEM_expectedParallelTime_optimal (drop hRank12, keep h12ranking + the three [12] hyps).

## FIRST sub-goal
Compose decision_before_timer_zero + MAClive (Markov) into: InSswap∧timer≥35 → ProbHitWithin(cons∨CRS)
≥ const in poly. Then cons∨CRS→consensus via CRS_to_silence. Then window_mul_inv. If a composition
primitive is missing, report exactly which.

## HARD RULES (automode, no effort cap)
- NO sorry/axiom/native_decide (h12* = [12] citations OK; hRank12 ELIMINATED). Grind or precise
  obstruction to HANDOFF/outbox/codex-elim2-report.md. Edit OptimalWindows.lean (+ helper if needed).
  Self-verify lake env lean (project root). NEVER lake build. Report final hypothesis list.
