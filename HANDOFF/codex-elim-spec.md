# Codex task (uisai1): ELIMINATE hRank12 from OW_consensusBound using decision_before_timer_zero

decision_before_timer_zero is now PROVEN (DecisionTiming.lean): InSswap ∧ MedianTimerAtLeast 35 →
ProbHitWithin DecisionProductiveTarget (decisionWindow n) ≥ 1/4. This IS the productive isolation
hRank12 was assuming. Use it to RESTRUCTURE OW_consensusBound so hRank12 is ELIMINATED.

## Check DecisionProductiveTarget's exact def first (DecisionTiming.lean) — it should be
(InSswap ∧ MAC ∧ timer≥1) ∨ IsConsensusConfig ∨ CorrectResetSeed  (the "MAC-live ∨ cons ∨ CRS").

## New OW_consensusBound renewal (cite ONLY [12])
window_mul_inv; from any bounded non-consensus C:
1. If InSswap ∧ timer≥35: decision_before_timer_zero → DecisionProductiveTarget ≥1/4 [PROVEN].
   - cons → done.
   - CRS → CRS_to_silence_faithful (h12reset+h12rank) → OW_silenceEndpoint → consensus [faithful].
   - MAC-live (InSswap∧MAC∧timer≥1): drain median timer to 0 (staying InSswap∧MAC), then
     PEM_expected_reset_trigger_v2 → cons∨CRS [PROVEN] → CRS_to_silence → consensus. (For the drain,
     reuse the maxMedianTimer descent / step_timer machinery; if a clean "drain to timer=0 staying MAC"
     E[T] window is needed, build it — it is a deterministic-ish timer descent.)
2. If InSswap ∧ 1≤timer<35: bridge to timer≥35? NO — timer only decreases. So the timer≥35 start must
   come from the RANKING endpoint (OW_rankBound's goal is MedianTimerAtLeast 35). So OW_consensusBound's
   entry is timer≥35 (fresh from ranking). Adjust OW_consensusBound's hypothesis to MedianTimerAtLeast 35
   (matching OW_rankBound's output) instead of ≥1, so decision_before_timer_zero applies directly.
3. exit/¬live or timer drained → h12reRank ([12] re-rank restores InSrank → InSswap with fresh timer≥35).
Compose → ProbHitWithin(consensus) ≥ const → window_mul_inv. Hypotheses: {h12reset, h12rank, h12reRank}
(all [12]). hRank12 GONE.

## FIRST sub-goal
Restructure OW_consensusBound to entry MedianTimerAtLeast 35 (matching OW_rankBound) and use
decision_before_timer_zero for the productive isolation, eliminating hRank12. The MAC-live→cons∨CRS
sub-chain (drain + reset_trigger_v2) is the main new work. If the drain-to-timer-0-staying-MAC genuinely
blocks, report it. Update PEM_expectedParallelTime_optimal hypotheses accordingly (drop hRank12).

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide (h12reset/h12rank/h12reRank/h12ranking = [12] OK; hRank12 ELIMINATED).
  Grind or precise obstruction to HANDOFF/outbox/codex-elim-report.md. Edit OptimalWindows.lean /
  DecisionTiming.lean. Self-verify lake env lean. NEVER lake build. Report final hypothesis list.
