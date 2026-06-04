# Codex task (uisai1): CLOSE OW_consensusBound — use PEM_expected_reset_trigger_v2 (PROVEN productive window)

cxclose failed because composing decision_window + timer_drain can't isolate the productive branch.
THE FIX: the productive window is ALREADY PROVEN — `PEM_expected_reset_trigger_v2` (PhaseProofs.lean:15):
```
InSswap C ∧ MedianAnswerCorrect C ∧ 0 < wrongAnswerCount C ∧ (median timer = 0)
  → expectedHittingTime P C (fun D => IsConsensusConfig D ∨ CorrectResetSeed D) ≤ n(n-1)
```
This DIRECTLY gives the productive (cons ∨ CRS) E[T] bound, isolated from exit. Use it.

## The close (cite ONLY [12])
window_mul_inv renewal; from any bounded non-consensus C:
1. If InSswap ∧ MAC ∧ timer=0 ∧ wrong>0: PEM_expected_reset_trigger_v2 → cons∨CRS in n(n-1) (Markov:
   prob ≥1/2 in 2n(n-1)) [PROVEN]. If wrong=0 ∧ InSswap: consensus directly via
   isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero [PROVEN].
2. To REACH InSswap∧MAC∧timer=0 from InSswap∧timer: decision_window (→MAC, ≥1/2 PROVEN) + drain the
   median timer to 0 (timer decrements on median-rank-n interactions; E[T to timer=0]=O(timer·n²),
   staying InSswap∧MAC — prove/extract a "drain-to-timer-0 while InSswap∧MAC" window, or reuse
   timer_drain_window refined to land at timer=0; the median timer ≤ 7(trank+4)).
3. CRS → CRS_to_silence_faithful → OW_silenceEndpoint → consensus [faithful, [12]-cited].
4. exit/¬live → h12reRank → live, retry [12].
Compose → ProbHitWithin(consensus) ≥ const in K=poly → window_mul_inv → OW_consensusBound with
hypotheses = {h12reset (CRSResetDuration12), h12rank, h12reRank} (all [12]) + arithmetic. ELIMINATE hRank12.

## FIRST sub-goal
The reach-timer-0 step (InSswap∧MAC∧timer → InSswap∧MAC∧timer=0, E[T]=O(timer·n²) staying MAC), then
chain with PEM_expected_reset_trigger_v2 to get InSswap∧timer → cons∨CRS productive (const prob).
That is the productive window cxclose lacked. Then thread into OW_consensusBound. If draining to timer=0
while staying InSswap∧MAC has an obstruction (e.g. MAC not preserved during drain), report it.

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide (h12reset/h12rank/h12reRank = [12] OK; hRank12 ELIMINATED). Grind or
  precise obstruction to HANDOFF/outbox/codex-close2-report.md. Edit OptimalWindows.lean. Self-verify
  lake env lean. NEVER lake build. Report final OW_consensusBound hypothesis list.
