# Codex task (uisai1): CLOSE OW_consensusBound faithfully — isolate productive branch via proven windows

cxfin built h12reset/h12rank/h12reRank ([12] citations) but left hRank12 because it needed the
"productive-exit" fact: from live-swap, reach {cons ∨ CRS} (NOT the union with exit) w.p. ≥ const.
KEY: that IS derivable from the PROVEN windows — compose them to isolate the productive branch.

## The productive isolation (from PROVEN windows, no new hypothesis)
- `decision_window` (PROVEN): InSswap ∧ timer ∧ ¬MAC → (InSswap ∧ MAC) ∨ ¬live, w.p. ≥ 1/2.
- `timer_drain_window` (PROVEN): InSswap ∧ MAC ∧ timer → cons ∨ CorrectResetSeed ∨ ¬live, w.p. ≥ 1/2.
So from live-swap: w.p. ≥ const reach (cons ∨ CRS), with the ¬live(exit) branch separated. Compose via
probReached_add_..._ge_mul / ProbHitWithin composition. This gives the productive-exit fact cxfin lacked.

## Final OW_consensusBound (cite ONLY [12])
Restructure to take h12reset (CRSResetDuration12), h12rank, h12reRank ([12] re-rank for exit) — NO hRank12.
Renewal via window_mul_inv: from any bounded non-consensus C:
- live: decision_window + timer_drain_window → cons ∨ CRS (const) [PROVEN]; CRS → CRS_to_silence_faithful
  → OW_silenceEndpoint → consensus (isConsensusConfig_of_InSswap_phiCount_zero) [PROVEN + [12] cited];
  exit-from-these → h12reRank back to live [12].
- ¬live: h12reRank → live, then above.
Product of constants → ProbHitWithin(consensus) ≥ const in K=poly → window_mul_inv → E[T] ≤ poly.
Result: OW_consensusBound with hypotheses = {h12reset, h12rank, h12reRank} (all [12]) + arithmetic.

## FIRST sub-goal
The productive isolation lemma: from InSswap+timer+bounded, ProbHitWithin(IsConsensusConfig ∨ CorrectResetSeed)
≥ const in (decision+drain window), composing decision_window + timer_drain_window (PROVEN, no new hyp).
Then thread into OW_consensusBound replacing hRank12. Report final hypothesis list (must be [12]-only).

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide (h12reset/h12rank/h12reRank = [12] OK; hRank12 must be ELIMINATED — replaced
  by the proven windows + [12] re-rank). Grind or precise obstruction to HANDOFF/outbox/codex-close-report.md.
  Edit OptimalWindows.lean. Self-verify lake env lean. NEVER lake build.
