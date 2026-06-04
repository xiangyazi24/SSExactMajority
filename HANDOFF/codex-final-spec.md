# Codex task (uisai1): OW_consensusBound FAITHFUL — replace hRank12 with [12]-only citations

Make OW_consensusBound cite ONLY [12] reset+rank (the over-bundled hRank12 → faithful pieces).

## Replace the hRank12 hypothesis with:
- `h12reset : CRSResetDuration12 ... T_reset` (the [12] reset-duration contract; CRS_to_silence_faithful
  consumes it).
- `h12rank : ∀ m D, EpidemicPhiGoal m D → rankProb ≤ ProbHitWithin ... (OW_rankedEpidemicEndpoint m) T_rank`
  ([12] L3, CRS branch).
- `h12reRank : ∀ C, IsTimerBoundedConfig _ C → ¬(InSswap C ∧ MedianTimerAtLeast 1 C) →
    (1/2 : ENNReal) ≤ ProbHitWithin ... C (fun D => InSswap D ∧ MedianTimerAtLeast 1 D) T_rerank`
  ([12] L3 re-rank: from a non-live/exit state, return to a live swap — this is [12]'s ranking restoring
  the live-swap region).

## Proof
Derive the old hRank12 (restart-branch → OW_silenceEndpoint, prob 1/2) from:
- CorrectResetSeed branch: `CRS_to_silence_faithful h12reset h12rank` directly gives CRS → OW_silenceEndpoint
  w.p. 1/2 in T_reset+T_rank.
- exit branch (¬live): `h12reRank` returns to live-swap; from live-swap, the swap window
  (swap_live_to_cons_or_crs_or_break) re-enters the cycle. For the window_mul_inv cycle this exit branch
  is handled by the OUTER renewal re-applying p from the (now live) state — OR fold the re-rank into the
  cycle window. Choose the structure that lets you discharge OW_consensusBound's old hRank12 (or restructure
  OW_consensusBound to consume the three [12] hypotheses directly).
Then OW_consensusBound's existing renewal (window_mul_inv, swap 1/4 × 1/2 → 1/8) closes with ONLY [12]
reset+rank cited.

## FIRST sub-goal
Discharge the CorrectResetSeed half of hRank12 via CRS_to_silence_faithful (immediate). Then handle the
exit half via h12reRank + the swap window. If the exit branch genuinely cannot be made to reach
OW_silenceEndpoint within the window (needs the outer renewal), restructure OW_consensusBound to take the
three [12] hypotheses and prove it via window_mul_inv with the exit branch as a re-rank-then-retry.
Report the final hypothesis list (must be ONLY [12] citations).

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide (h12reset/h12rank/h12reRank = [12] citations OK). Grind or precise
  obstruction to HANDOFF/outbox/codex-final-report.md. Edit OptimalWindows.lean. Self-verify lake env
  lean. NEVER lake build. Report the final OW_consensusBound hypothesis list.
