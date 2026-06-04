# Codex task (uisai1): OW_consensusBound via renewal (Kanaya's composition — scope-independent)

Close OW_consensusBound (OptimalWindows.lean, currently `sorry`) via the renewal assembly. This is
Kanaya's Lemma 9+11 contribution — independent of [12] internals and of the A/B scope decision; the
proof STRUCTURE is regime-independent (constants adapt when we re-parameterize to trank=O(1) later).

## Target (the existing keystone statement)
```
OW_consensusBound : ∀ C, InSswap C → MedianTimerAtLeast 1 C → IsTimerBoundedConfig (7*(Rmax+4)) C →
  expectedHittingTime (PEMProtocolCoupled n Rmax Emax Dmax _) _ C IsConsensusConfig ≤ 10*Rmax*n*n
```
(Adjust the constant if the renewal gives a different explicit poly — keep it explicit, report what.)

## Proof via window_mul_inv (ExpectedTime: expectedHittingTime_le_window_mul_inv, E[T] ≤ K·p⁻¹)
Need: ∀ bounded C (in the reachable region), ¬consensus → p ≤ ProbHitWithin P C IsConsensusConfig K,
with K = poly, p = constant. Build p from the PROVEN pieces:
- swap window `swap_live_to_cons_or_crs_or_break` (OptimalWindows.lean): from InSswap+timer+bounded,
  ProbHitWithin(IsConsensusConfig ∨ CorrectResetSeed ∨ ¬(InSswap∧timer)) ≥ 1/4 in W_swap steps.
- For the renewal, compose: a "cycle" = swap attempt; on the cons branch → done; on CorrectResetSeed
  or exit branch → re-rank back to (InSswap+timer) using `OW_rankBound` (TAKE IT AS GIVEN — it is the
  OTHER keystone; use the theorem OW_rankBound as a hypothesis/lemma), then retry. CorrectResetSeed
  carries the CORRECT answer so it does not regress.
- Use the geometric structure: each cycle reaches consensus w.p. ≥ const (the swap 1/4, with the
  re-rank returning to a live swap within OW_rankBound expected time, converted to a window via
  ProbHitWithin_ge_half_of_expectedHittingTime_le). Compose via probReached_add_..._ge_mul / the
  amplification lemmas to get ProbHitWithin(consensus) ≥ const in K = O(Rmax·n²). Then window_mul_inv.

## Available PROVEN pieces (USE, don't reprove)
swap_live_to_cons_or_crs_or_break, decision_window, timer_drain_window, crs_to_allR_or_break_window
(all OptimalWindows.lean); PEM_CRS_to_allR_or_break, allR_to_consensus (PolynomialBound); OW_rankBound
(as hypothesis — the other keystone); expectedHittingTime_le_window_mul_inv,
ProbHitWithin_ge_half_of_expectedHittingTime_le, probReached_add_add_add_add_ge_mul5 (ExpectedTime).

## FIRST sub-goal
The renewal core: from InSswap+timer+bounded, ProbHitWithin(consensus) ≥ const in K=O(Rmax·n²),
composing the swap window with the OW_rankBound re-rank return. If the cons/CRS/exit branch handling
genuinely blocks (e.g. CRS doesn't return to a live swap cleanly), report the EXACT obstruction.

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide IN THE PROOF (OW_rankBound may be used as a hypothesis/the existing
  theorem). Grind or precise obstruction to HANDOFF/outbox/codex-consensus-report.md. ONLY edit
  OptimalWindows.lean (OW_consensusBound) + a helper file if needed. Self-verify lake env lean. NEVER lake build.
