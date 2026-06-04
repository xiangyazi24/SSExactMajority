# Codex task (uisai1): OW_consensusBound under scope (A) — [12] re-rank as cited hypothesis

SCOPE (A, decided): formalize Kanaya's contribution CITING [12]'s Optimal-Silent-SSR time bounds as
hypotheses (the paper does exactly this — Lemmas 1-3). So the CRS/exit re-rank-return time is an
explicit HYPOTHESIS, not something we derive from compactness (removes allR_to_consensus's +B).

cxcons's obstruction was: the renewal needs an explicit CRS/exit → live-swap return; the existing
allR_to_consensus has a non-explicit existential B. (A) replaces that with a cited explicit hypothesis.

## Add a helper theorem in OptimalWindows.lean (or a new OptimalWindowsA.lean)
```
theorem OW_consensusBound_of_reRank
  (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
  -- CITED [12]+reset re-rank-return time (explicit poly):
  (hReRank : ∀ C : Config (AgentState n) Opinion n,
     IsTimerBoundedConfig (7*(Rmax+4)) C →
     (CorrectResetSeed C ∨ ¬ (InSswap C ∧ MedianTimerAtLeast 1 C)) →
     Probability.expectedHittingTime P hn2 C
       (fun D => (InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D) ∨ IsConsensusConfig D)
       ≤ (R_return : ENNReal)) :
  ∀ C, InSswap C → MedianTimerAtLeast 1 C → IsTimerBoundedConfig (7*(Rmax+4)) C →
    Probability.expectedHittingTime P hn2 C IsConsensusConfig ≤ (explicit poly in Rmax,n,R_return)
```
Proof via window_mul_inv: per cycle, from InSswap+timer the swap window gives ProbHitWithin(cons ∨
CorrectResetSeed ∨ exit) ≥ 1/4 in W_swap; on CRS/exit, hReRank returns to (InSswap+MAC+timer) in
R_return expected (⟹ ProbHitWithin ≥1/2 in 2·R_return via ProbHitWithin_ge_half_of_expectedHittingTime_le);
from InSswap+MAC, the swap reaches consensus (MAC ⟹ decision correct, no CRS regress) w.p. ≥1/4 in W_swap.
Compose (probReached_add_..._ge_mul) ⟹ ProbHitWithin(consensus) ≥ const in K=O(W_swap+R_return);
window_mul_inv ⟹ E[T] ≤ K/const. Then OW_consensusBound follows by supplying hReRank from the cited
[12] ranking bound (state that supply as another hypothesis OR the existing OW_rankBound-style lemma).

## FIRST sub-goal
Prove OW_consensusBound_of_reRank (the renewal, with hReRank as hypothesis). This is the pure
Kanaya-composition, fully provable from the swap window + hReRank + window_mul_inv. If a branch
(e.g. CRS preserving MAC across re-rank) blocks, report the EXACT obstruction.

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide (hReRank is an explicit HYPOTHESIS, allowed). Grind or precise
  obstruction to HANDOFF/outbox/codex-consensusA-report.md. Edit OptimalWindows.lean or new
  OptimalWindowsA.lean. Self-verify lake env lean (project-root form). NEVER lake build.
