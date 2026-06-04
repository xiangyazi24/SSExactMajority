# Codex task (uisai1): faithful reset re-architecture → non-vacuous, genuine O(n)

Read HANDOFF/RESET_REARCH_DOCTRINE.md first. Context: the 3-way adversarial audit found the parallel-time
keystone OPERATIONALLY VACUOUS — `CRSResetDuration12.resetInv` is a FALSE hypothesis (EpidemicRegion needs ALL
agents Resetting; CorrectResetSeed allows nonResettingCount>0), so h12resetDuration is unsatisfiable; and
`resetWindow : 2*(n*n*(n-1)) ≤ T_reset+1` forces an n^3 (=> O(n^2) parallel) window. Fix it faithfully.

## Scope of THIS task (one file/section, do NOT touch GenericTrank.lean — cxg owns it and is paused)
Work in OptimalWindows.lean (and a new helper file if cleaner). Goal: replace the false/over-strong reset
contract with a FAITHFUL, SATISFIABLE, [12]-cited probabilistic reset window, and rewire CRS_to_silence_faithful.

## Steps
1. AUDIT the current `CRSResetDuration12` (OptimalWindows.lean:445) and how `CRS_to_silence_faithful` consumes
   each field (resetInv, stepNoPhase4, stepAllResetting, pairRankResetting, resetWindow). Confirm in writing
   which fields are sound (the EpidemicMechanics one-step closures, applied ON all-resetting configs ARE fine)
   and which are broken (resetInv: CRS→EpidemicRegion is false; resetWindow n^3).
2. DESIGN the faithful contract. Replace `resetInv` (deterministic CRS→EpidemicRegion) with a CITED [12]
   probabilistic reset-completion window of the ProbHitWithin form, e.g.:
     resetReach : ∀ C, <reset-triggered/CorrectResetSeed-precondition> →
        p_reset ≤ Probability.ProbHitWithin P C (fun D => EpidemicRegion (majorityAnswer C) D) K_reset
   with K_reset = O(n^2) sequential (NOT n^3) and p_reset a positive constant — this is [12] Lemma 3.2 / Cor 3.5
   (reset epidemic reaches all-Resetting w.h.p. in O(log n) time; answer epidemic O(n) time). Keep it as a CITED
   hypothesis (scope A), but it MUST be satisfiable + faithfully shaped (a real ProbHitWithin window, not a false
   deterministic invariant). Demote CorrectResetSeed to a post-success/all-resetting target where EpidemicMechanics
   legitimately apply.
3. REWIRE CRS_to_silence_faithful to: (reset-triggered) --[resetReach, cited 12]--> EpidemicRegion
   --[existing proven EpidemicMechanics: stepAllResetting/stepNoPhase4/pairRankResetting + answer epidemic]-->
   OW_silenceEndpoint, within K_reset+T_rank, prob ≥ const. Drop the false resetInv and the n^3 resetWindow.
4. Re-derive the window arithmetic so the reset contributes O(n^2) sequential (=> O(n) parallel), NOT n^3.
5. Re-audit (§3.3): every new contract field must be SATISFIABLE and faithfully [12]-derivable. NO false invariant.

## FIRST sub-goal + report
Do steps 1-2: write the faithful contract definition (compiles, `lake build` the OptimalWindows olean) and a
written audit of old-vs-new fields. Report to HANDOFF/outbox/cxreset-report.md whether the rewiring (step 3) is
mechanical given the existing EpidemicMechanics, or hits a genuine gap (name it precisely).

## HARD RULES
- NO sorry/axiom/admit/native_decide. The new contract may be a CITED hypothesis (like h12rank) but must be
  SATISFIABLE and faithful — never reintroduce a false ∀-invariant. Verify via `lake build` (olean), not just
  lake env lean. Do NOT touch GenericTrank.lean. Report precisely; if blocked, write "### BLOCKER: <what>".
