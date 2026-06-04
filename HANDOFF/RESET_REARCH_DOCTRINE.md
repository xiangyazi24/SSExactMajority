# DOCTRINE: faithful reset re-architecture → genuine O(n) (SSExactMajority)

## Goal (one sentence)
Replace the deterministic-reset shortcut (false `resetInv` + n^3 `resetWindow` + Rmax=n) with a faithful
probabilistic reset that CITES [12] Lemma 3.2 / Cor 3.5, so the parallel-time keystone is NON-vacuous and
yields genuine O(n) EXPECTED parallel time for protocolPEM with trank=O(1), Rmax=ceil(60 log n).

## What is broken (audit verdict, 3-way verified)
- `CRSResetDuration12.resetInv : ∀C, IsTimerBounded C → CorrectResetSeed C → EpidemicRegion (maj) C` is FALSE
  (EpidemicRegion needs ALL resetting; CorrectResetSeed allows nonResettingCount>0). => h12resetDuration
  unsatisfiable => keystone PEM_expectedParallelTime_optimal operationally vacuous.
- `CRSResetDuration12.resetWindow : 2*(n*n*(n-1)) ≤ T_reset+1` forces T_reset ≥ ~2n^3 => O(n^2) parallel.
- Final correctness theorem uses protocolPEM n n n (trank=Rmax=n) => timer Θ(n) => timer-drain Θ(n^2).

## Terminal condition (acceptance)
Full `lake build`-verified, 0 sorry / 0 custom axiom; a theorem concluding O(n) EXPECTED parallel time for
protocolPEM with trank=O(1), Rmax=ceil(60 log n); every reset/ranking contract field SATISFIABLE and
faithfully derivable from [12] (ProbHitWithin / expectedHittingTime form, O(n^2) sequential = O(n) parallel);
NO false/unsatisfiable hypothesis (re-audit each field with §3.3 method).

## Avenues
(a) [PRIMARY] Probabilistic reset window. Replace `resetInv` (deterministic CRS→EpidemicRegion) by a CITED
    [12] probabilistic window: from a reset-triggered config, ProbHitWithin to EpidemicRegion (all-resetting)
    within K_reset = O(n^2) seq with constant prob (cite [12] Lemma 3.2 / Cor 3.5). Then from EpidemicRegion
    use the EXISTING proven EpidemicMechanics (stepAllResetting/stepNoPhase4/pairRankResetting + answer
    epidemic) to finish. The reset becomes a renewal phase like h12rank/h12reRank, not a deterministic invariant.
(b) Demote `CorrectResetSeed` to a POST-SUCCESS target (config after the reset epidemic completed, all-resetting),
    used only where all-resetting holds — never as an immediate consequence of a reset firing.
(c) Decouple trank=O(1) (cxg's GenericTrank window ports — reusable) and instantiate Rmax=ceil(60 log n).
(d) Split theorem families: PEM_paper_expected_time (faithful: trank=O(1), Rmax=ceil 60 log n, cited [12]) and
    PEM_deterministicReset (the current Rmax=n variant kept as a valid, clearly-labeled lemma — not the paper).

## Fallback
If a fully faithful K_reset=O(n^2) probabilistic reset proof is too deep to cite cleanly, state the reset window
as an explicit [12]-cited ProbHitWithin hypothesis (scope A) with the HONEST O(n^2)-seq bound and SATISFIABLE
shape (re-audit: must be derivable-in-principle from [12], not a disguised false invariant).

## Re-audit gate (before claiming done)
Run §3.3 three-way audit on the NEW contract: (1) self vs source+paper, (2) codex Lean-internal satisfiability,
(3) ChatGPT paper-faithfulness. Every field must be satisfiable + faithful. No vacuity.
