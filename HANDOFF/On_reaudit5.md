# Re-audit ROUND 5 (convergence gate): epidemic-step-fields removed, race folded into resetReach, at d9c6cf7

History: 5 holes found+fixed (all the over-strong-quantification class): false resetInv; silent-config vacuity
(consensus-escape); p_reset (pinned 1/2); h12rank wrong-answer (majorityAnswer=m); unbounded counters (WellFormed);
and now the epidemic-step fields removed (race folded into cited resetReach). The reset contract now exposes ONLY
resetReach + probability/window bookkeeping. Independently verify CONVERGENCE; try hard to break it.

CRITICAL new questions (the removal could have created a GAP):
1. With epidemicStep/epidemicNonincrease/epidemicPairDescent/stepNoPhase4/stepAllResetting/pairRankResetting
   REMOVED from the contract, is the path from a fresh reset (CorrectResetSeed) all the way to OW_silenceEndpoint
   (answer propagated, silent) GENUINELY covered with NO GAP? Specifically: does resetReachs target
   (ResetCompletionTarget12 / completed) actually reach SILENCE, or only all-Resetting EpidemicRegion? If only the
   latter, where does the answer-propagation EpidemicRegion -> silence come from now (proven EpidemicMechanics with
   side conditions, or a gap)? Trace CRS_to_silence_faithful(_product)_generic end to end.
2. Did resetReach get STRENGTHENED (target now = completed silence) to absorb the race? If so, is the strengthened
   resetReach STILL faithfully [12]-derivable (Burman Lemma 3.2/Cor 3.5 give reset completion; does [12] give the
   ANSWER-epidemic completion too, or is that Kanaya/our part that must be proven not cited)? I.e. did folding the
   race into resetReach make it cite MORE than [12] actually provides (a faithfulness regression)?
3. Re-verify EVERY remaining hypothesis (h12ranking, h12reRank, h12rank, resetReach, hTimerStep, arithmetic) is
   satisfiable+faithful. Any NEW over-strong hypothesis or new class of hole?
4. Bound genuinely <= K*n, K constant in n?
Classify GENUINE non-vacuous explicit O(n), or STILL-HAS-HOLE (file:line + class). READ-ONLY, no edits, no build.
