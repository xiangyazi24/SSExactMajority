# THE LAST CORRECTNESS PIECE: strengthen the seed-producer layer to expose resetcount = Rmax

## State (your report)
burmanConvergence_concrete_log_with_strong_seed_prefixes (:2570) and
P_EM_solves_SSEM_log_with_strong_seed_prefixes (:2654) are PROVEN, conditional only on:
  MedCorrectLiveProducesStrongSeedOrProgress and ReservoirCaseProducesStrongSeedOrProgress.
The weak versions (CorrectResetSeed-only) are proven in the old chain; the strong versions need the producers
to expose the resetcount = Rmax (and leader .L) witness they establish internally.

## Task
Discharge the two obligations: prove
  medCorrectLiveProducesStrongSeedOrProgress_holds : MedCorrectLiveProducesStrongSeedOrProgress ...
  reservoirCaseProducesStrongSeedOrProgress_holds : ReservoirCaseProducesStrongSeedOrProgress ...
by re-deriving the producer-layer proofs with the strengthened conclusion. Method: follow the EXISTING proofs
of the weak obligations (the lemmas proving ReservoirCaseProducesCorrectSeedOrProgress and the med-correct
counterpart in BurmanConvergenceFinal.lean — find where each CorrectResetSeed conclusion is established). At
every point a seed is created, the creating step sets resetcount = Rmax and leader = .L on the seed
(:395-396, :646, :741 and the collision/error step lemmas). Track whether the construction's schedule
continues AFTER seed creation: if the seed is created by the LAST step, the strong fact holds at the endpoint;
if intermediate steps follow, verify they do not touch the seed (disjoint pairs) or re-derive with the seed
protected. Re-state the producer lemmas in LogRegimeFinal.lean as strong variants (do not edit originals);
duplicate proof skeletons where needed.
Then instantiate: P_EM_solves_SSEM_log (final, hypothesis list = constants + clog only) by feeding the
discharged obligations into P_EM_solves_SSEM_log_with_strong_seed_prefixes. Report the COMPLETE final
hypothesis list — this is the paper-faithfulness verdict for correctness.

## If a producer genuinely loses the witness
If some producer's construction genuinely continues past seed creation in a way that decrements the seed's
resetcount (e.g. the seed itself must keep interacting), report the exact location and the actual final
resetcount value (Rmax - k for which k) — a weaker witness like Rmax - 2 >= 2*clog 2 n + 2 is still fine
(just shifts the constant); land that instead of stopping, and report the shift.

## HARD RULES (automode: NO effort cap; lake build SSExactMajority.Convergence.LogRegimeFinal until clean;
no sorry/axiom/native_decide; commit [Xiang-proxy]; report to HANDOFF/outbox/cxfix-report.md.)
