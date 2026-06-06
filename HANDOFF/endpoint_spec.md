# Time-side fix: swap the renewal endpoint from old CorrectResetSeed to the strong seed — dissolve the genuine-LARGE hRmax

## Your classification found the pivot
The ONLY genuine-LARGE n <= Rmax sites are where window lemmas construct the OLD CorrectResetSeed
(BurmanConvergenceFinal:13787) whose fuel-dominance clause nonResettingCount < resetcount forces n-2 < Rmax
right after a pair-reset (CRSEven:71/:124, CRSOdd:53/:137, CRSEvenTimerPos:77/:118/:163/:203,
HeavyProofs:347/:390, inherited by PolynomialBound/GenericTrank chain). The dominance clause served ONLY the
old deterministic single-seed reset route. The creation sites already prove resetcount = Rmax and leader = .L
— which is exactly CorrectResetSeedStrong (LogRegimeFinal.lean:10), the endpoint the log route consumes with
NO fuel dominance.

## Task: re-thread the time-side window chain with the strong endpoint (new file
SSExactMajority/UpperBound/Time/LogWindows.lean, yours; import LogRegimeFinal for CorrectResetSeedStrong or
re-define a time-side equivalent StrongResetSeed to avoid heavy imports — your call, report which)
1. Strong CRS constructors: re-derive the CRS-producing lemmas (the CRSEven/CRSOdd/CRSEvenTimerPos/HeavyProofs
   constructors used by the window chain) concluding the STRONG seed (exists r: role=Resetting AND
   resetcount = Rmax AND leader=.L AND answer=majorityAnswer AND the all-Resetting-answers clause as in the old
   CorrectResetSeed second component — check what the creation steps give for OTHER Resetting agents; right
   after a pair-reset the only Resetting agents may be the pair, making the clause near-vacuous) WITHOUT the
   nonResettingCount < resetcount clause, hence WITHOUT n <= Rmax. The existing proofs already derive
   rc = Rmax; just DROP the dominance step.
2. Re-derive the genuine-LARGE chain rows at the strong endpoint: generic_crs_of_InSswap_break_with_MedC,
   generic_timer_ge_two_descent_step, generic_PEM_expected_timer_drain_poly, generic_timer_drain_window,
   generic_timer_drain_to_zero_productive, generic_PEM_expected_reset_trigger_v2,
   generic_MAClive_to_consensus_or_crs(_window), generic_swap_live_to_cons_or_crs_or_break — strong-endpoint
   versions (_strong), with hRmax REPLACED by nothing (or 0 < Rmax / clog-level where the statement needs a
   value). Keep conclusions otherwise identical (the CRS disjunct becomes the strong seed).
3. Keystone re-wire: PEM_expectedParallelTime_On_faithful consumes the CRS endpoint via the renewal
   (ConsOrCRS = IsConsensusConfig OR CorrectResetSeed) and feeds CRSReset12Faithful.freshSeedReach (which
   currently takes CorrectResetSeed C as input precondition). Change the faithful reset contract input to the
   STRONG seed (freshSeedReach: from CorrectResetSeedStrong-style input — a STRONGER input makes the cited
   premise WEAKER/easier, strictly more faithful) and produce
   PEM_expectedParallelTime_On_faithful_log with hypotheses: constants + 2*clog 2 n + 2 <= Rmax + the
   genuine-small d <= Dmax drain budget + the cited h12/epidemic premises. Same O(n) conclusion over
   PEMProtocol n 1.
4. The artifact hEmax/hDmax rows: drop n <= Emax entirely; keep only the genuine d <= Dmax budget.

## If something genuinely resists
If any window lemma turns out to USE the dominance clause beyond satisfying the old definition (i.e. the
PROOF needs the seed to dominate, not just the endpoint type), STOP on it and report the exact use.

## HARD RULES (automode: NO effort cap; lake build SSExactMajority.UpperBound.Time.LogWindows until clean;
no sorry/axiom/native_decide; commit [Xiang-proxy]; report landed names + final keystone hypothesis list to
HANDOFF/outbox/cxfix-report.md.)
