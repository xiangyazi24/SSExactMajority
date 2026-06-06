# Step 2 endgame: produce burmanConvergence_concrete_log + P_EM_solves_SSEM_log (clog-level hypotheses only)

## What exists now (LogRegimeConvergence.lean)
log_seed_uniform_leader_to_FreshRankingStart_resAns_noPhi_log (:166): from a Resetting seed with
resetcount >= 2*clog2 n + 2, leader .L, and (forall Resetting w, answer w = majorityAnswer C) — all constants
otherwise (4<=n, 1<Dmax, 0<Rmax) — reaches FreshRankingStart AND ResAns m0 AND no-phi AND majority preserved.
NO n<=Dmax / n<=Rmax / n<=Emax.

## Goal
The log-regime correctness theorems:
  burmanConvergence_concrete_log  and  P_EM_solves_SSEM_log
with parameter hypotheses ONLY of the forms: numeric constants (4<=n, 1<Dmax, 0<Emax...), and
2*clog2 n + 2 <= Rmax (and clog-level bounds on Dmax/Emax ONLY if a genuine consumer needs them — report each).
Mirror the statement shapes of burmanConvergence_concrete (~:15941) and P_EM_solves_SSEM_final (~:16052) in
BurmanConvergenceFinal.lean, instantiating the protocol at the log parameters instead of n.

## The work: re-route ALL consumers through the _log route
1. SEED INTERFACE (piece A): the producers of CorrectResetSeed actually establish resetcount = Rmax on the
   seed(s) (BurmanConvergenceFinal.lean:395-396, :646, :741) plus leader .L plus the answer invariant.
   Strengthen the interface: either a CorrectResetSeedStrong predicate carrying (exists r, role=Resetting AND
   resetcount = Rmax AND leader=.L) AND the all-Resetting-answers invariant, with lemmas showing each existing
   producer delivers it; or thread the extra facts alongside. Verify the answer invariant matches the _log
   theorem hAllAns (CorrectResetSeed def at :13787 — check its exact answer clause; adapt if it differs).
2. RE-ENTRY (the :13666/:13719 consumer): replace the old positive-resetcount route with: strong seed +
   (2*clog2 n + 2 <= Rmax) -> _log theorem -> FreshRankingStart -> continue the existing post-ranking-start
   chain to consensus/silence.
3. RANKING-SIDE CARRIER (piece D): ranking_from_InSrank_by_parity bad-ranking handlers consume n<=Dmax and
   n<=Rmax (BurmanProof.lean:12376, :13074). Read WHY: if the bad-ranking path triggers a reset whose recovery
   used the old n-fuel machinery, re-route that recovery through the _log fresh route as well (the bad-ranking
   reset also produces an Rmax-fueled seed — verify). If the carrier is genuinely different (not a reset
   recovery), STOP on it and report exact reasoning + file:line.
4. Assemble burmanConvergence_concrete_log from the re-routed phases (collision/error -> strong seed -> _log
   fresh -> ranking -> silence/consensus), then P_EM_solves_SSEM_log instantiating concrete log parameters
   (e.g. Rmax := 2*clog2 n + 2 or any value >= it; state the instance cleanly).

## Method
NEW file SSExactMajority/Convergence/LogRegimeFinal.lean (yours) importing LogRegimeConvergence + the existing
chain (read-only). You may re-derive small log-variants of mid-chain lemmas in your file when the originals
hard-code n<=_; reuse everything parameter-generic as-is. MAP first (list the consumers you must re-route),
then build. If any segment between FreshRankingStart and silence carries a GENUINE n<=_ that is not a reset
recovery, STOP and report it precisely instead of weakening.

## HARD RULES (automode: NO effort cap — this is the correctness endgame)
Iterate lake build SSExactMajority.Convergence.LogRegimeFinal until clean. No sorry/axiom/native_decide.
Commit clean with [Xiang-proxy]. Report: final theorem names + file:line + the COMPLETE parameter hypothesis
list of P_EM_solves_SSEM_log (this is the paper-faithfulness verdict) to HANDOFF/outbox/cxfix-report.md.
