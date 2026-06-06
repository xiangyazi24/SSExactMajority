# Final wire continuation: the no-answer log recovery endpoint + reroute + assemble the final theorems

## You already diagnosed it (your report) — now build it. Three steps, all pieces exist.

### 1. all_fresh_unique_from_log_seed_no_answer
Answer-AGNOSTIC version of all_fresh_uniform_unique_from_log_seed (LogTreeReset.lean:3571): from a Resetting
seed with resetcount >= 2*clog 2 n + 2 and leader .L (NO answer hypothesis):
  exists L, after runPairs: (forall w, FreshResettingAt Dmax w) AND (exists! l, leader l = .L).
Same construction as the answer-coupled one (growth preserving root .L -> fueled leader tournament -> drain
preserving unique leader) with the answer clauses dropped. Reuse the existing growth/tournament/drain lemmas —
if they are stated answer-coupled, either generalize them (drop the answer hypotheses/conclusions) or add
answer-free variants; the proofs are the same minus the answer bookkeeping.
NOTE the bad-ranking snapshot gives you MORE: ALL Resetting agents have rc = Rmax AND leader .L (every
Resetting agent is a fresh seed). You may state the endpoint with whatever Resetting-population precondition
the snapshot provides (all Resetting have rc = Rmax and leader .L) if that simplifies the tournament
bookkeeping; report the exact precondition landed.

### 2. Reroute the ranking-side recovery at clog level
Re-derive (in LogRegimeFinal.lean, do NOT edit BurmanProof.lean):
  reset_snapshot_to_RankingEndpoint_log and step_reset_snapshot_to_RankingEndpoint_log
mirroring BurmanProof.lean:11468/:11529 but with hypotheses 1 < Dmax (or what the dormant route needs) and
2*clog 2 n + 2 <= Rmax instead of n <= Dmax / n <= Rmax, routing through your no-answer endpoint into
IsDormantConfig / dormant_to_RankingEndpoint (BurmanProof.lean:11368). Then re-derive the parity bad-ranking
handlers (the consumers at BurmanProof.lean:12376/:13074) at clog level the same way.

### 3. Assemble the final theorems
burmanConvergence_concrete_log and P_EM_solves_SSEM_log (mirroring burmanConvergence_concrete ~:15941 and
P_EM_solves_SSEM_final ~:16052 in BurmanConvergenceFinal.lean), combining: the strong-seed re-entry route you
already landed (correct_reset_seed_strong_to_InSswap_ResAns_phi_zero_log + the strong seed-prefix interfaces)
+ the clog-level ranking recovery from step 2. Final hypothesis list must be ONLY: Inhabited, numeric constants
(4 <= n, 1 < Dmax, 0 < Emax-style), and clog-level bounds (2*clog 2 n + 2 <= Rmax, similar for Dmax/Emax ONLY
if genuinely needed — report each). If the strengthened seed-prefix obligations (MedCorrectLiveProducesStrongSeedOrProgress,
ReservoirCaseProducesStrongSeedOrProgress) are dischargeable from the existing producers (they prove rc = Rmax
at creation — BurmanConvergenceFinal.lean:395,:646,:741), discharge them; if a producer genuinely loses the
rc = Rmax fact mid-schedule, report exactly where.

## HARD RULES (automode: NO effort cap — this completes the correctness side of the paper result)
Files: LogRegimeFinal.lean / LogTreeReset.lean / LogRegimeConvergence.lean (yours). Iterate
lake build SSExactMajority.Convergence.LogRegimeFinal until clean. No sorry/axiom/native_decide. Commit clean
with [Xiang-proxy]. Report final theorem names + file:line + COMPLETE hypothesis list of P_EM_solves_SSEM_log
to HANDOFF/outbox/cxfix-report.md.
