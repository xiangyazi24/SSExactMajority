# Final correctness chunk: the arbitrary-entry stack at clog level -> assemble the final theorems

## The remaining gap (your own diagnosis)
burmanConvergence needs entry from ARBITRARY configurations. The old entry stack carries n <= Emax/Dmax/Rmax:
  phase1_trigger_reset_or_InSrank -> resetting_exists_to_known_entry / partial_resetting_to_known_entry ->
  reach_known_entry_from_any (BurmanConvergenceFinal.lean:2042-2230), plus KnownRankingEntry.of_all_resetting
  (:988) and the all_resetting_correct_normalize* family (:2763-3256).

## Key insights to use
1. Existential schedules drain ARBITRARY finite counters for free: a config with huge delaytimer/timer values
   still wakes in finitely many selections — the witness list just gets longer. Counter UPPER bounds are never
   needed for existence; suspect every n <= Emax/Dmax use in the entry stack is a schedule-bookkeeping artifact
   (the constructed schedule lets some count grow to n where a smarter schedule or a finer invariant does not).
2. Where the old route needs a STRONG seed: conflicts/collisions mint fresh seeds with resetcount = Rmax
   (the producers at :395/:646/:741). With 2*clog 2 n + 2 <= Rmax those feed your log endpoints
   (correct_reset_seed_strong_to_InSswap_ResAns_phi_zero_log for answer-faithful re-entry;
   all_fresh_unique_from_log_seed_no_answer + dormant_to_RankingEndpoint for answer-agnostic recovery).
3. Arbitrary all-Resetting populations with low/zero fuel: drain fuel (pair positive-rc agents together,
   arbitrary finite rc drains in rc pairings), wake dormants (delaytimer selections each), agents leave
   Resetting via wake -> the population reaches non-Resetting phases where ranking/conflict machinery applies
   -> conflicts mint Rmax seeds. Check how KnownRankingEntry.of_all_resetting / all_resetting_correct_normalize
   actually proceed and mirror at clog level. If a low-fuel all-Resetting state can reach consensus WITHOUT a
   fresh seed (e.g. it is already uniform), the existing no-seed branch should port as-is (check its bounds).

## Task
1. MAP: inside phase1_trigger_reset_or_InSrank, resetting_exists_to_known_entry,
   partial_resetting_to_known_entry, KnownRankingEntry.of_all_resetting, and the
   all_resetting_correct_normalize* family, find each REAL consumption of n <= Emax / n <= Dmax / n <= Rmax
   (not binder pass-through). Classify artifact vs genuine. Report the list with file:line.
2. RE-DERIVE the stack at clog level in LogRegimeFinal.lean (new lemmas, do not edit originals), routing
   all-Resetting and seed cases through the log endpoints per insights 2-3.
3. ASSEMBLE burmanConvergence_concrete_log + P_EM_solves_SSEM_log (mirror :15941/:16052), discharging the
   strong seed-prefix obligations from the producers. Report the COMPLETE final hypothesis list.
4. If any single use is GENUINE (not an artifact — a counting argument that requires a counter >= n for the
   STATEMENT to hold), STOP on it and report precisely why; do not weaken the goal.

## HARD RULES (automode: NO effort cap; iterate lake build SSExactMajority.Convergence.LogRegimeFinal until
clean; no sorry/axiom/native_decide; commit [Xiang-proxy]; report to HANDOFF/outbox/cxfix-report.md.)
