# Optimal parallel-time bound — completion map (Zinan, 2026-06-03)

## Done & clean (#print axioms = propext/Classical.choice/Quot.sound only)
- Correctness/termination (P_EM_solves_SSEM_final).
- FINITE expected parallel time (PEM_expected_parallel_time_finite_of_initial).
- Window-amplification skeleton: pem_table2_phase_windows_to_expectedParallelTime
  reduces the OPTIMAL bound to 5 constant-prob phase windows
  (hRank 1/10, hSwap 1/20, hDec 1/8, hTim 1/1280, hSem 1/2).

## Clean polynomial pieces already proven (the hard math is mostly DONE)
- Ranking: PEM_FreshRankingStart_expected_until_srank_timer2_or_consensus_or_heap_exit_le
  ≤ Rmax·n²   (Time.lean:6288 / Composition.lean:1903)  CLEAN
- AllR → Phase1Goal: allR_to_phase1Goal_bound ≤ Rmax·n²  (RecoveryBound.lean:845)  CLEAN
- Timer drain: PEM_expected_timer_drain_poly: InSswap+MAC → (Consensus ∨ CRS ∨ break)
  ≤ 7(Rmax+4)·n(n-1)   (PolynomialBound.lean:151)  CLEAN
- Epidemic descent: PEM_CRS_to_allR_or_break: CRS → (nRC=0 ∨ ¬CRS) ≤ n²(n-1)
  (PolynomialBound.lean:587)  CLEAN

## The ONE keystone gap
det_trace (Phase2Helper axiom, ORPHANED): AllR+correct → Target reachable, E[T] ≤ 2Rmax·n².
Equivalently the poly Phase1Goal→consensus / decision-phase bound. Currently the live
path only has the FINITE version (bounded_config_consensus_uniform_le, sup over finite
config space). Composing it polynomially from the clean pieces above + the renewal for
the break/exit disjuncts is the remaining ASSEMBLY work (not a missing hard lemma).

## Known bug
PropagationLive.lean:64 PEM_expected_consensus_from_InSswap_MAC: stated bound
wrongAnswerCount·n(n-1) is FALSE (off by ~Rmax; correction needs a reset cycle —
phase4_propagate resets the pair, median timer must drain first). Restate ~O(Rmax·n²).
Only consumer: hPropagationLive_proof (hTim window); re-derive its constants after restate.

## Cleanup
Phase2Helper.lean is imported by nothing — its 2 axioms taint no live theorem. Delete
for repo-wide 0-custom-axiom.

## Session 2026-06-03 verified commits (uisai2)
- 5d4c32b PropagationLive nlinarith→omega (build 2595) + sorry@64 false-bound audit note.
- 266498f Time.lean 0 sorry (dead | sorry fallbacks removed, build 2583).
