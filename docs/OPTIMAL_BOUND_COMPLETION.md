# Optimal (time-optimal, explicit-poly) parallel-time bound — completion map

## Status
DONE (clean, committed, 0 sorry/axiom): correctness, termination, FINITE expected time (<⊤),
drift framework (DriftHittingTime: expectedHittingTime_le_of_drift), swap chain
(swap_live_to_cons_or_crs_or_break ≥1/4 → cons∨CorrectResetSeed∨exit), decision/timer windows,
amplification lemmas (ExpectedTime: expectedHittingTime_le_window_mul_inv = E[T]≤K·p⁻¹;
ProbHitWithin_ge_half_of_expectedHittingTime_le = Markov), ALL qualitative ranking machinery.

Proven NEGATIVE results pinning the route: PhiDescent/RankInitDescent/PhiDrift/CombDrift
(no simple monotone potential works; no invariant region has per-step drift — protocol cycles).

## REMAINING for the explicit-poly OPTIMAL bound = OptimalWindows.lean OW_rankBound + OW_consensusBound
The repo proves convergence + FINITENESS; the time-OPTIMAL (explicit O(Rmax·n²) seq) layer needs:

1. ENTRY E[T] [cxen, EntryBound.lean]: arbitrary bounded/dormant config → FreshRankingStart in
   explicit poly. Today only QUALITATIVE dormant_to_FreshRankingStart (∃ path,
   BurmanConvergenceFinal:6985). Lead: rcLevelPotential_* (RecoveryBound) is a nonincreasing
   potential w/ per-step drop prob — the reset-wave descent backbone. Check rcLevelPotential=0 +
   awakening ⟹ FreshRankingStart.
2. ELIMINATE +B: allR_to_consensus_bound (PolynomialBound:808) is ≤ Rmax·n² + B with B only <⊤
   (bounded_config_consensus_uniform_le:778). Upgrade B to explicit poly.
3. CLOSE heap-exit disjunct in PEM_FreshRankingStart_expected_until_srank_timer2_or_consensus_or_heap_exit_le
   (Time:6288, ≤Rmax·n²) via renewal (exit → re-enter via entry link).
4. ASSEMBLE OW_rankBound (entry ∘ FreshRankingStart bound, renewal-closed) and OW_consensusBound
   (swap chain + OW_rankBound via expectedHittingTime_le_window_mul_inv), then the unconditional
   PEM_expectedParallelTime_optimal follows from the existing team assembly
   PEM_expected_parallel_time_from_global_expected_phase_bounds.

Scope: focused multi-session campaign (the explicit-complexity layer of the paper), precisely
mapped, all qualitative+finiteness scaffolding in place.

## DEFINITIVE DIAGNOSIS (after entry-link attempts)
No clean phase-invariant region works: the random scheduler INTERLEAVES phases. From partial
awakening, pair (unsettled-follower, root) fires a recruit step → state is cleanly none of
awakening/FreshRankingStart/ranking. variable_descent_until_goal + drift BOTH need the region
closed under ALL pairs (hInvStep/hRegStep); every phase-specific region fails this.

CORRECT ROUTE = global Lyapunov on the ONE provably-closed region IsBoundedConfig
(PEMProtocolCoupled_preserves_bounded). Collapses everything to ONE obligation:
  global φ : BoundedConfig → ℕ with  E[φ(step)] + ε ≤ φ  for all non-consensus bounded C,
then expectedHittingTime_le_of_drift gives E[T to consensus] ≤ φ(C₀)/ε directly.
Subtlety: fresh collision/error resets inject rare positive jumps ⟹ needs supermartingale /
bounded-total-increase argument (same family as the PP-proof supermartingale work).

Proven reusable component pieces: rcLevelPotential_* (reset-mass, RecoveryBound, nonincreasing+drop),
awakening_step_descent_witness/prob (EntryBound, card descent), phiCount lemmas (answer-error).
Global φ must use measures defined on ALL bounded configs (Σrc, #non-Settled, #wrong-answer),
weighted W3≫W2≫W1, with the reset-jump compensator the crux.
