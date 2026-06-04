# codex-trank report (2026-06-04)

## Scope

The [12] ranking looseness was local: `OW_rankBound` was just forwarding
`h12ranking`, and `PEM_expectedParallelTime_optimal` used that bound only to
make the first Markov window.  I changed this from `Rmax*n*n` to a separate
constant `C_rank*n*n`.

Timer is not uniformly parameterized in the current time-bound layer.  The
protocol definition is uniform (`transitionPEM_prePhase4` initializes the
median timer to `7*(trank+4)`), but the closed timing theorems are baked to
`PEMProtocolCoupled n Rmax Emax Dmax`, hence `trank = Rmax`.

Exact baked points:

* `PEMProtocolCoupled_preserves_timer_bounded` and its private helper
  `transitionPEM_preserves_protocol_timer_bound` use
  `IsTimerBoundedConfig (7*(Rmax+4))` and call
  `transitionPEM_prePhase4_preserves_protocol_timer_bound (trank := Rmax)`.
* `timer_ge_two_descent_step`, `PEM_expected_timer_drain_poly`,
  `timer_drain_to_zero_productive`, and `MAClive_to_consensus_or_crs` unfold
  or call the coupled protocol.  The actual drain argument is mathematically
  uniform in an upper bound on `maxMedianTimer`, but the Lean statements are
  specialized to `7*(Rmax+4)`.
* `timer_drain_window`, `MAClive_to_consensus_or_crs_window`,
  `swap_live_to_cons_or_crs_or_break`, and `OW_consensusBound` propagate that
  specialization through `OW_macLiveWindow n Rmax`.
* `decision_before_timer_zero` is also coupled through
  `PEM_srank_or_timer_failure_prob_le_quarter_short35`; it needs the protocol
  parameter generalized, though the numeric entry condition `MedianTimerAtLeast
  35` is compatible with constant `trank` as soon as `7*(trank+4) >= 35`.

## Attempt

Changed `SSExactMajority/UpperBound/Time/OptimalWindows.lean`:

* `OW_globalWindow` now takes `C_rank` separately:
  `OW_globalWindow n C_rank Rmax T_reset T_rank T_rerank`.
* `OW_rankBound` now assumes and concludes the true cited [12] ranking form
  `expectedHittingTime <= C_rank*n*n`.
* `PEM_expectedParallelTime_optimal` now assumes `h12ranking <= C_rank*n*n`
  and uses the first window `2*C_rank*n*n`, not `2*Rmax*n*n`.

This removes the ranking-source log factor.  The theorem is still not the
headline `O(n)` parallel bound because `OW_consensusExpectedSteps` still
contains `OW_macLiveWindow n Rmax =
2*(7*(Rmax+4)*n*(n-1)+n*(n-1))`.

Minimal remaining structural change for the headline:

1. Add a parameterized protocol path using
   `PEMProtocol n trank Rmax Emax Dmax hn` instead of
   `PEMProtocolCoupled`.
2. Prove a generic timer invariant:
   if `7*(trank+4) <= K`, then `IsTimerBoundedConfig K` is preserved.
3. Generalize the drain stack to a timer bound `K`:
   `timer_drain_to_zero_productive` and `MAClive_to_consensus_or_crs` should
   give `K*n*(n-1)` and `(K*n*(n-1)+n*(n-1))`.
4. Replace `OW_macLiveWindow n Rmax` by a `K`/`T_timer` version and thread it
   through `swap_live_to_cons_or_crs_or_break`, `OW_consensusBound`, and
   `PEM_expectedParallelTime_optimal`.
5. Generalize the decision-tail lemma stack from `PEMProtocolCoupled` to the
   same `PEMProtocol n trank Rmax ...` instance.

Then with `C_rank = O(1)`, `K = 7*(trank+4) = O(1)`, and the cited reset/rank
windows `T_reset,T_rank,T_rerank = O(n^2)` sequential, the final window is
`O(n^2)` sequential, hence `O(n)` expected parallel time.

## Verification

* `lake env lean SSExactMajority/UpperBound/Time/OptimalWindows.lean`:
  passed, with existing linter warnings.
* `lake build SSExactMajority.UpperBound.Time.OptimalWindows`:
  passed, 3251 jobs, with existing linter warnings.
* Full `lake build`: blocked by a pre-existing root import duplicate, not by
  this patch:
  `SSExactMajority.lean:1:0: import SSExactMajority.Convergence.BurmanProperties failed, environment already contains 'SSEM.P_EM_solves_SSEM_concrete' from SSExactMajority.Convergence.Final`.

I confirmed the duplicate exists in `b927830`: both
`Convergence/Final.lean` and `Convergence/BurmanProperties.lean` define
`P_EM_solves_SSEM_concrete`, and the root imports `Final` before an import path
through `MasterModuloBurman -> BurmanProof -> BurmanProperties`.
