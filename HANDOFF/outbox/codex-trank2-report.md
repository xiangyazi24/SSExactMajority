## 2026-06-04T09:45:29-05:00 - codex-trank2

Completed the timer/window tightening layer on top of the existing `C_rank`
edits.

What changed:

- `DrainProductive.lean`: generalized
  `timer_drain_to_zero_productive` and `MAClive_to_consensus_or_crs` from the
  fixed `7*(Rmax+4)` timer cap to an explicit `T_timer`; bounds are now
  `T_timer*n*(n-1)` and `T_timer*n*(n-1)+n*(n-1)`.
- `PolynomialBound.lean`: generalized `PEM_expected_timer_drain_poly` to the
  same `T_timer` cap, and removed stale comment references to open gaps.
- `OptimalWindows.lean`: threaded `C_rank` through `OW_rankBound`,
  `OW_globalWindow`, and `PEM_expectedParallelTime_optimal`; threaded
  `T_timer` through `OW_swapWindow`, `OW_macLiveWindow`,
  `OW_liveConsensusWindow`, `OW_consensusCycleWindow`,
  `OW_consensusExpectedSteps`, `OW_consensusBound`, and the final parallel-time
  bound.

Resulting final shape:

- `OW_globalWindow n C_rank T_timer T_reset T_rank T_rerank` replaces the old
  `Rmax`-based ranking/timer window.
- `PEM_expectedParallelTime_optimal` now concludes
  `expectedParallelTimeToConsensus <= OW_globalWindow(...)/n` up to the same
  constant factor, so with `C_rank = O(1)`, `T_timer = O(1)`, and the cited
  [12] windows `T_reset,T_rank,T_rerank = O(n^2)` sequential, the theorem gives
  `E[parallel] = O(n)`.

Scope note:

- The drain/window stack is uniform in the timer cap. The Time-layer protocol is
  still `PEMProtocolCoupled`; preservation of an arbitrary constant timer cap is
  exposed as the deterministic `hTimerStep` input. Existing CRS/reset lemmas
  still carry the old `7*(Rmax+4)` invariant in parallel, so the final theorem
  requires both the legacy invariant and the new `T_timer` invariant.

Verification:

- `lake build SSExactMajority.UpperBound.Time.OptimalWindows`
  succeeded: `Build completed successfully (3251 jobs)`.
- Full `lake build` succeeded after the final edits:
  `Build completed successfully (2606 jobs)`.
- Code-form scan for `sorry`/`admit`/`axiom` in Lean sources had no hits.
