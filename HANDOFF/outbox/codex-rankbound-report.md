# codex-rankbound report

Status: BLOCKED-at per-step drift for `phi = n - heapPrefixLen`.

Date: 2026-06-04T02:47:13Z

I did not close `OW_rankBound`. The requested additive drift inequality is false
for the prefix-length potential on the current ranking region.

Exact obstruction:

* The descent witness `heapPrefix_recruit_step` / BCF child variant proves that,
  from `HeapPrefix C k ∧ SettledMedianTimerStrong C`, scheduling an Unsettled
  child with the frontier parent of rank `heapParent k` grows the prefix to
  `HeapPrefix (k+1)`.
* But `rankDeltaOSSR` Part 3 does not restrict recruitment to that frontier
  parent. Any Settled agent with `children < 2` and valid child rank may recruit
  any Unsettled agent.
* Concrete shape: take `k = 2`, `n >= 4`, with a valid `HeapPrefix C 2`.
  The root rank 0 has `children = 1`, the rank-1 Settled agent has
  `children = 0`, and all remaining agents are Unsettled. The good ordered
  pairs `(u, root)` recruit rank 2 and decrease `phi` by 1. The bad ordered
  pairs `(u, rank1)` recruit rank 3 while rank 2 is still missing. The resulting
  configuration has a Settled agent of rank 3, so `HeapPrefix D 2` fails by the
  "all Settled ranks < 2" clause, and smaller positive prefixes fail as well
  because rank 1/rank 3 are already Settled. Thus `heapPrefixLen` drops instead
  of increasing.
* These bad off-frontier recruit pairs have the same order of scheduler mass as
  the good frontier pairs: `(n-k)/(n(n-1))` in the `k=2` example. Their potential
  increase is at least 2 if missing-prefix states are assigned length 0, while
  the good witness only gives a decrease of 1. So the expected one-step drift
  cannot satisfy
  `E[phi(next)] + epsilon <= phi(C)` for any positive `epsilon`.
* Independently, HeapPrefix does not constrain Unsettled `errorcount`. Ordered
  Unsettled/Unsettled pairs with low errorcount can trigger the `rankDeltaOSSR`
  error-monitoring reset branch, producing Resetting agents and leaving the
  HeapPrefix region. This is another positive-drift/exit term not dominated by
  the single frontier witness.

This matches the existing stochastic ranking API in `SSExactMajority/UpperBound/Time.lean`:
`PEM_heapPrefix_recruit_step_or_exit_expected_le` and
`PEM_heapPrefix_expected_until_rankingEndpoint_or_exit_from_level_le` deliberately
target `Next ∨ ¬ Region`, with comments noting that arbitrary scheduler
interactions can leave the heap-prefix region. The available proved bound is a
ranking-to-endpoint-or-heap-exit bound from `FreshRankingStart`, not the
unconditional rank endpoint bound required by `OW_rankBound`.

What would be needed next:

* Either replace `heapPrefixLen` by a potential compatible with out-of-order
  recruits, e.g. settled-count plus reset/error components, and prove all
  non-frontier recruit steps are non-increasing/progress;
* or strengthen the phase region with an actual protocol-invariant "frontier-only"
  property. That property is not true for the current `HeapPrefix` after `k=2`,
  so this would require a different region/potential, not just an extra hypothesis;
* and separately account for Unsettled error-monitoring resets or route them
  through an explicit restart/renewal bound.

Verification: `lake env lean SSExactMajority/UpperBound/Time/OptimalWindows.lean`
exited 0. Warnings are the existing `OW_rankBound` / `OW_consensusBound` `sorry`s
and one unused section-variable warning.
