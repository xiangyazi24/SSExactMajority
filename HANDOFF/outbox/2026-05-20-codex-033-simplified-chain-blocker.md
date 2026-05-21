# Codex status: simplified chain blocker

Remote single-file build is green after syncing the simplified end-to-end
chain:

```text
remote-build.sh SSExactMajority --file SSExactMajority/UpperBound/Time.lean
=== BUILD OK (28s) ===
```

Remaining sorries:

```text
Time.lean:5980 PEM_ranking_expected_hitting_time
Time.lean:6022 PEM_consensus_expected_hitting_time
Time.lean:6041 PEM_swap_ProbHitWithin_InSswap
```

Important blocker found while checking the new "remove timer conditions from
the chain" design:

The current `PEM_swap_ProbHitWithin_InSswap` statement is now:

```lean
InSrank C ->
  1/4 <= ProbHitWithin P C InSswap (4*n*n)
```

with no median-timer/live hypothesis.  The old available bound is only

```lean
1/2 <= ProbHitWithin P C (InSswap ∨ ¬ InSrank) (4*n*n)
```

and the intended subtraction argument needs an upper bound on
`ProbHitWithin P C (¬ InSrank) (4*n*n)`.  That upper bound was previously a
timer-live/no-reset estimate.  Without a timer premise, it is not available:
an arbitrary `InSrank` configuration may have low median timer, so reset-exit
is not a small-probability event.

`ProbHitWithin_union_le` is useful, but it does not by itself recover the
missing timer-live hypothesis.  We need one of the following interface fixes:

1. Restore timer conditions in the phase target:
   `InSrank ∧ MedianTimerAtLeast 2 ∧ MedianTimerAtMost ...`, and keep the old
   timer-exit subtraction route.
2. Strengthen the ranking expected theorem so its target carries the timer
   facts, then keep the chain target typed with those facts.
3. Prove a genuinely stronger swap theorem from arbitrary `InSrank`, including
   the reset/re-ranking fallback inside the same `4*n*n` window.  This looks
   substantially stronger and probably false/at least not supported by current
   infrastructure.

Recommendation: use option 1/2.  The current simplified chain is type-clean
but likely has over-strong Phase B and Phase C interfaces.

