## 2026-06-03 codex phidrift

Added `SSExactMajority/UpperBound/Time/PhiDrift.lean`.

Result: the requested one-step drift bound is false on the natural reservoir
region

`InSswap C ∧ ResAns (majorityAnswer C) C`.

Formal obstruction:

- `phiCount_drift_target_false_on_InSswap_ResAns`

The counterexample is the same four-agent shape as the earlier `PhiDescent`
obstruction, now aggregated over all ordered off-diagonal scheduler pairs.
Take `n = 4`, all inputs `A`, all agents `Settled`, ranks `0,1,2,3`, and set
only the lower-median rank (`rank.val = 1`) to `answer = .phi` and `timer = 1`;
all other answers are `.outA`.

It satisfies:

- `InSswap C`
- `ResAns (majorityAnswer C) C`
- `phiCount C = 1`
- `¬ IsConsensusConfig C`

Exact ordered-pair computation over `OffDiagonalPairs 4`:

- 2 ordered pairs decrease `phiCount`: the lower/upper median-pair decision,
  both orientations, sends the median pair to `.outA`.
- 2 ordered pairs increase `phiCount`: lower median against max rank, both
  orientations, decrements the lower-median timer to `0` and Phase 4 propagation
  copies `.phi` to the max-rank agent.
- 8 ordered pairs leave `phiCount` unchanged.

Therefore

`∑_{i≠j} phiCount (C.step P i j) = 12 = 12 * phiCount C`,

so the one-step expected drift is exactly `0`.  The target
`drift ≤ -1/(n(n-1))` would require, after multiplying by `n(n-1) = 12`,

`ordered_post_sum + 1 ≤ 12 * phiCount C`,

which is `13 ≤ 12` in this counterexample.

Minimal strengthening indicated by the obstruction:

- Excluding only "single-step phi increase" is not enough as a useful region
  unless it is stated tautologically as a pair-surplus condition.
- A semantic one-step `phiCount` descent region must prevent imminent median
  `.phi` propagation and ensure an active correction pair exists.  The clean
  strengthening is:

`InSswap C ∧ ResAns (majorityAnswer C) C ∧ MedianAnswerCorrect C ∧ MedianTimerZero C`

where `MedianTimerZero C` means every median-ranked propagation agent has
timer `0`.  `MedianAnswerCorrect` prevents copying `.phi` outward; timer zero
makes any wrong/`.phi` non-median partner immediately correctable.  The commonly
used live condition `MedianTimerAtLeast 1` goes in the wrong direction for a
one-step `phiCount` drift theorem: with a correct median but timer still positive,
non-median `.phi` agents can wait with zero one-step `phiCount` drift.

Verification:

`PATH=$HOME/.elan/bin:$PATH lake env lean SSExactMajority/UpperBound/Time/PhiDrift.lean`

Result: passed. `rg -n "sorry|axiom|native_decide" SSExactMajority/UpperBound/Time/PhiDrift.lean`
returned no matches.
