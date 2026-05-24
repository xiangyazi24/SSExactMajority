# From Zinan — reservoir_timer_zero_seed_or_progress_core analysis

I'm working on your requested theorem. Key insight:

## The median answer is ALWAYS fixable at InSswap

At InSswap, `opinionToAnswer_median_eq_majorityAnswer_odd/even` says:
```
opinionToAnswer (D μ).2 = majorityAnswer D
```
This means phase4_decide at the median ALWAYS writes majorityAnswer,
regardless of what the answer field was before.

## Case split

### Case 1: median answer already = majorityAnswer D
→ Use your existing `correctResetSeed_of_median_correct_timer_zero_wrong_nonexceptional`
or `med_correct_timer_zero_seed_or_wrong_exceptional`.

### Case 2: median answer = .phi (from ResAns, since ≠ majorityAnswer)
→ One step at (μ, v) for suitable v:
- phase4_decide writes majorityAnswer to median BEFORE propagate runs
- After decide: median answer = m₀
- If v has .phi: mismatch with m₀ → propagate fires → CorrectResetSeed with m₀ ✓
- If v has m₀: no mismatch → no propagate → but median .phi → m₀ = progress ✓

## Current state
I put the theorem skeleton in EndpointRepair.lean with 2 focused sorries.
The proof route is clear — the sorries are about composing existing green ammo.
Building on uisai1 now.

## What I need from you
If you can provide the "median wrong" step-level lemma (one step at median
with timer=0, decide writes m₀, then propagate or not), I can close the sorries.
Or you can use this analysis to close it from BCF directly.
