## 2026-06-03 codex combdrift

Added `SSExactMajority/UpperBound/Time/CombDrift.lean`.

Result: the requested net-count drift inequality is false on the natural
reservoir region

`InSswap C ∧ ResAns (majorityAnswer C) C`

even for the combined potential

`combPotential W2 W1 C = W2 * phiCount C + W1 * (n - settledCount C) + timerSum C`.

Formal obstruction:

- `combPotential_drift_target_false_on_InSswap_ResAns`

Counterexample: `n = 4`, all inputs `A`, all agents `Settled`, ranks
`0,1,2,3`, all timers `0`; only the lower-median rank (`rank.val = 1`,
so `rank.val + 1 = ceilHalf 4`) has `answer = .phi`, and every other
agent has `answer = .outA`.

It satisfies:

- `InSswap C`
- `ResAns (majorityAnswer C) C`
- `phiCount C = 1`
- `¬ IsConsensusConfig C`
- the median-ranked agent has `answer = .phi`

For arbitrary weights `W2 W1 : ℕ`:

- base potential is `W2`
- 4 ordered pairs propagate median `.phi` outward and reset two agents,
  each with post-potential `2*W2 + 2*W1`
- 2 ordered median-pair decision pairs repair the `.phi`, post-potential `0`
- 6 ordered pairs are flat, post-potential `W2`

Thus the ordered post-step sum is exactly

`14 * W2 + 8 * W1`.

The target inequality after multiplying by the ordered-pair count would require

`(14 * W2 + 8 * W1) + 1 ≤ 12 * W2`,

which is impossible for every `W2 W1`.

Needed R: at minimum, the reservoir region must exclude median `.phi`:

`∀ μ, (C μ).1.rank.val + 1 = ceilHalf n → (C μ).1.answer ≠ .phi`.

Under `ResAns (majorityAnswer C) C`, this is equivalent to every median-ranked
agent already carrying `majorityAnswer C`.  This condition is not cosmetic:
without it, the median `.phi` propagation pairs outnumber the median-pair
repair pairs, and the settled-incompleteness weight only worsens the drift
because the bad propagation pairs reset two agents.

Verification:

`PATH=$HOME/.elan/bin:$PATH lake env lean SSExactMajority/UpperBound/Time/CombDrift.lean`

Result: passed.

`rg -n "sorry|axiom|native_decide" SSExactMajority/UpperBound/Time/CombDrift.lean`

Result: no matches.
