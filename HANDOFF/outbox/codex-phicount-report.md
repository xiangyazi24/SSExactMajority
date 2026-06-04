## 2026-06-03 codex phicount

Added `SSExactMajority/UpperBound/Time/PhiDescent.lean`.

Result: the requested all-step non-increase fact is false for the natural
qualitative cycle region

`InSswap C ∧ ResAns (majorityAnswer C) C`.

Formal counterexample:

- `phiCount_not_nonincreasing_on_InSswap_ResAns`
- `phiCount_increases_on_phiCex_step`

Counterexample shape: `n = 4`, all inputs are `A`, ranks are already sorted
and all agents are `Settled`. The lower-median rank has `answer = .phi` and
`timer = 1`; the max-rank agent has `answer = .outA`. Scheduling the
lower-median agent against the max-rank agent is not an even median-pair
decision step, so Phase 4 decision does not resolve the lower median.
Then Phase 4 propagation decrements the lower-median timer to `0`, sees
`.phi ≠ .outA`, and copies `.phi` to the max-rank agent while resetting both.
Thus the proved values are:

- `phiCount phiCex = 1`
- `phiCount (phiCex.step phiCexP loMed4 max4) = 2`

So the variable-descent proof cannot use the proposed global hypothesis

`∀ C, Pinv C → ∀ i j, phiCount (C.step P i j) ≤ phiCount C`

when `Pinv` is `InSswap ∧ ResAns (majorityAnswer)`. The per-macro-step
descent based on that monotonicity was not attempted after this counterexample.
A stronger live/correct region, e.g. including lower-median correctness before
timer expiry, would need a separate monotonicity statement.

Verification:

`PATH=$HOME/.elan/bin:$PATH lake env lean SSExactMajority/UpperBound/Time/PhiDescent.lean`

Result: passed. No `sorry`, `axiom`, or `native_decide` in `PhiDescent.lean`.
