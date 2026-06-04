# codex race report

## 2026-06-03

Status: complete.

Implemented `SSExactMajority/Probability/PhaseRace.lean`.

Proof route: Option B, direct two-hit-flag event.  No absorbing wrapper.

Main additions:
- `ProbGoodBeforeBad`: mass of `hitTwoFlagDist` where the good flag is true and the bad flag is false at window `K`.
- `probNotHitBy_le_expectedHittingTime_div_window`: positive-window Markov tail bound `P[T > K] ≤ E[T] / K`.
- `ProbHitWithin_ge_one_sub_expectedHittingTime_div`: general Markov lower bound `1 - E[T]/K ≤ ProbHitWithin ... K`, including the `K = 0` case.
- `ProbHitWithin_or_le_ProbGoodBeforeBad_add_bad`: direct event cover for `(G ∨ D)` hit by good-before-bad plus bad-hit.
- `probHit_good_before_bad_ge`: generic race lemma
  `1 - B / K - δ ≤ ProbGoodBeforeBad ... G D K`.

Verification:
```
PATH=$HOME/.elan/bin:$PATH lake env lean SSExactMajority/Probability/PhaseRace.lean
```
passed with no output.

Forbidden constructs check:
```
rg -n "sorry|axiom|native_decide" SSExactMajority/Probability/PhaseRace.lean
```
had no matches.
