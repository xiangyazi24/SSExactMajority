# Codex -> Zinan/Claude: timer>=2 swap branch status

Sender: Codex
Receiver: Zinan / Claude Code
Topic: `Time.lean` remaining 3 sorrys after restoring `RankTarget = InSrank ∧ MedianTimerAtLeast 2`

## Read

- `HANDOFF/outbox/2026-05-20-codex-032-time-bound-status.md`
- `SSExactMajority/UpperBound/Time.lean` around the final 3 sorrys
- `SSExactMajority/Convergence/SwapFromRanking.lean`
- relevant `BurmanConvergenceFinal` deterministic swap/reset wrappers

## Current precise blocker

The current Phase-B theorem is:

```lean
PEM_swap_ProbHitWithin_InSswap
  (hSrank : InSrank C) (hTimer : MedianTimerAtLeast 2 C) :
  (4 : ENNReal)^-1 <= ProbHitWithin P C InSswap (4*n*n)
```

The already proved stochastic theorem is only:

```lean
PEM_swap_ProbHitWithin_or_exit :
  (2 : ENNReal)^-1 <=
    ProbHitWithin P C (fun D => InSswap D ∨ ¬ InSrank D) (4*n*n)
```

This comes from:

```lean
PEM_swap_phase_expected_until_swap_or_exit_le_sum
```

and that proof deliberately uses `Goal := InSswap ∨ ¬ InSrank`, because arbitrary
PEM steps may leave `InSrank`.

Restoring `MedianTimerAtLeast 2` is enough for the deterministic `SwapInv`
path:

```lean
swap_reaches_Sswap_from_timer_bound
```

but the available stochastic descent infrastructure needs either:

1. an all-step invariant lemma, e.g.

```lean
SwapInv C -> ¬ InSswap C ->
  ∀ i j, SwapInv (C.step P i j) ∨ InSswap (C.step P i j)
```

plus nonincrease of the chosen potential under all arbitrary steps; or

2. a quantitative exit bound:

```lean
ProbHitWithin P C (fun D => ¬ InSrank D) (4*n*n) <= (4 : ENNReal)^-1
```

or an equivalent `¬ SwapInv` bound, so `ProbHitWithin_union_le` can subtract the
exit branch.

I did not find either lemma already packaged in `Time.lean`, `ExpectedTime.lean`,
or the imported convergence files.

## Why `timer>=2` alone is not immediately enough

The deterministic `SwapInv` proof is existential: it supplies a good pair that
preserves `SwapInv` and decreases `misorderedCount`. It does not show arbitrary
random scheduler steps preserve `SwapInv`. The variable-descent theorem
`expectedHittingTime_le_of_variable_descent_until_goal` requires all-step
invariant/nonincrease hypotheses, so the deterministic path theorem cannot be
used directly for a high-probability window.

The comment currently above `PEM_swap_ProbHitWithin_InSswap` says the exit term
is bounded by a timer-decrement Markov argument, but I do not see a formal lemma
for that bound. Also the theorem only assumes `MedianTimerAtLeast 2`, while the
comment's denominator mentions `7*(Rmax+4)`, so that comment appears to be from
the earlier stronger timer target.

## Consensus side

The consensus expected-time sorry remains blocked in the same way as outbox 032:

```lean
PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le
```

targets:

```lean
(InSswap ∧ MedianAnswerCorrect) ∨ ¬ (InSswap ∧ MedianTimerAtLeast 1)
```

not pure decision. The reset-seed propagation lemmas give one-step descent facts,
but I did not find an expected-time theorem from `CorrectResetSeed` to
`IsConsensusConfig` that can close the exit branch.

## Suggested next theorem to add

The most local useful theorem for Phase B is probably:

```lean
theorem PEM_swap_exit_prob_le_quarter_of_median_timer_ge_two
  ...
  (hSrank : InSrank C) (hTimer : MedianTimerAtLeast 2 C) :
    ProbHitWithin P C (fun D => ¬ InSrank D) (4*n*n) <= (4 : ENNReal)^-1
```

If this is false or too tight with only timer>=2, the end-to-end chain should
target `InSswap ∨ reset/ranking-exit` and thread that branch explicitly.

No lock held.
