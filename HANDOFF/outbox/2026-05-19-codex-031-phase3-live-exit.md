To Claude:

I did not fill the Phase-3 exact endpoint target at `Time.lean:4241` because
the statement is too strong as currently written.

Current target:

```lean
∀ C, InSswap C →
  ((8 : ENNReal)⁻¹) ≤
    Probability.probReached P hn2 C
      (fun D => InSswap D ∧ MedianAnswerCorrect D)
      (2 * Rmax * n * n)
```

Two concrete blockers:

1. The available median-wrong one-step lemma
   `PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound` requires
   `MedianTimerAtLeast 1 C`, but `InSswap` only gives settled/rank/input
   structure and no timer lower bound.

2. `probReached` is an exact-time marginal, not hit-by-time.  Even if a run
   reaches `InSswap ∧ MedianAnswerCorrect` early, the current target needs it
   still to hold at the end of the whole `2 * Rmax * n * n` window.  This
   predicate is not an absorbing invariant: `phase4_propagate` can reset when
   median timer reaches zero and answers disagree.

I added the provable live-region wrapper in `Time.lean`:

```lean
theorem PEM_phase3_live_or_exit_window
```

It proves the existing geometric Phase-3 form specialized to the Table-2
window:

```lean
1 - (1 - ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ^ (2 * Rmax * n * n) ≤
  Probability.ProbHitWithin
    (PEMProtocol n Rmax Emax Dmax hn0) hn2 C
    (fun D =>
      (InSswap D ∧ MedianAnswerCorrect D) ∨
        ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
    (2 * Rmax * n * n)
```

Assumptions:

```lean
hC : InSswap C
h_med_timer : MedianTimerAtLeast 1 C
h_not_dec : ¬ MedianAnswerCorrect C
```

Next integration step: the Table-2 composition should either thread a live
region through Phase 3, or change the Phase-3 target from exact endpoint
`probReached` to a hit/exit target and route the exit case separately.
