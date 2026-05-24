# Time-Bound Plan B: Lower Bound

## Source Check

Kanaya et al. Theorem 3 states two claims for silent self-stabilizing exact
majority:

- expected parallel stabilization time is `Ω(n)`;
- parallel stabilization time is `Ω(n log n)` with high probability.

The expected part follows from the stated two-agent waiting argument.  The
high-probability part needs extra care: the displayed calculation in the
paper shows that a fixed pair does **not** interact for
`α * n * (n - 1) / 2 * log n - 1` sequential interactions with probability
larger than `n^{-α}`.  That is a polynomially small lower-tail event, not a
`1 - O(1/n)` event.  As written, the one-pair argument proves the expected
lower bound cleanly but does not by itself prove the standard whp lower
bound.

Formalization policy: prove the expected lower bound first.  Do not state
the whp theorem as closed until either the paper argument is repaired by an
amplification step or the intended meaning of "whp lower bound" is clarified.

## Geometric Waiting Lemma

For `n ≥ 2`, the scheduler samples ordered off-diagonal pairs uniformly from
`OffDiagonalPairs n`, whose cardinality is `n * (n - 1)`.

For a fixed unordered pair `{u, w}` with `u ≠ w`, the success probability per
sequential interaction is

```text
p = 2 / (n * (n - 1))
```

because the ordered samples `(u, w)` and `(w, u)` both count.  If `T` is the
number of sequential interactions until the first success, then

```text
Pr[T > t] = (1 - p)^t
E[T] = sum_t Pr[T > t] = 1 / p = n * (n - 1) / 2.
```

After dividing by `n`, this is `(n - 1) / 2 = Ω(n)` expected parallel time.

Lean target, standalone:

```lean
theorem geometric_wait_expected_ordered_offdiag_pair
    {n : ℕ} (hn : 2 ≤ n) {u w : Fin n} (huw : u ≠ w) :
    -- first-hit expected sequential time for `(u,w) ∨ (w,u)`
    -- equals `(n * (n - 1) : ENNReal) / 2`
    ...
```

The first concrete scheduler lemmas are now in
`SSExactMajority.Probability.RandomScheduler`:

```lean
mem_offDiagonalPairs
uniformPair_apply_of_ne
uniformPair_apply_self
uniformPair_apply_pair_add_swap_of_ne
```

The unordered-pair mass is stated in multiplication form:

```lean
theorem uniformPair_apply_pair_add_swap_of_ne
    (n : ℕ) (hn : 2 ≤ n) {u w : Fin n} (huw : u ≠ w) :
    uniformPair n hn (u, w) + uniformPair n hn (w, u) =
      (2 : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹
```

## Mathlib Status

Verified locally by grepping the vendored Mathlib:

- `Mathlib.Probability.Distributions.Geometric` defines
  `ProbabilityTheory.geometricPMFReal`, `geometricPMF`, and
  `geometricMeasure`.
- That file proves normalization and positivity, but not the expectation
  or tail formulas needed here.
- `Mathlib.Probability.Process.HittingTime` defines
  `MeasureTheory.hittingBtwn`, `hittingAfter`, and stopping-time lemmas,
  but this is measure/process infrastructure, not a ready PMF geometric
  waiting-time bound.

Conclusion: use the existing PMF/geometric definitions only as reference.
For the current finite scheduler API, prove a standalone tail-sum lemma over
`ENNReal` or keep the theorem statement in terms of `probNotHitBy` until the
closed-form series facts are needed.

## Lift to Theorem 3

Expected lower-bound route:

1. Start from the paper's odd population with `|V| ≥ 5`, `|V| mod 2 = 1`,
   `|Va| = floor(n / 2)`, and `|Vb| = ceil(n / 2)`.
2. Use the space-lower-bound machinery, ultimately Lemma 4's distinct-state
   fact, to obtain distinct silent A-states.
3. Pick an A-agent `w` with silent state `sA` and a B-agent `u`.
4. Modify `u` to carry `(sA, A)`.  The modified configuration has majority
   A but all outputs are still B, so it is not safe.
5. Silence of the original configuration implies no repair-relevant state can
   change before `u` and `w` interact.
6. Apply the two-agent waiting lemma.  Sequential expected wait is
   `n * (n - 1) / 2`; parallel expected wait is `(n - 1) / 2`.

The Lean theorem currently stated in `LowerBound/Time.lean` targets only this
expected part:

```lean
time_lower_bound_omega_n_expected
```

## Open Gaps

- Need a Lean version of Lemma 4 as a reusable theorem, not only the final
  `SSEM.space_lower_bound`.
- Need the exact "modified unsafe configuration" construction over the
  generic `Config Q Opinion n`.
- Need the geometric expected-wait theorem for a two-element success set under
  `uniformPair`.
- The whp part is mathematically blocked unless an amplification argument is
  supplied.  The current paper text's one-pair calculation gives probability
  `n^{-α}` for the long wait, not `1 - O(1/n)`.
