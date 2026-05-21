# Time-Bound Plan C: Upper Bound

## Source Check

Kanaya et al. §5.2 proves the concrete protocol reaches `Sem` in
`O(n)` expected parallel time and `O(n log n)` parallel time with high
probability.  The proof is a constant-success-window argument, not a direct
global drift proof.

Paper Table 2 gives the window decomposition:

| Step | Time | Success probability |
|------|------|---------------------|
| `Call(P_EM) -> Srank` | `O(n)` | `1/10` |
| `Srank -> Tswap ∪ Stim` | `O(n)` | `1/20` |
| `Tswap -> Sdec` | `O(n)` | `1/8` |
| `Sdec -> Stim` | `O(n)` | `1/1280` |
| `Stim -> Sem` | `O(n)` | `1/2` |
| `Call(P_EM) -> Sem` | `O(n)` | `1/4096000` |

The final expected bound is the geometric-restart inequality

```text
E[T] <= C*n + (1 - p) E[T]
```

with `p = 1 / 4096000`, hence `E[T] <= 4096000*C*n`.  The whp upper bound
comes from repeating a constant-probability `O(n)` window `O(log n)` times.

## Mapping to Current Lean

Qualitative theorem names already present:

- Ranking: `ranking_field_proof`, bundled in `burmanConvergence_concrete`.
- Ranking-to-swap: `swap_reaches_Sswap_from_timer_bound_with_timer`.
- Swap/decision potential: `misorderedCount`, `wrongAnswerCount`.
- Reservoir cycle potential: `phiCount`.
- Main cycle drivers:
  `cycle_potential_reaches_consensus`, `cycle_macro_discharge`,
  `cycle_macro_discharge_tieaware`.
- Final qualitative concrete theorem: `P_EM_solves_SSEM_final`.

The current quantitative scaffold is:

```lean
PEM_expected_parallel_time_linear_param
```

in `SSExactMajority/UpperBound/Time.lean`.

## Timer / `trank = n` Issue

The paper describes a constant `trank` with `srank ≤ trank * n`, then sets
the median timer to `7 * (trank + 4)`.  In the current Lean target we use

```lean
protocolPEM n n n (rankDeltaOSSR n Emax Dmax hn)
```

and the convergence code often writes this as

```lean
protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
```

So in the literal theorem, `trank = Rmax = n`.  This is not the same
constant-`trank` asymptotic regime as the paper text.

Effect on the upper bound:

- Longer timers make "timer survives ranking/swap" events easier, not harder.
- But draining the median timer is expensive.  A single decrement needs the
  median-rank agent to interact with the max-rank agent.  That fixed unordered
  pair has probability `2 / (n * (n - 1))` per sequential interaction, so one
  decrement costs `Θ(n^2)` sequential interactions, i.e. `Θ(n)` parallel time.
- With the paper's constant `trank`, the timer value is `O(1)`, so draining
  costs `O(n^2)` sequential / `O(n)` parallel.
- With the literal Lean instantiation `protocolPEM n n n ...`, the timer value
  is `7 * (n + 4) = Θ(n)`, so the direct Kanaya timer-drain argument costs
  `Θ(n^3)` sequential / `Θ(n^2)` parallel.

Therefore the literal `protocolPEM n n n ...` theorem should **not** be stated
as `O(n)` from the Kanaya §5.2 argument alone.  Either state the theorem with
a constant/externally bounded `trank`, or add a new protocol-specific lemma
showing the `trank = n` timer does not need to drain linearly in `n`.

Recommended theorem structure:

1. Prove a parameterized theorem with an explicit timer bound:

```lean
theorem PEM_expected_parallel_time_linear_param
    {n trank Rmax Emax Dmax : ℕ}
    (hn4 : 4 ≤ n)
    (hTimer : trank ≤ Ctimer * n)
    (hRmax : n ≤ Rmax)
    (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C₀,
        expectedParallelTimeToConsensus
          (protocolPEM n trank Rmax
            (rankDeltaOSSR Rmax Emax Dmax (by omega : 0 < n)))
          (by omega : 2 ≤ n) C₀ ≤ ENNReal.ofReal (C * n)
```

2. For the current literal theorem, expose the weaker bound supplied by the
   direct Kanaya argument:

```lean
theorem ConcretePEM_expected_parallel_time_from_Kanaya_argument
    {n : ℕ} [Inhabited (Fin n × Fin n)]
    {Emax Dmax : ℕ} (hn4 : 4 ≤ n)
    (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C₀ : Config (AgentState n) Opinion n,
        Probability.expectedParallelTimeToConsensus
          (protocolPEM n n n
            (rankDeltaOSSR n Emax Dmax (by omega : 0 < n)))
          (by omega : 2 ≤ n) C₀ ≤ ENNReal.ofReal (C * n^2)
```

3. Only state an `O(n)` theorem for the literal `protocolPEM n n n ...` after
   proving a replacement for the timer-drain estimate.

## Bridging Lemma: Constant-Success Window

The cleanest quantitative bridge is not "some deterministic decreasing
step exists" by itself.  A deterministic existential step gives an expected
wait only after bounding the probability of selecting a good pair or good
finite schedule segment under the uniform scheduler.

Target statement:

```lean
def reachesGoalInWindowWithProbAtLeast
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n -> Prop)
    (t : ℕ) (p : ENNReal) : Prop :=
  p <= probHitBy P hn C₀ Goal t

theorem expectedHittingTime_le_of_window_success
    (hpos : 0 < p) (hle1 : p <= 1)
    (hwin : ∀ C, ¬ Goal C ->
      reachesGoalInWindowWithProbAtLeast P hn C Goal W p) :
    expectedHittingTime P hn C₀ Goal <= W / p := ...
```

This directly formalizes Lemma 13's restart inequality.  It avoids needing
independence between phases: the window guarantee is conditional on the
current configuration, and the Markov property comes from `PMF.bind`.

For high probability:

```lean
theorem tail_le_of_window_success
    (hwin : ∀ C, ¬ Goal C ->
      reachesGoalInWindowWithProbAtLeast P hn C Goal W p) :
    probNotHitBy P hn C₀ Goal (k * W) <= (1 - p) ^ k := ...
```

Then choose `k = ceil(log n / -log(1-p))`.

## Good-Pair Counts

The deterministic convergence proofs produce witnesses such as "there exists
a pair whose step decreases the potential."  For stochastic bounds this must
be strengthened to a count of good ordered pairs.

Local scheduler lemmas already available:

```lean
offDiagonalPairs_card
uniformPair_apply_of_ne
uniformPair_apply_pair_add_swap_of_ne
```

Needed good-pair count lemmas:

```lean
theorem prob_selects_pair_set
    (S : Finset (Fin n × Fin n))
    (hS : S ⊆ OffDiagonalPairs n) :
    -- probability that `uniformPair` lands in S is S.card / (n*(n-1))
    ...

theorem swap_good_pairs_card
    (hC : InSrank C) :
    -- if there are i misordered A/B pairs, there are 2*i^2 useful
    -- ordered interactions, matching Kanaya Lemma 7
    ...

theorem median_participation_probability
    {μ : Fin n} :
    -- probability μ participates in a sampled ordered off-diagonal pair
    -- is 2 / n
    ...
```

These are separate from the deterministic witness lemmas.  A single witness
only gives probability `1 / (n*(n-1))`; Kanaya's `O(n)` phase bounds use
many good pairs at once.

## Phase Bounds Needed

The deterministic qualitative proof should not be reused blindly as a time
proof.  Each phase needs a probabilistic wrapper.

### Phase A: Ranking

Paper input: Burman Optimal-Silent-SSR has `srank = O(n)` expected parallel
time; Markov gives completion within `2*srank` with probability at least
`1/2`.  Together with reset/timer survival, Kanaya obtains `1/10`.

Lean status: currently represented qualitatively by `ranking_field_proof` and
`burmanConvergence_concrete`.  Quantitative formalization needs a new
assumption or imported theorem:

```lean
structure QuantitativeBurmanConvergence ... where
  ranking_window :
    ∀ C₀, reachesGoalInWindowWithProbAtLeast P hn C₀ InSrank (CRank * n) (1/10)
```

Do not try to derive Burman's `O(n)` time from the existing qualitative
`ranking_field_proof`; the quantitative ranking theorem is external to this
repo.

### Phase B: Swap

Paper Lemma 7: if reset does not occur, expected parallel time from `Srank`
to `Sswap` is at most `n`, using the potential
`misorderedCount`.  If there are `i` bad A/B pairs, success probability is
`2*i^2 / (n*(n-1))`, giving a harmonic-square sum bounded by `π^2/6`.

Lean qualitative anchors:

- `misorderedCount`
- `swap_reaches_Sswap_from_timer_bound_with_timer`
- `median_wrong_step_resAns_decrease` and related single-step decrease
  lemmas in `BurmanConvergenceFinal.lean`

Quantitative target:

```lean
theorem swap_expected_sequential_le
    {C : Config (AgentState n) Opinion n}
    (hC : InSrank C) :
    expectedHittingTime P hn C InSswap <= CSwap * n^2 := ...
```

Parallel version divides by `n`, so `O(n)`.

### Phase C: Decision / Propagation

Paper Lemmas 9-12 split this into timer and propagation windows:

- `Tswap -> Sdec`: probability at least `1/8` within `3n - 1`.
- `Sdec -> Stim`: probability at least `1/1280` within `O(n)`.
- `Stim -> Sem`: probability at least `1/2` within `O(n)`.

Lean anchors:

- `wrongAnswerCount` for wrong-answer descent.
- `phiCount` for reservoir/no-phi cycle descent.
- `cycle_potential_reaches_consensus`.
- `cycle_macro_discharge_tieaware`.
- `isConsensusConfig_of_InSswap_phiCount_zero`.

Quantitative target should be a window theorem, not a deterministic schedule:

```lean
theorem decision_window_success
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C) :
    reachesGoalInWindowWithProbAtLeast P hn C IsConsensusConfig
      (CDec * n) (1 / 1280) := ...
```

## Composition

Once the phase window lemmas exist, prove one consolidated window:

```lean
theorem P_EM_sem_window_success
    {n : ℕ} [Inhabited (Fin n × Fin n)]
    {Emax Dmax : ℕ} (hn4 : 4 ≤ n)
    (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∃ W : ℕ, W <= CWindow * n ∧
      ∀ C₀ : Config (AgentState n) Opinion n,
        reachesGoalInWindowWithProbAtLeast
          (protocolPEM n n n
            (rankDeltaOSSR n Emax Dmax (by omega : 0 < n)))
          (by omega : 2 ≤ n) C₀ IsConsensusConfig W
          ((1 : ENNReal) / 4096000) := ...
```

Then `PEM_expected_parallel_time_linear_param` is proved from
`expectedHittingTime_le_of_window_success` and `parallelTime`.

## Final Theorem Shapes

Constant/parameterized version:

```lean
theorem PEM_expected_parallel_time_linear_param
    {n trank Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n)
    (hTimer : trank ≤ Ctimer * n)
    (hRmax : n ≤ Rmax)
    (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C₀ : Config (AgentState n) Opinion n,
        Probability.expectedParallelTimeToConsensus
          (protocolPEM n trank Rmax
            (rankDeltaOSSR Rmax Emax Dmax (by omega : 0 < n)))
          (by omega : 2 ≤ n) C₀ ≤ ENNReal.ofReal (C * n)
```

Literal current-protocol version from the direct Kanaya argument:

```lean
theorem ConcretePEM_expected_parallel_time_from_Kanaya_argument
    {n : ℕ} [Inhabited (Fin n × Fin n)]
    {Emax Dmax : ℕ} (hn4 : 4 ≤ n)
    (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C₀ : Config (AgentState n) Opinion n,
        Probability.expectedParallelTimeToConsensus
          (protocolPEM n n n
            (rankDeltaOSSR n Emax Dmax (by omega : 0 < n)))
          (by omega : 2 ≤ n) C₀ ≤ ENNReal.ofReal (C * n^2)
```

The `O(n)` theorem for this exact instantiation requires an extra lemma:

```lean
theorem concrete_timer_zero_window_linear
    {n : ℕ} [Inhabited (Fin n × Fin n)]
    {Emax Dmax : ℕ} (hn4 : 4 ≤ n) :
    ∃ K : ℕ, ∃ p : ENNReal, 0 < p ∧ p ≤ 1 ∧
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        Probability.reachesGoalInWindowWithProbAtLeast
          (protocolPEM n n n
            (rankDeltaOSSR n Emax Dmax (by omega : 0 < n)))
          (by omega : 2 ≤ n) C IsConsensusConfig
          (K * n * n) p
```

High-probability version should be stated through `hitsGoalByWithFailureAtMost`:

```lean
theorem P_EM_parallel_time_upper_bound_whp
    ... :
    ∃ C : ℕ, ∀ C₀,
      Probability.hitsGoalByWithFailureAtMost P hn C₀ IsConsensusConfig
        (C * n * Nat.ceil (Real.log n)) ((1 : ENNReal) / n)
```

The exact integer/log wrapper can be adjusted after the repeated-window lemma
is formalized.

## Implementation Checklist

1. Prove finite probability algebra for `probHitBy` and `probNotHitBy`:
   complement, monotonicity in time, and Markov/window composition.
2. Prove `prob_selects_pair_set` for `uniformPair`.
3. Prove good-pair count lemmas for swap, median participation, and reset
   seed interactions.
4. Add the constant-success window lemmas:
   `expectedHittingTime_le_of_window_success` and
   `tail_le_of_window_success`.
5. Introduce `QuantitativeBurmanConvergence` as an assumption layer for
   Burman's ranking protocol.  The existing `ranking_field_proof` is
   qualitative and cannot supply expected-time constants by itself.
6. Prove phase window lemmas, then compose them into
   `P_EM_sem_window_success`.
7. Derive expected and high-probability final theorems.

## Mathlib Gaps

- No ready theorem for expectation/tail of repeated constant-success
  windows over the current `PMF` finite-prefix API.
- Need `probHitBy`/`probNotHitBy` monotonicity and complement lemmas.
- Need finite-prefix Markov-property lemmas for `hitFlagDist`.
- Need closed-form finite scheduler probabilities for one pair and for an
  agent participating in any interaction.  The ordered-pair and unordered-pair
  mass lemmas have started in `RandomScheduler.lean`.
- Quantitative Burman ranking must be imported as an assumption/theorem; it
  is not contained in the existing qualitative proof.
