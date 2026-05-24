# Time-Bound Plan A: Probability Foundation

## 1. Probability Foundation Choice

Recommendation: use the `PMF` path for the first formalization pass.

The current project needs finite-prefix distributions, closed-form
waiting-time bounds, and a lightweight definition of expected hitting
time.  `PMF` matches that shape directly:

- `PMF.uniformOfFinset` from `Mathlib.Probability.Distributions.Uniform`
  gives the one-step uniform scheduler over off-diagonal ordered pairs.
- `PMF.map` and `PMF.bind` from
  `Mathlib.Probability.ProbabilityMassFunction.Constructions` /
  `Monad` compose one-step transition distributions.
- `PMF.map_apply`, `PMF.bind_apply`, `PMF.pure_apply`, and
  `PMF.uniformOfFinset_apply` are the concrete expansion lemmas needed
  for later finite-sum calculations.
- `PMF.toMeasure`, `PMF.integral_eq_tsum`, and `PMF.integral_eq_sum`
  remain available if a later proof needs to bridge into measure
  notation.

The kernel path is mathematically natural but too heavy for this layer.
Mathlib has `ProbabilityTheory.Kernel`, Ionescu-Tulcea trajectory
machinery, and process/stopping-time files such as
`MeasureTheory.hittingAfter` and `MeasureTheory.IsStoppingTime`.  That
would be the right choice for a reusable Markov-chain library, but here
the state space is discrete and the immediate estimates are geometric
waiting-time estimates over finite prefixes.

Use `Kernel` later only if the high-probability API truly needs infinite
trajectory measures.  The expected-time definitions should stay `PMF`
based.

## 2. Expected Hitting Time Definition

Use a lifted Markov chain on `Config × Bool`, where the boolean remembers
whether the goal has appeared on the finite prefix.  This avoids building
an infinite schedule-stream measure just to define expected hitting time.

Implemented shape:

```lean
noncomputable def hitFlagStepDist
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop)
    (S : Config Q X n × Bool) : PMF (Config Q X n × Bool) := by
  classical
  exact
    (stepDist P hn S.1).map
      (fun C' => (C', S.2 || decide (Goal C')))

noncomputable def hitFlagDist
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) :
    ℕ → PMF (Config Q X n × Bool)
  | 0 => by
      classical
      exact PMF.pure (C₀, decide (Goal C₀))
  | t + 1 => (hitFlagDist P hn C₀ Goal t).bind
      (hitFlagStepDist P hn Goal)

noncomputable def probNotHitBy
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) : ENNReal :=
  ∑' S : Config Q X n × Bool,
    if S.2 = false then (hitFlagDist P hn C₀ Goal t) S else 0

noncomputable def probHitBy
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) : ENNReal :=
  ∑' S : Config Q X n × Bool,
    if S.2 = true then (hitFlagDist P hn C₀ Goal t) S else 0

def reachesGoalAlmostSurely
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) : Prop :=
  (⨆ t : ℕ, probHitBy P hn C₀ Goal t) = 1

def hitsGoalByWithFailureAtMost
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) (ε : ENNReal) : Prop :=
  probNotHitBy P hn C₀ Goal t ≤ ε

noncomputable def expectedHittingTime
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) : ENNReal :=
  ∑' t : ℕ, probNotHitBy P hn C₀ Goal t
```

This is the standard tail-sum form for a nonnegative integer-valued
stopping time: `E[T] = ∑ t, P[T > t]`.  The value may be `⊤`, which is
the right result when the goal is not hit with sufficient probability.
The companion `probHitBy` supports almost-sure reachability as
`⨆ t, P[T ≤ t] = 1`, and `hitsGoalByWithFailureAtMost` is the intended
finite-time API for later high-probability claims.

## 3. Parallel Time

Keep:

```lean
noncomputable def parallelTime (T : ENNReal) (n : ℕ) : ENNReal :=
  T / n
```

Kanaya §2 defines parallel time as sequential interactions divided by
`n`.  On `ENNReal`, `⊤ / n = ⊤` for positive `n`, which correctly says
an infinite expected sequential hitting time remains infinite in
parallel rounds.  All theorem statements should carry `hn : 2 ≤ n`, so
division by zero is not a meaningful case for this project.

## 4. Statement Style

Use explicit closed-form statements first, not `Asymptotics.IsBigO`.

The paper's time bounds are quantitative:

- Theorem 3 expected lower bound: Ω(n) parallel time.
- Theorem 3 high-probability lower bound: Ω(n log n) parallel time.
- Theorem 4 / §5.2 expected upper bound: O(n) parallel time.
- Theorem 4 / §5.2 high-probability upper bound: O(n log n) parallel
  time.

The current Lean scaffold has an expected-time API but not yet a
tail-probability API.  Therefore the first Lean targets should be:

```lean
theorem time_lower_bound_omega_n_expected : ... := by
  -- real proof, no statement-definition substitute

theorem PEM_expected_parallel_time_linear_param : ... := by
  -- real proof, no statement-definition substitute
```

Add high-probability targets only after a `probNotHitBy`/tail statement
style is fixed.  `Asymptotics.IsBigO` and `IsOmega` corollaries can be
added after the explicit inequalities compile.
