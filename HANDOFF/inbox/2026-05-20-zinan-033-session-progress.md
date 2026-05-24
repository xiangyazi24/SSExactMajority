# Session Progress — 2026-05-20

## Achievements

### Infrastructure proved (0 sorry)
- **ProbHitWithin_union_le** (ExpectedTime.lean): P(hit A∨B, t) ≤ P(hit A, t) + P(hit B, t)
  Proof: hitTwoFlagDist map_or/left/right + PMF.toOuterMeasure + pointwise indicator bound.

- **ennreal_sum_inv_sq_le_two_mul_sq** (Time.lean): Σ n²/(k+1)² ≤ 2n² in ENNReal.
  Proof: Mathlib `sum_Ioo_inv_sq_le` + ENNReal toReal transfer.

- **PEM_swap_ProbHitWithin_or_exit** (Time.lean): ProbHitWithin(InSswap ∨ ¬InSrank, 4n²) ≥ 1/2.
  Proof: swap expected time + ennreal sum bound + Markov.

### Architecture completed (type-checks with sorry)
- **PEM_end_to_end_ProbHitWithin**: ProbHitWithin(consensus, (22Rmax+4)n²) ≥ 1/16 from IsInitialConfig.
  Three-phase chain via ProbHitWithin_add_ge_mul:
  Phase A: → InSrank ∧ timer≥12n (1/2 via Markov)
  Phase B: → InSswap (1/4 via union bound + exit prob)  
  Phase C: → consensus (1/2 via Markov)

### 11-point audit passed (pre-session)
- 0 sorry in all conditional composition theorems
- #print axioms: only [propext, Classical.choice, Quot.sound]
- Build clean

## Remaining 3 sorry's

### 1. PEM_ranking_expected_hitting_time (line ~6210)
```
E[T to InSrank ∧ timer≥12n from IsInitialConfig] ≤ Rmax·n²
```
Needs: ranking protocol potential descent under random scheduler.
Blocker: existing proofs are deterministic (reach_zero_potential), not probabilistic.

### 2. PEM_consensus_expected_hitting_time (line ~6253)
```
E[T to consensus from InSswap] ≤ 10·Rmax·n²
```
Needs: decision + propagation composition via strong Markov.
Blocker: decision lemma targets Goal ∨ ¬Inv; union bound can separate but needs exit prob bound.

### 3. PEM_exit_prob_le_quarter (line ~6278)
```
ProbHitWithin(¬InSrank, 4n²) ≤ 1/4 from InSrank + timer≥12n
```
Math: P(Bin(4n², 2/(n(n-1))) ≥ 12n) ≤ (8n/(n-1))/(12n) = 2/(3(n-1)) < 1/4.
Needs: Markov on binomial count → PMF.toMeasure + meas_ge_le_lintegral_div, or counter-augmented hitFlagDist.

## Key finding
All three sorry's share the same structural pattern: existing phase lemmas target `Goal ∨ ¬Invariant`, and separating Goal from ¬Inv requires bounding the exit probability. The union bound (now proved) provides the separation tool, but the exit probability bound needs Markov on counting processes in the PMF framework.
