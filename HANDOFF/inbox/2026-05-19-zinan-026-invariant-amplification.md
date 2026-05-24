---
sender: zinan
receiver: codex
topic: Close the invariant amplification sorry in ExpectedTime.lean
status: open
---

# Task

Close the sorry at `SSExactMajority/Probability/ExpectedTime.lean:2053`.

```lean
theorem expectedHittingTime_le_window_mul_inv_of_invariant
    ...
    (hwin : ∀ C, Inv C → ¬ Goal C → p ≤ ProbHitWithin P hn C Goal K) :
    expectedHittingTime P hn C₀ Goal ≤ (K : ENNReal) * p⁻¹ := by
  apply expectedHittingTime_le_window_mul_inv P hn C₀ Goal K p hp_le_one
  intro C hGoal
  by_cases hInvC : Inv C
  · exact hwin C hInvC hGoal
  · sorry  -- THIS sorry
```

## Why it's stuck

`expectedHittingTime_le_window_mul_inv` requires `∀ C, ¬ Goal C → p ≤ ProbHitWithin ...`
universally. For non-Inv C, we can't guarantee the window. So the reduction
to the non-invariant version doesn't work.

## Solution

Don't use `expectedHittingTime_le_window_mul_inv`. Instead, duplicate the
proof chain with Inv threaded through. The chain is:

1. `probNotHitBy_add_window_le_mul` (line 990) — the KEY lemma
2. `probNotHitBy_mul_window_le_initial_mul_pow` (line 1045) — induction
3. `expectedHittingTime_le_window_mul_tsum_pow_of_not_goal` (line 1693) — tail sum
4. `expectedHittingTime_le_window_mul_inv` (line 1735) — geometric sum

Only #1 needs modification. In its tsum (lines 1001-1029), at line 1024:
```lean
  hwin C hGoalC
```
becomes:
```lean
  hwin C hInvC hGoalC
```
where `hInvC` is obtained from:
- `hitFlagDistFrom ... (C, false) > 0`
- → `hitFlagDist ... (C, false) > 0` (by `hitFlagDist_eq_hitFlagDistFrom`)
- → `(C, false) ∈ support (hitFlagDist ...)`
- → `Inv C` (by `hitFlagDist_support_inv`, already proved)

For the non-Inv case (weight = 0): the term is `0 * anything = 0 ≤ 0`.

## Concrete plan

1. Add `probNotHitBy_add_window_le_mul_of_invariant`:
   Copy `probNotHitBy_add_window_le_mul` (lines 990-1041).
   Add `Inv`, `hInv₀`, `hInvStep` parameters.
   At line 1021-1027: replace with `by_cases hInvC : Inv C`:
   - Inv: use `hwin C hInvC hGoalC`
   - Not Inv: show `hitFlagDistFrom ... (C, false) = 0`, then `rw [hzero]; simp`

   To show `hitFlagDistFrom ... (C, false) = 0`: use the support fact:
   ```lean
   have : ¬ ((C, false) ∈ (hitFlagDist P hn C₀ Goal t).support) := by
     intro hmem; exact hInvC (hitFlagDist_support_inv ... hmem)
   rw [hitFlagDist_eq_hitFlagDistFrom] at this
   exact PMF.not_mem_support_iff.mp this
   ```

2. Add `probNotHitBy_mul_window_le_initial_mul_pow_of_invariant`:
   Same as original but call #1 instead. Mechanically identical.

3. Replace the sorry in `expectedHittingTime_le_window_mul_inv_of_invariant`:
   ```lean
   by_cases hGoal : Goal C₀
   · rw [expectedHittingTime_eq_zero_of_goal ...]; exact zero_le _
   · calc expectedHittingTime ...
       ≤ K * Σ (1-p)^r := by
           use probNotHitBy_mul_window_le_initial_mul_pow_of_invariant ...
       _ = K * p⁻¹ := by rw [tsum_geometric, sub_sub_cancel ...]
   ```

## Build

```
scp ExpectedTime.lean uisai1:repos/SSExactMajority/SSExactMajority/Probability/ExpectedTime.lean
ssh uisai1 'rm -f repos/SSExactMajority/.lake/build/lib/lean/SSExactMajority/Probability/ExpectedTime.olean ...; cd repos/SSExactMajority && PATH=$HOME/.elan/bin:$PATH lake build SSExactMajority.Probability.ExpectedTime'
```

## File

Edit `SSExactMajority/Probability/ExpectedTime.lean` directly. I am NOT editing it.
