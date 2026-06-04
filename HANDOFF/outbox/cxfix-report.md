# cxfix report

## Result

- Added `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean`.
- Defined the faithful `[12]` reset-completion contract targeting a fresh reset seed, not `EpidemicPhiGoal`.
- Proved the faithful reset-to-phi-goal composition over `PEMProtocol n 1` by chaining `freshSeedReach` with `answer_epidemic_bridge_from_fresh_resetting` via `Probability.ProbHitWithin_add_ge_mul`.
- No `sorry`, `axiom`, or `native_decide` in `OptimalWindowsFaithful.lean`.

## Theorems

- `SSEM.FreshResetSeedTarget`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:11`
- `SSEM.CRSReset12Faithful`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:21`
- `SSEM.faithful_reset_to_phiGoal`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:38`

## Verification

```bash
/data/home/xhuan5/.elan/bin/elan run leanprover/lean4:v4.30.0 lake build SSExactMajority.UpperBound.Time.OptimalWindowsFaithful
```

Result: build completed successfully.

## Capstone Result

- Appended the faithful capstone bridge to `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean`.
- Added import `SSExactMajority.UpperBound.Time.GenericKeystone`.
- Proved `SSEM.crsReset12Faithful_to_generic`, constructing
  `CRSResetCompletion12Generic (trank := 1)` from the faithful fresh-reset
  contract plus the proven answer-epidemic bridge, using
  `Probability.ProbHitWithin_mono_goal` to drop the `AllAgentsResetting`
  conjunct.
- Proved `SSEM.PEM_expectedParallelTime_On_faithful` by calling the existing
  `PEM_expectedParallelTime_On` with reset probability `p_reset * (pE / 2)`
  and window `K_reset + K_bridge`.
- No `sorry`, `axiom`, or `native_decide` in `OptimalWindowsFaithful.lean`.

## Capstone Theorems

- `SSEM.FreshResetSeedTarget`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:12`
- `SSEM.CRSReset12Faithful`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:22`
- `SSEM.faithful_reset_to_phiGoal`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:39`
- `SSEM.crsReset12Faithful_to_generic`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:87`
- `SSEM.PEM_expectedParallelTime_On_faithful`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:162`

## Capstone Verification

```bash
/data/home/xhuan5/.elan/bin/elan run leanprover/lean4:v4.30.0 lake build SSExactMajority.UpperBound.Time.OptimalWindowsFaithful
```

Result: build completed successfully.

O(n) status: yes, genuinely O(n). The theorem reuses the generic renewal
machinery with global window
`OW_globalWindow n C_rank PEM_trank1_timer (K_reset + K_bridge) T_rank T_rerank`;
the reset and bridge windows are both assumed quadratic, and the final bound is
that window divided by `n`. The probability factor
`(p_reset * (pE / 2)) * 128⁻¹` is a positive constant under
`h12reset.resetProb_pos` and `hpE_pos`.

## Drain-Tail Result

- Added `SSExactMajority/UpperBound/Time/DrainTailBound.lean`.
- Proved the closed-form drain-tail bound using `Nat.choose_le_pow_div`
  and `Stirling.le_factorial_stirling`.
- Final constant: `11`, from `4 * Real.exp 1 < 11`.
- No `sorry`, `axiom`, or `native_decide` in `DrainTailBound.lean`.

## Drain-Tail Theorems

- `SSEM.drainNoWakeTail_le_geom`:
  `SSExactMajority/UpperBound/Time/DrainTailBound.lean:139`
- `SSEM.drainNoWakeTail_le_geom_at_Dmax_ge_n`:
  `SSExactMajority/UpperBound/Time/DrainTailBound.lean:162`

## Drain-Tail Verification

```bash
/data/home/xhuan5/.elan/bin/elan run leanprover/lean4:v4.30.0 lake build SSExactMajority.UpperBound.Time.DrainTailBound
```

Result: build completed successfully.

Asymptotic-to-zero status: not included as a separate topological eventual
theorem. The delivered corollary is the spec-minimum closed form:
when `Dmax >= n`, `drainNoWakeTail n K Dmax <= n * (1/2)^n`.
