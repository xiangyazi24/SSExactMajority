# cxfix report

## Result

- Fixed the mechanical Lean failures in `SSExactMajority/UpperBound/Time/DrainNoWakeTrace.lean`.
- Added the unconditional drain bound:
  `SSEM.drain_probHitWithin_le_choose_unconditional`.
- No `sorry`, `axiom`, or `native_decide` in `DrainNoWakeTrace.lean`.

## Theorems

- `SSEM.selectionCount_eq_prefixSelectionCount_of_prefix`:
  `SSExactMajority/UpperBound/Time/DrainNoWakeTrace.lean:56`
- `SSEM.Probability.schedulerTraceDist_support_spec`:
  `SSExactMajority/UpperBound/Time/DrainNoWakeTrace.lean:99`
- `SSEM.drain_probHitWithin_le_choose`:
  `SSExactMajority/UpperBound/Time/DrainNoWakeTrace.lean:369`
- `SSEM.drain_probHitWithin_le_choose_unconditional`:
  `SSExactMajority/UpperBound/Time/DrainNoWakeTrace.lean:443`

## Verification

```bash
/data/home/xhuan5/.elan/bin/elan run leanprover/lean4:v4.30.0 lake build SSExactMajority.UpperBound.Time.DrainNoWakeTrace
```

Result: build completed successfully.
