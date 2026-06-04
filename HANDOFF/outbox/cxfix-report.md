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
