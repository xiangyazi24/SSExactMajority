# codex-wire report (2026-06-04)

Implemented `CRS_to_silence_faithful` in
`SSExactMajority/UpperBound/Time/OptimalWindows.lean`.

## What changed

- Added import of `SSExactMajority.UpperBound.Time.EpidemicMechanics`.
- Added `epidemicRegion_phiCount_lt` and
  `epidemic_coupon_sum_le_quadratic`, giving the coarse
  `n*n*(n-1)` coupon bound for the epidemic sum.
- Added `CRSResetDuration12`, a cited [12] reset-duration contract carrying:
  - `CorrectResetSeed` entry into `EpidemicRegion (majorityAnswer C) C`;
  - reset-window no-Phase4/no-wake guard for arbitrary steps;
  - post-step all-Resetting guard;
  - rankDelta endpoint-stays-Resetting guard for scheduled
    `(phi, non-phi)` pairs;
  - the reset-window Markov inequality for the proved coupon budget.
- Proved `CRS_to_silence_faithful` by instantiating
  `CRS_to_silence_of_rank12` with `Inv := EpidemicRegion`.

## Epidemic hypotheses discharged

- `hAnsInv`: `epidemicRegion_answerInv`.
- `hInvStep`: `epidemicRegion_step_closed`, using the [12] no-Phase4 guard
  and post-step all-Resetting guard.
- `hNonincrease`: `epidemicRegion_phiCount_nonincrease`, using the [12]
  no-Phase4 guard.
- `hGood`: `epidemicRegion_phiPair_descent` plus
  `epidemicRegion_step_closed`, using the [12] rankDelta
  stay-Resetting guard for the scheduled good pair.
- `hEpidemicSum`: `epidemic_coupon_sum_le_quadratic`.  The lemma first uses
  the non-`phi` carrier in `EpidemicRegion` to show `phiCount C < n`, so the
  terminal `k=n` inverse-rate term never appears.

## Note on `hResetInv`

The raw Lean definition of `CorrectResetSeed` does not imply
`EpidemicRegion (majorityAnswer C) C`: it gives one Resetting seed and
constraints on agents already in `.Resetting`, but it does not say every
agent is `.Resetting`. Therefore the all-Resetting epidemic entry fact has
to be part of the cited [12] reset-duration contract (or replaced by a
separate proved probabilistic CRS-to-all-Resetting bridge).

## Verification

Ran:

```bash
lake env lean -R . -o .lake/build/lib/lean/SSExactMajority/UpperBound/Time/EpidemicMechanics.olean -i .lake/build/lib/lean/SSExactMajority/UpperBound/Time/EpidemicMechanics.ilean SSExactMajority/UpperBound/Time/EpidemicMechanics.lean
lake env lean SSExactMajority/UpperBound/Time/OptimalWindows.lean
```

Result: success. Remaining warnings are pre-existing in `OptimalWindows.lean`:
the existing `OW_rankBound` `sorry` and the existing unused-section-variable
warning on `decision_window`. No new `sorry`, `axiom`, `admit`, or
`native_decide` was added.
