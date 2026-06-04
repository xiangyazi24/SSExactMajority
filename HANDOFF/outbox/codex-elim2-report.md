# codex-elim2 report (2026-06-04)

Status: implementation wired, but not fully Lean-verified locally.

## Changes made

- Updated `SSExactMajority/UpperBound/Time/OptimalWindows.lean` to import:
  - `SSExactMajority.UpperBound.Time.DecisionTiming`
  - `SSExactMajority.UpperBound.Time.DrainProductive`
- Replaced the old `hRank12`-based `OW_consensusBound` with a renewal whose entry is:
  - `InSswap C`
  - `MedianTimerAtLeast 35 C`
  - timer bounded
- New `OW_consensusBound` hypotheses are [12]-only:
  - `h12resetDuration : CRSResetDuration12 ... T_reset`
  - `h12rank : EpidemicPhiGoal -> ProbHitWithin OW_rankedEpidemicEndpoint T_rank >= 1/2`
  - `h12reRank : bounded non-live35 -> ProbHitWithin live35 T_rerank >= 1/2`
- Added product-preserving CRS helpers:
  - `CRS_to_silence_of_rank12_product`
  - `CRS_to_silence_faithful_product`
  - `CRS_to_consensus_faithful_product`
- Added `MAClive_to_consensus_or_crs_window`, the Markov form of
  `MAClive_to_consensus_or_crs`.
- Rebuilt the consensus renewal:
  - live35 branch:
    `decision_before_timer_zero` (`1/4`) ->
    `MAClive_to_consensus_or_crs_window` (`1/2`) ->
    CRS-to-consensus product (`1/4`), giving `1/32`.
  - non-live35 branch:
    `h12reRank` (`1/2`) -> live35 branch, giving renewal constant `1/64`.
- Updated `PEM_expectedParallelTime_optimal` to drop `hRank12` and thread:
  - `h12ranking`
  - `h12resetDuration`
  - `h12rank`
  - `h12reRank`

## Small dependency fix

`DrainProductive.lean` had local Lean errors before `OptimalWindows` could import it:

- replaced `zero_le _` with `zero_le`;
- unfolded `maxMedianTimer` before `Finset.le_sup`.

No new `sorry`, `admit`, `axiom`, or `native_decide` was added in the diff.

## Verification

Succeeded:

```bash
lake env lean -R . -o .lake/build/lib/lean/SSExactMajority/UpperBound/Time/DecisionTiming.olean -i .lake/build/lib/lean/SSExactMajority/UpperBound/Time/DecisionTiming.ilean SSExactMajority/UpperBound/Time/DecisionTiming.lean
git diff --check -- SSExactMajority/UpperBound/Time/OptimalWindows.lean SSExactMajority/UpperBound/Time/DrainProductive.lean
```

Blocked:

```bash
lake env lean -R . -o .lake/build/lib/lean/SSExactMajority/UpperBound/Time/DrainProductive.olean -i .lake/build/lib/lean/SSExactMajority/UpperBound/Time/DrainProductive.ilean SSExactMajority/UpperBound/Time/DrainProductive.lean
```

This ran for about 10 minutes with the Lean process still consuming CPU and no error output; I killed it to avoid leaving a runaway local check.

Consequently:

```bash
lake env lean SSExactMajority/UpperBound/Time/OptimalWindows.lean
```

currently stops at:

```text
error: object file '.lake/build/lib/lean/SSExactMajority/UpperBound/Time/DrainProductive.olean'
of module SSExactMajority.UpperBound.Time.DrainProductive does not exist
```

I did not get a final `OptimalWindows.lean` proof check because the new
`DrainProductive` import could not be materialized locally within the run.
