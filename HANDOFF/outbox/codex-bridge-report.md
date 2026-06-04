# codex-bridge report

Implemented `SSExactMajority/Probability/SchedulerBridge.lean`.

Main construction:

- `schedulerPrefixSnocPMF`: recursive prefix product PMF, appending one iid
  `uniformPair` by `Fin.snoc`.
- `schedulerPrefixSnocPMF_eq_schedulerPrefixPMF`: proves this recursive PMF is
  exactly the existing product `schedulerPrefixPMF` from `SelectionCount`.
- `schedulerTraceDist`: coupled finite-prefix process carrying
  `(Config × hitFlag) × SchedulerPrefix`.
- `schedulerTraceDist_map_hitFlag`: first projection is the existing
  `hitFlagDist`, hence the `ProbHitWithin` execution measure.
- `schedulerTraceDist_map_prefix`: second projection is `schedulerPrefixPMF`;
  this is the sigma-marginal bridge.

Usable bounds:

- `ProbHitWithin_le_schedulerPrefix_high_load`:
  if every coupled trace with hit flag true has `PrefixHighLoad` on its tracked
  scheduler prefix, then
  `ProbHitWithin ≤ schedulerPrefixPMF[PrefixHighLoad]`.
- `ProbHitWithin_le_schedulerPrefix_high_load_choose`: composes the bridge with
  the existing `prefix_high_load_mass_le_union_choose`.
- `disruption_ProbHitWithin_le_choose`: named wrapper for the disruption-tail
  use case, with certificate
  `∀ S : SchedulerTraceState Q X n K, S.1.2 = true → PrefixHighLoad S.2 r`.

Verification:

- Generated the missing local dependency olean for `SelectionCount` with
  `lake env lean -R . -o .lake/build/lib/lean/SSExactMajority/Probability/SelectionCount.olean -i .lake/build/lib/lean/SSExactMajority/Probability/SelectionCount.ilean SSExactMajority/Probability/SelectionCount.lean`.
- Checked the new file with
  `lake env lean SSExactMajority/Probability/SchedulerBridge.lean`.
- Text check found no forbidden proof placeholders in `SchedulerBridge.lean`.

No obstruction for the bridge itself.  The remaining protocol-specific step is
to instantiate the coupled-trace certificate from the concrete disruption
predicate/certificate used by the renewal layer.
