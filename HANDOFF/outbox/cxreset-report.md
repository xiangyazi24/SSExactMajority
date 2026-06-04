# Faithful reset re-architecture report

## Scope

Step 3 is completed in `SSExactMajority/UpperBound/Time/OptimalWindows.lean`.
`GenericTrank.lean` was not touched.

The old reset-duration contract is no longer a keystone hypothesis.  The reset
branch now consumes `CRSResetCompletion12`, whose reset entry is a cited
`ProbHitWithin` reachability statement from `CorrectResetSeed` to
`ResetCompletionTarget12`/`EpidemicRegion`, with a quadratic sequential window
and positive constant probability.

## Old vs new

Old path:

```text
CorrectResetSeed
  -- deterministic resetInv -->
EpidemicRegion
  -- cubic resetWindow / coupon bound -->
EpidemicPhiGoal
  -- ranking -->
silence / consensus
```

That path was vacuous/too strong because the deterministic
`CorrectResetSeed -> EpidemicRegion` invariant was not a [12] reset-completion
fact, and because the old reset window forced a cubic sequential contribution.

New path:

```text
CorrectResetSeed
  -- CRSResetCompletion12.resetReach, ProbHitWithin, K_reset <= C_reset*n*n -->
ResetCompletionTarget12 (majorityAnswer C) = EpidemicRegion (majorityAnswer C)
  -- resetCompletion_to_phiGoal_window, ProbHitWithin, 2*n*n -->
EpidemicPhiGoal (majorityAnswer C)
  -- h12rank -->
OW_silenceEndpoint / IsConsensusConfig
```

Evidence:

- `OW_answerEpidemicWindow n = 2*n*n`:
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:58`.
- The live/reset contribution is now
  `K_reset + OW_answerEpidemicWindow n + T_rank`, not the old cubic reset
  window: `SSExactMajority/UpperBound/Time/OptimalWindows.lean:64-65`.
- `OW_globalWindow` uses ranking plus this live/reset window:
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:73-75`.
- The sharper epidemic coupon bound is now
  `epidemic_coupon_sum_le_nsq`:
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:224`.
- `CRSResetCompletion12` carries `0 < p_reset`, `p_reset <= 1`,
  `K_reset <= C_reset*n*n`, and the cited reset `ProbHitWithin` field:
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:353-390`.
- `resetCompletion_to_phiGoal_window` proves the post-reset answer epidemic
  window with probability at least `1/2` in `2*n*n` interactions:
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:395-453`.

## Composition verdict

The reach-then-within composition lemma exists and composes cleanly:
`Probability.ProbHitWithin_add_ge_mul`.

It is used for the reset branch as:

- `CorrectResetSeed -> ResetCompletionTarget12 -> EpidemicPhiGoal`:
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:507-512`.
- `EpidemicPhiGoal -> OW_silenceEndpoint`:
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:529-534`.

Downstream uses also compose cleanly:

- decision/MAC/reset-to-consensus in `OW_consensusBound`:
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:1102-1117`.
- rerank/live-to-consensus in `OW_consensusBound`:
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:1179-1181`.
- decision/MAC/reset-to-consensus in `PEM_expectedParallelTime_optimal`:
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:1419-1434`.
- initial ranking/rerank/live-to-consensus in
  `PEM_expectedParallelTime_optimal`:
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:1500-1515`.

## Keystone verdict

The keystone is now non-vacuous relative to the cited hypotheses.

- `CRS_to_silence_faithful_product` consumes `CRSResetCompletion12`, not the
  old deterministic reset-duration package:
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:459-534`.
- `CRS_to_silence_faithful` is the caller-chosen probability wrapper over that
  product theorem:
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:538-566`.
- The consensus wrappers consume the same faithful reset completion contract:
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:571-659`.
- `OW_consensusBound` takes `CRSResetCompletion12` as its reset hypothesis and
  has renewal success `p_reset * 64^-1`:
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:906-1198`.
- `PEM_expectedParallelTime_optimal` takes `CRSResetCompletion12` as its reset
  hypothesis and has global success `p_reset * 128^-1`:
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:1204-1531`.

The remaining [12]-style hypotheses are all satisfiable-shaped cited
probability/expectation windows: initial ranking, rerank entry, reset
completion, and post-epidemic ranking.  The false forall-invariant reset entry
is gone, so the theorem is no longer vacuous for that reason.  With
`K_reset <= C_reset*n*n` and `OW_answerEpidemicWindow n = 2*n*n`, the reset
branch contributes `O(n^2)` sequential interactions, hence `O(n)` parallel
time after division by `n`.

## Removed old contract from the keystone

The following names/patterns are absent from
`SSExactMajority/UpperBound/Time/OptimalWindows.lean` after the rewrite:

- `CRSResetDuration12`
- `resetInv`
- the old cubic `2 * (n * n * (n - 1))` reset window
- `OW_consensusExpectedSteps`
- `crs_to_allR_or_break_window`
- `hResetInv`
- `CRS_to_silence_of_rank12`

## Verification

Commands run:

```bash
bash -lc 'exec -a lake /data/home/xhuan5/.elan/bin/elan env lean SSExactMajority/UpperBound/Time/OptimalWindows.lean'
bash -lc 'exec -a lake /data/home/xhuan5/.elan/bin/elan build SSExactMajority.UpperBound.Time.OptimalWindows'
```

Both passed.  The module build ended with:

```text
Built SSExactMajority.UpperBound.Time.OptimalWindows
Build completed successfully (3251 jobs).
```

The target build replays existing dependency warnings.  For
`OptimalWindows.lean` itself, the remaining warnings are unused decidability or
section-variable linter warnings.  A token scan of `OptimalWindows.lean` found
no forbidden proof placeholders, unchecked-declaration shortcuts, or native
decision shortcuts.
