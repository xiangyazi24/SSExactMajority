# Generic reset O(n) integration report

## Verdict

No blocker.  The generic reset integration and the `trank = 1` instantiation
give the intended clean `O(n)` parallel-time form, conditional on the same
satisfiable cited windows:

- generic faithful reset completion with `K_reset <= C_reset*n*n` and constant
  `p_reset > 0`;
- generic initial ranking/reranking windows of `O(n^2)` sequential interactions;
- generic post-epidemic rank window of `O(n^2)` sequential interactions.

There is no old deterministic `CorrectResetSeed -> EpidemicRegion` invariant in
the new keystone.  The reset branch is the faithful probabilistic
reach-then-within chain.

## Files

- Added `SSExactMajority/UpperBound/Time/GenericKeystone.lean`.
- Added root import:
  `SSExactMajority.lean:43`.
- Did not edit `SSExactMajority/UpperBound/Time/GenericTrank.lean`.
- Did not edit `SSExactMajority/UpperBound/Time/OptimalWindows.lean`.

## Generic reset contract

`CRSResetCompletion12Generic` is stated directly for
`PEMProtocol n trank Rmax Emax Dmax`, so the reset contract no longer depends
on the coupled median-timer scale:

- contract header:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:31`;
- `resetReach` is the faithful `CorrectResetSeed -> ProbHitWithin ->
  ResetCompletionTarget12` reset window:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:37`;
- the reset window is quadratic:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:36`;
- the post-reset epidemic mechanics are generic protocol obligations consumed
  by the coupon/window lemma, not a false forall-invariant:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:45`,
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:53`,
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:59`.

This is a cited-hypothesis genericization, not a transfer proof from the old
coupled contract.  That is the faithful shape here: the reset-completion window
is a probabilistic [12] reset fact and is satisfiable as a `ProbHitWithin`
assumption for the actual generic protocol.

## Composition

The reach-then-within composition lemma exists and composes cleanly:
`Probability.ProbHitWithin_add_ge_mul`.

Evidence:

- reset completion to answer epidemic:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:73`;
- `CorrectResetSeed -> ResetCompletionTarget12 -> EpidemicPhiGoal` composition:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:155`,
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:160`;
- `EpidemicPhiGoal -> OW_silenceEndpoint` composition:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:181`,
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:182`;
- consensus wrapper over the same reset branch:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:190`.

## Generic keystone

`PEM_expectedParallelTime_optimal_generic` is assembled over
`PEMProtocol n trank Rmax Emax Dmax`:

- theorem header:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:235`;
- free timer cap `T_timer` and its step preservation hypothesis:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:237`,
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:239`;
- generic ranking target preserves both `7*(trank+4)` and `T_timer`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:243`;
- generic reset completion hypothesis:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:254`;
- generic post-epidemic ranking and reranking hypotheses:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:258`,
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:266`;
- final expected parallel-time bound has global window divided by `n`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:279`,
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:282`.

The proof consumes the generic timer preservation/window lemmas from
`GenericTrank`.  The timer-drain contribution is carried through
`OW_macLiveWindow n T_timer` inside the generic MAClive window, so the generic
keystone keeps `T_timer` free instead of baking in the coupled timer scale.

## `trank = 1` instantiation

The constant-timer instantiation is explicit:

- `PEM_trank1_timer = 35`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:566`;
- `PEM_expectedParallelTime_On` specializes the generic keystone at
  `trank = 1`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:569`;
- timer preservation is discharged by `generic_timer_preservation` with
  `7*(1+4) <= 35`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:612`,
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:618`;
- the instantiated theorem returns the same renewal bound with
  `OW_globalWindow n C_rank 35 K_reset T_rank T_rerank / n`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:603`,
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:608`.

The sequential window is proved quadratic for the `trank = 1` constants:

- `OW_globalWindow_trank1_quadratic`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:640`;
- assumptions `K_reset`, `T_rank`, and `T_rerank` are all `O(n^2)`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:641`,
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:642`,
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:643`;
- conclusion:
  `OW_globalWindow <= (2*C_rank + C_reset + C_T_rank + C_T_rerank + 76)*n*n`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:645`.

With constant `p_reset` and constant `C_rank`, the bound in
`PEM_expectedParallelTime_On` is therefore `O(n^2)/n = O(n)` parallel time.

## Non-vacuity

The keystone hypotheses are satisfiable-shaped and faithful:

- reset entry is a probabilistic `ProbHitWithin` completion window, not a
  deterministic invariant;
- timer assumptions are generic boundedness/preservation hypotheses over the
  actual `PEMProtocol n trank Rmax`;
- ranking, reranking, and post-epidemic rank windows are cited
  probability/expectation windows with explicit finite time bounds.

No hypothesis asserts the previously false global invariant
`CorrectResetSeed -> EpidemicRegion` for every step.

## Verification

Commands run:

```bash
exec -a lake /data/home/xhuan5/.elan/bin/elan env lean SSExactMajority/UpperBound/Time/GenericKeystone.lean
exec -a lake /data/home/xhuan5/.elan/bin/elan build
```

Results:

```text
GenericKeystone single-file Lean check: passed with no output.
Full lake build: Build completed successfully (3266 jobs).
```

A token scan of `GenericKeystone.lean` found no forbidden proof placeholders,
unchecked-declaration shortcuts, or native decision shortcuts.
