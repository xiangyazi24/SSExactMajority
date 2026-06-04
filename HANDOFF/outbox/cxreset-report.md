# Generic keystone re-audit fix report

## Verdict

No blocker.  Both re-audit holes are closed in
`SSExactMajority/UpperBound/Time/GenericKeystone.lean`.

- Hole 1, vacuous timer-ranked hypotheses: closed by adding a consensus
  done-escape to the ranking and reranking targets, and by threading the
  renewal proof through the consensus branch.
- Hole 2, only-positive `p_reset`: closed by adding an explicit linear corollary
  with reset success probability fixed to the absolute constant `1/2`.

`OptimalWindows.lean` and `GenericTrank.lean` were not edited.

## Hole 1

The generic keystone no longer asks the cited ranking/reranking windows to
force a silent consensus state with median timer `0` to reach
`MedianTimerAtLeast 35`.

Evidence:

- `PEM_expectedParallelTime_optimal_generic` ranking target is now
  `(InSrank ∧ MedianTimerAtLeast 35 ∧ timer-bounded) ∨ IsConsensusConfig`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:243-253`.
- Its rerank target is now
  `(InSswap ∧ MedianTimerAtLeast 35) ∨ IsConsensusConfig`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:266-276`.
- Internal renewal target names are `RankOrConsensus` and
  `LiveOrConsensus`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:298-306`.
- If the ranking stage hits consensus, the proof uses the zero-time hit branch;
  otherwise it continues through live/rerank:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:532-608`.
- The final composition is still the same renewal window and success product
  `p_reset * 128^-1`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:609-628`.

The `trank = 1` theorem exposes the same satisfiable targets:

- ranking with consensus done-escape:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:641-649`;
- rerank with consensus done-escape:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:662-671`.

This removes the silent-consensus vacuity while preserving the original
non-consensus renewal composition.

## Hole 2

The new explicit corollary fixes the reset success probability to `1/2` and
returns a literal linear bound.

Evidence:

- Linear coefficient:
  `PEM_On_explicit_linearConstant C_rank C_reset C_T_rank C_T_rerank =
  256 * (2*C_rank + C_reset + C_T_rank + C_T_rerank + 76)`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:745-747`.
- `PEM_expectedParallelTime_On_explicit` assumes
  `CRSResetCompletion12Generic ... ((2 : ENNReal)^-1) ...`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:754-769`.
- It assumes the cited `T_rank` and `T_rerank` windows are bounded by fixed
  constants times `n^2`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:788-789`.
- Its conclusion is an explicit linear bound:
  `expectedParallelTimeToConsensus <=
  (PEM_On_explicit_linearConstant ... * n : Nat)`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:790-796`.
- The arithmetic helper cancels one `n` from a quadratic sequential window:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:725-740`.
- The proof rewrites
  `(((2^-1) * (128^-1))^-1)` to `256` and uses
  `OW_globalWindow_trank1_quadratic`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:806-848`.

This makes the theorem family genuinely `O(n)` once the cited constants
`C_rank`, `C_reset`, `C_T_rank`, and `C_T_rerank` are fixed absolute constants.

## Verification

Commands run:

```bash
exec -a lake /data/home/xhuan5/.elan/bin/elan env lean SSExactMajority/UpperBound/Time/GenericKeystone.lean
exec -a lake /data/home/xhuan5/.elan/bin/elan build
grep -n "sorry\\|admit\\|axiom\\|native_decide" SSExactMajority/UpperBound/Time/GenericKeystone.lean || true
```

Results:

```text
GenericKeystone single-file Lean check: passed with no output.
Full lake build: Build completed successfully (3266 jobs).
Forbidden-token scan: no matches.
```
