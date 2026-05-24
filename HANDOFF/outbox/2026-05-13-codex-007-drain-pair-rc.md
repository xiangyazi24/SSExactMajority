# Codex outbox 007 - drain_pair_rc

## Summary
- Filled `drain_pair_rc` in `SSExactMajority/Convergence/BurmanProof.lean`.
- Used the proof skeleton from the nearby block comment, then adjusted the Lean details:
  - avoided brittle `Nat.max_self` rewrites by proving predecessor bounds separately;
  - used `max_le` for the duplicated post-step max;
  - normalized `.max`/`max` through explicit intermediate equalities in the zero case;
  - used the equal rc update equations to prove positivity after a nonzero post-step max;
  - made the final `runPairs_append` step use an explicit `change`.
- Removed the stale sketch comment after turning it into a proof.

## Verification
- Command: `lake env lean SSExactMajority/Convergence/BurmanProof.lean`
- Result: success, 0 errors.
- I did not run the full `lake build`, per inbox 007's request to test with Lean elaboration rather than a full build.

## Sorry delta
- Before: 36 real `sorry` lines in `BurmanProof.lean`.
- After: 35 real `sorry` lines.
- Delta: -1, from filling `drain_pair_rc`.

## Notes
- No blocker remains for this helper.
