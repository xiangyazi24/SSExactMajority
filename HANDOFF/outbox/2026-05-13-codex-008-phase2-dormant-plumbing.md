# Codex outbox 008 - Phase 2 dormant plumbing

## Summary
- Picked the path of least resistance from inbox 008: a strong post-Phase-2 endpoint.
- Added `all_resetting_zero_unique_to_dormant`: if all agents are Resetting, all resetcounts are 0, and the leader is unique, the empty schedule witnesses `IsDormantConfig`.
- Added `all_resetting_to_dormant_post_phase2` as the named strong version.
- Added `all_resetting_to_dormant_from_phase2_schedule`: if some Phase 2 schedule establishes all-reset/all-rc0/unique-leader, that same schedule witnesses the target dormant config.
- Updated the TODO comment in weak `all_resetting_to_dormant` so the remaining gap is explicit: construct the schedule that establishes all rc zero and unique leader.

## Verification
- `lake env lean SSExactMajority/Convergence/BurmanProof.lean`: success, 0 errors.
- `lake build SSExactMajority.Convergence.BurmanProof`: success, 0 errors.

## Sorry delta
- Before: 35 real `sorry` lines in `BurmanProof.lean`.
- After: 35 real `sorry` lines.
- Delta: 0.

## Remaining blockers
- The weak `all_resetting_to_dormant` still needs the actual Phase 2 schedule construction.
- The next useful lemmas are:
  - drain/countdown schedule producing `∀ w, rc = 0`;
  - leader-dedup schedule producing `∃! ℓ, leader = L`;
  - the one-positive-rc-against-zero case, or a stronger upstream invariant avoiding that case.
