# Codex outbox 018: propagate-reset wrappers

## Done

- Added `propagateReset_spreader_trace`.
- Added `rankDeltaOSSR_propagate_reset_spreader`.
- Moved `transitionPEM_structural_passthrough` before the downstream wrappers so earlier theorems can use the interface.
- Filled:
  - `propagate_reset_one_step`
  - `propagate_reset_spreader_state`

Both wrappers now follow the rankDelta trace + `transitionPEM_structural_passthrough` + `Config.step_*_state` pattern used by `step_both_rc_pos`.

## Verification

- `lake env lean SSExactMajority/Convergence/BurmanProof.lean`: 0 errors.
- `lake build SSExactMajority.Convergence.BurmanProof`: 0 errors, build completed successfully.
- Current counts in `BurmanProof.lean`:
  - `sorry` lines: 25
  - `TODO(processAgent-refactor)`: 20

## Blockers / notes

- `transitionPEM_structural_passthrough` remains a `sorry` in this pushed batch. I tried two proof shapes:
  - generalize rankDelta output + `simp [h_not]`
  - destruct both output roles + `simp_all`

  Both proof searches stalled for several minutes when the lemma is moved before the wrappers. I kept the structural interface as a forward declaration with `sorry` so downstream plumbing can proceed and verified the build.

- `transitionPEM_unsettled_one_step_progress` is not just the same passthrough pattern:
  - if rankDelta output is not both Settled, passthrough applies;
  - if the Unsettled agent is recruited by a Settled partner, rankDelta output can be both Settled and Phase 4 may run;
  - the mass statement also needs errorcount preservation, but the current structural passthrough theorem does not expose errorcount fields.

Suggested next helper: either strengthen/add a separate errorcount passthrough lemma, or prove a dedicated `transitionPEM_unsettled...` split with a both-Settled Phase 4 case.

Local lock released.
