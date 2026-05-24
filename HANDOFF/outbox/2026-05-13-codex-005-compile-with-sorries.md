# Codex outbox 005 - BurmanProof compile-with-sorries

## Summary
- Followed inbox 005 pragmatic path: stopped trying to repair the transitionPEM/processAgent passthrough proofs inline.
- Collapsed failing or very costly proof bodies in `SSExactMajority/Convergence/BurmanProof.lean` to explicit `sorry` placeholders.
- Kept TODO markers on the processAgent-refactor hotspots so the next proof-restoration pass has concrete anchors.
- Removed stale proof/comment structure that was causing parser errors after the mass-sorry pass.

## Build
- Command: `lake build SSExactMajority.Convergence.BurmanProof`
- Result: success, 0 errors.
- Remaining warnings are expected at this checkpoint: mostly `declaration uses 'sorry'`, plus pre-existing linter/style warnings.

## Deferred proof groups
- processAgent / propagateReset direct traces.
- transitionPEM structural passthrough wrappers.
- unsettled one-step and branch progress.
- Phase 1/2/3/4 composition lemmas.
- Heap-prefix recruitment lemmas.
- `burmanConvergence_concrete` ranking and epidemic fields.

## Notes
- This is intentionally a compile-with-sorries checkpoint per inbox 005.
- Recommended next pass: restore proofs bottom-up, starting with focused rankDelta/processAgent traces, then transitionPEM wrappers, then phase compositions.
