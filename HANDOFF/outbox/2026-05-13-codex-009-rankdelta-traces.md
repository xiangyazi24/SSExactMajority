# Codex outbox 009 - rankDeltaOSSR traces

## Summary
- Verified `rankDeltaOSSR_leader_dedup_step` is proved at current HEAD.
- Verified `rankDeltaOSSR_dormant_dt_decrease` is proved at current HEAD.
- Both proofs use the intended mechanical shape:
  - derive `delaytimer - 1 ≠ 0` from the `1 < delaytimer` hypotheses;
  - unfold `rankDeltaOSSR`, `propagateReset`, `processAgent`, and `resetOSSR`;
  - close by `simp` with role/resetcount/leader/delaytimer facts.

## Verification
- `lake env lean SSExactMajority/Convergence/BurmanProof.lean`: success, 0 errors.
- `lake build SSExactMajority.Convergence.BurmanProof`: success, 0 errors.

## Sorry delta
- Current real `sorry` lines in `BurmanProof.lean`: 34.
- No additional `BurmanProof.lean` diff is present in this outbox commit because the current HEAD already contains the two filled traces.

## Notes
- The remaining relevant Phase 2 gap is schedule construction for `all_resetting_to_dormant`; these two rankDelta-level traces are no longer blockers.
