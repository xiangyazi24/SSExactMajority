# Codex outbox 017: processAgent residual batch

## Done

- Cleared `rankDeltaOSSR_unsettled_no_resetting_progress`.
- Proof is the expected rankDelta-only pattern:

```lean
unfold rankDeltaOSSR
simp [hs_uns, ht_not_res]
split_ifs <;> simp_all <;> omega
```

## Verification

- `lake env lean SSExactMajority/Convergence/BurmanProof.lean`
- Result: 0 errors.
- Current counts in `BurmanProof.lean`:
  - `sorry` lines: 27
  - `TODO(processAgent-refactor)`: 22

## Attempted / blocker

I tried `propagate_reset_one_step` directly:

1. Rewrote the `let P` goal through `Config.step_snd_state`.
2. Reduced to the second component of `transitionPEM`.
3. `unfold transitionPEM; simp [rankDeltaOSSR_propagate_reset ...]` still times out in `whnf` at the default 200000 heartbeats.

So I restored this theorem to its existing `sorry`. This confirms the remaining nearby propagate-reset wrappers are not the simple processAgent unfold/simp class; they need the structural passthrough wrapper moved earlier, duplicated locally, or proved in a form usable before these theorems.

## Residual classification

The remaining `processAgent-refactor` TODOs are wrapper/global/Phase-4 obligations, not direct rankDelta traces:

- reset propagation through `transitionPEM`: `propagation_reset_fires_no_swap`, `propagate_reset_one_step`, `propagate_reset_spreader_state`, `phase2_propagate_reset`
- unsettled wrappers depending on `transitionPEM_unsettled_one_step_progress`
- structural passthrough itself
- Phase 3/Phase 4 recruitment and composition macros

Local lock released.
