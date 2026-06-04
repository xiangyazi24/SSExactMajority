
## Run 2026-06-03 ~23:40 (automode)
- doctrine: docs/DOCTRINE.md @ dce6e30
- approval msg_id: 3580 ("继续")
- starting avenue: (a) escape-to-restart renewal
- first concrete step (R3-independent): relaxed-goal per-phase descents
  (goal includes ¬invariant ⟹ all-pair closure trivial)
- end: <open>
- final result: <open>

## Run 2026-06-04 — genuine O(n) via generic-trank re-param (path confirmed)
- ChatGPT Pro R4 (SHA b0bee4b): verdict (c) generic re-param; (a) downward timer-cap rescale UNSOUND, (b) trank-monotonicity UNSOUND. Both load-bearing claims source-verified:
  - timer is a transition semantic: state literally gets `{ a₀ with timer := 7*(trank+4) }` (BurmanConvergenceFinal.lean:2609) → cannot shrink cap without changing kernel.
  - 35 is a real correctness floor: OW_consensusBound needs MedianTimerAtLeast 35; 7*(1+4)=35 exactly → trank=1 is the minimal sound choice (T_timer=35=O(1)).
- Path: re-state window stack + keystones over PEMProtocol n trank Rmax (cap K, 7(trank+4)≤K), instantiate trank=1/T_timer=35 → O(n). All lake-build verified. b0bee4b (O(n log n)) kept as base until O(n) verified.
- cxg (uisai1 tmux): GenericTrank.lean — generic_transitionPEM_preserves_timer_bound DONE (0 sorry); probing first window for timer-cap-uniformity.
