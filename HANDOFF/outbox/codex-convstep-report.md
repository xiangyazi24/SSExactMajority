## 2026-06-03 codex convstep

Status: completed.

Added `SSExactMajority/UpperBound/Time/ConvStep.lean`.

What was proved:

- `rankDeltaOSSR_converts_resetting_rc0` (private): protocol-unfold structural lemma showing the first component leaves `.Resetting` when a `Resetting`/`resetcount = 0` initiator actually fires after `propagateReset` resetcount synchronization.
- `step_converts_resetting_rc0`: `Config.step` version for the full concrete `protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)`, under the necessary guard that the rankDelta output is not both `.Settled`, so P_EM Phase 4 is skipped.
- `step_converts_resetting_rc0_follower`: follower specialization with no extra Phase 4 hypothesis; the initiator becomes `.Unsettled`.

Necessary adjustments from the handoff target:

- There is no `PEMProtocolCoupled` name in the repo; the concrete protocol used here is `protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)`.
- The true firing condition is not just `delaytimer = 0 ∨ partner not Resetting`. If the partner is also `.Resetting`, Phase 2 synchronizes resetcounts first; the initiator fires only when the partner contributes zero after decrement and the local delaytimer fires. I stated this as:
  `(C j).1.role ≠ .Resetting ∨ ((C j).1.resetcount ≤ 1 ∧ (C i).1.delaytimer ≤ 1)`.
- For the full `transitionPEM`, a leader that wakes to `.Settled` may enter Phase 4 if the rankDelta output is both `.Settled`; Phase 4 can swap/propagate and potentially re-reset. The main `Config.step` theorem therefore includes the non-both-settled guard, and the follower corollary discharges that guard automatically.

Verification:

`PATH=$HOME/.elan/bin:$PATH lake env lean SSExactMajority/UpperBound/Time/ConvStep.lean`

Result: passed. No `sorry`, `axiom`, or `native_decide` in `ConvStep.lean`.
