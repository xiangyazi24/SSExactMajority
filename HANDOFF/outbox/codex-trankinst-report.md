# codex-trankinst report (2026-06-04)

## Verdict

The chain is **not trank-uniform** in the current Lean code.  The numeric
windows were generalized to `T_timer`, but the protocol instance throughout the
window/citation/convergence chain is still `PEMProtocolCoupled n Rmax Emax Dmax`,
i.e. `PEMProtocol n Rmax Rmax Emax Dmax`.  Therefore setting
`T_timer = O(1)` would not give a genuine `trank = O(1)` protocol theorem: the
proved final theorem is still about the coupled protocol whose median entry
timer is `7 * (Rmax + 4)`.

I did **not** instantiate a fake `O(n)` bound.

## What is already uniform

* `Time.lean:43-50` defines the intended family
  `PEMProtocol n trank Rmax Emax Dmax`.
* `OptimalWindows.lean:48-72` defines the swap/MAC/live/global window sizes in
  terms of `T_timer`.
* The private timer helper in `Time.lean:5303-5318` is genuinely generic:
  `transitionPEM_prePhase4_preserves_protocol_timer_bound` takes `trank` and a
  cap `K`, with side condition `7 * (trank + 4) <= K`.

Those facts are not enough, because the public theorems below are still stated
over `PEMProtocolCoupled`.

## Exact coupled scope

Timer invariant:
* `Time.lean:5392-5418`
  `transitionPEM_preserves_protocol_timer_bound` and
  `PEMProtocolCoupled_preserves_timer_bounded` are specialized to
  `7 * (Rmax + 4)` and `PEMProtocolCoupled`.
* A constant-trank theorem needs a public version for
  `PEMProtocol n trank Rmax Emax Dmax hn` with `7 * (trank + 4) <= K`
  (then instantiate `K = T_timer`).

Window stack:
* `OptimalWindows.lean:718-741` `OW_rankBound` has the [12] `h12ranking`
  contract and conclusion over `PEMProtocolCoupled`, and also carries
  `IsTimerBoundedConfig (7 * (Rmax + 4))`.
* `OptimalWindows.lean:765-778` `decision_window` is over
  `PEMProtocolCoupled`, via `Time.lean:2335-2347`
  `PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le`.
* `DrainProductive.lean:25-38`
  `timer_drain_to_zero_productive` is `T_timer`-bounded numerically but runs
  on `PEMProtocolCoupled`.
* `DrainProductive.lean:219-231` `MAClive_to_consensus_or_crs` is also
  `T_timer`-bounded numerically but coupled in the protocol.
* `OptimalWindows.lean:831-843` `swap_live_to_cons_or_crs_or_break` takes a
  `T_timer` step invariant, but that invariant is for steps of
  `PEMProtocolCoupled`.
* `DecisionTiming.lean:282-293` `decision_before_timer_zero` is coupled; it
  depends on `Time.lean:8584-8596`
  `PEM_srank_or_timer_failure_prob_le_quarter_short35`, also coupled.
* `OptimalWindows.lean:973-1008` `OW_consensusBound` is coupled in
  `hTimerStep`, `h12rank`, `h12reRank`, the conclusion, and its internal
  invariant; it additionally calls `PEMProtocolCoupled_preserves_timer_bounded`
  at `OptimalWindows.lean:1042-1048`.
* `OptimalWindows.lean:1240-1286` `PEM_expectedParallelTime_optimal` is the
  final expected-parallel theorem, but every protocol occurrence in the
  assumptions and conclusion is `PEMProtocolCoupled`.  Its invariant still
  contains `IsTimerBoundedConfig (7 * (Rmax + 4))` at `1291-1299` and it calls
  the coupled preservation theorem at `1324-1329`.

[12] citation contracts:
* `OptimalWindows.lean:445-476` `CRSResetDuration12` bakes in
  `transitionPEM_prePhase4 n Rmax ...`, `PEMProtocolCoupled`, and
  `IsTimerBoundedConfig (7 * (Rmax + 4))`.
* The downstream reset/rank wrappers
  `CRS_to_silence_faithful(_product)` and
  `CRS_to_consensus_faithful(_product)` at `OptimalWindows.lean:483-691`
  inherit that coupled protocol.
* `h12rank` and `h12reRank` in `OW_consensusBound` and
  `PEM_expectedParallelTime_optimal` are both stated for
  `PEMProtocolCoupled`; `h12reRank` also uses the coupled timer cap
  `7 * (Rmax + 4)`.

Convergence side:
* The abstract bridge in `BurmanProperties.lean:202-211` is trank-parametric:
  `P_EM_consensus_reachable_from_BurmanConvergence_only` works for
  `protocolPEM n trank Rmax rankDelta`.
* The concrete proof that supplies Burman convergence is not parametric:
  `BurmanConvergenceFinal.lean:15941-15948`
  `burmanConvergence_concrete` returns
  `BurmanConvergence Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)`.
* Its proof body sets
  `P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)`
  at `15958`, and the median-correct exit subchain states execution over the
  same coupled protocol at `15923-15925` and `16013-16015`.
* The final qualitative theorem at `BurmanConvergenceFinal.lean:16052-16061`
  is the literal `protocolPEM n n n ...` instantiation.
* `BurmanProof.lean` also contains many direct
  `protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)` occurrences, so
  the concrete convergence proof is not just a one-line wrapper issue.

## Constant-trank requirements if generalized

The Lean decision/timer chain uses `MedianTimerAtLeast 35` as the fresh entry
condition.  Since `transitionPEM_prePhase4` initializes median timers to
`7 * (trank + 4)`, the constant-trank instantiation must at least satisfy

`35 <= 7 * (trank + 4)`, i.e. `trank >= 1`.

The paper-side [12] silence/ranking assumption must additionally supply the
constant `trank` satisfying `srank <= trank * n`; this is currently represented
only as external `h12ranking` / `h12rank` / `h12reRank` contracts, all of which
would need to be restated for `PEMProtocol n trank Rmax Emax Dmax`.

## Minimal restatement/reproof list

1. Add a public generic timer preservation theorem for
   `PEMProtocol n trank Rmax Emax Dmax hn` with cap `K` and
   `7 * (trank + 4) <= K`.
2. Restate/prove the phase-window stack for the generic protocol:
   `PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le`,
   `decision_window`, `PEM_srank_or_timer_failure_prob_le_quarter_short35`,
   `decision_before_timer_zero`, `timer_ge_two_descent_step`,
   `PEM_expected_timer_drain_poly`, `timer_drain_to_zero_productive`,
   `MAClive_to_consensus_or_crs`, and
   `swap_live_to_cons_or_crs_or_break`.
3. Restate `CRSResetDuration12`, `h12ranking`, `h12rank`, and `h12reRank`
   against `PEMProtocol n trank Rmax Emax Dmax`, replacing the coupled timer
   cap by `K`/`T_timer` plus the side condition
   `7 * (trank + 4) <= T_timer`.
4. Restate `OW_rankBound`, `OW_consensusBound`, and
   `PEM_expectedParallelTime_optimal` over the generic protocol.
5. Either generalize the concrete Burman proof to produce
   `BurmanConvergence trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)`, or keep it
   out of the time theorem and make every convergence/citation assumption
   explicitly about the generic protocol.

Only after those are in place can one instantiate a fixed constant, e.g.
`trank = 1` and `T_timer = 35`, to get a genuine `OW_globalWindow = O(n^2)`
sequential / `E[parallel] = O(n)` theorem.

No full build was run for this report because no Lean code was changed and the
requested branch is the structural-scope report, not an instantiated theorem.
