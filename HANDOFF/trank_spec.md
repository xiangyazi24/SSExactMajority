# Final unification: correctness at trank = 1 — same protocol instance as the complexity keystone

## The gap
Correctness: P_EM_solves_SSEM_log is over protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) — trank
(first argument) = Rmax. Complexity: PEM_expectedParallelTime_On_faithful_log is over PEMProtocol n 1 Rmax
Emax Dmax — trank = 1. The paper theorem needs BOTH for ONE instance: protocolPEM n 1 Rmax (trank = 1,
timer = 7*(1+4) = 35).

## Task
1. DETERMINE: does the correctness log chain (LogTreeReset / LogRegimeConvergence / LogRegimeFinal and the
   old-chain segments they reuse: the FreshRankingStart -> InSswap wake segment, the ranking/silence segments,
   phase1_trigger, the producers) actually USE trank = Rmax in any proof, or is protocolPEM n Rmax Rmax pure
   inherited notation? trank enters transitionPEM only through the timer reset value 7*(trank+4) (and possibly
   rank-phase guards). The reset/fresh/drain machinery (delaytimer/resetcount) should be trank-independent.
   The median-timer/ranking segments may reference the timer value — find where.
2. If notational / timer-value-generic: re-state the correctness log chain at GENERIC trank (or directly at
   trank = 1), producing P_EM_solves_SSEM_log_trank1 :
     4 <= n -> 1 < Dmax -> 2*clog 2 n + 2 <= Rmax ->
     SolvesSSEM (protocolPEM n 1 Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) n
   Reuse the GenericTrank step-equality machinery (generic_step_eq_coupled_of_InSrank etc.) where the old
   segments were proven at coupled trank, OR re-instantiate the statements — whichever is cheaper. NOTE the
   old chain segments you reused were stated at protocolPEM n Rmax Rmax; if their proofs go through verbatim
   at protocolPEM n 1 Rmax (only the timer constant changes), duplicate-instantiate them.
3. If a segment GENUINELY uses trank = Rmax (e.g. a proof needs the timer reset value to be >= some
   n-dependent quantity), STOP on it and report the exact use — that would mean the wake/ranking segment
   needs timer >= f(n) and trank=1 (timer=35) breaks it; we would then need the segment re-proved for
   timer=35 (which the TIME side already handles probabilistically — check if the correctness side can route
   around).

## HARD RULES (automode: NO effort cap; work in LogRegimeFinal.lean / a new LogTrank1.lean (yours); do NOT
edit old files; lake build until clean; no sorry/axiom/native_decide; commit [Xiang-proxy]; report the
final P_EM_solves_SSEM_log_trank1 hypothesis list (or the exact genuine trank use) to
HANDOFF/outbox/cxfix-report.md.)
