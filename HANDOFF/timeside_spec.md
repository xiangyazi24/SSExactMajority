# Step 3 piece 1: classify and eliminate the time-side n <= Rmax/Emax/Dmax (the O(n) keystone at log params)

## Context
Correctness is DONE at log params (P_EM_solves_SSEM_log: 4<=n, 1<Dmax, 2clog2 n+2<=Rmax). The time keystone
PEM_expectedParallelTime_On_faithful (OptimalWindowsFaithful.lean:~190) still carries hRmax/hEmax/hDmax
(n <= each). For the paper instance (Rmax=Theta(log n)) those must be classified and eliminated where they
are artifacts. NOTE the time-side hDmax interacts with the drain budget: the probabilistic side ALSO needs
Dmax >= d with d = Theta(log n) (hTail/drainNoWakeTail at the epidemic window) — that is genuine and fine at
Dmax = Theta(log n).

## Task
1. MAP: the keystone passes hRmax/hEmax/hDmax into generic_decision_before_timer_zero and
   generic_MAClive_to_consensus_or_crs_window (GenericKeystone.lean:673,:723), which route into the window
   machinery (GenericTrank.lean — uses at :654,:1540,:1589,:1610,:1680,:1755,:1772,:1780 — and
   OptimalWindows.lean swap_live_to_cons_or_crs_or_break / timer_drain_window and the Time.lean layers below).
   For EVERY real consumption (not binder pass-through), record file:line and classify:
   (a) artifact (only uses 1 < _ or a constant),
   (b) genuine-LARGE: the proof needs the counter >= n (e.g. fuel/error budget must survive n events in a
       window) — these BREAK at log params and need re-derivation or a different argument,
   (c) genuine-SMALL-OK: the proof works for any value >= some constant/clog bound.
   IMPORTANT: these are PROBABILISTIC window lemmas (all-scheduler-outcome within a window), NOT existential
   schedules — counter bounds CAN be genuine here. Classify honestly; do NOT assume artifact.
2. For every (a)/(c): re-derive log-level variants (new file SSExactMajority/UpperBound/Time/LogWindows.lean,
   yours) or thread weakened hypotheses, culminating in PEM_expectedParallelTime_On_faithful_log with
   hypotheses: constants + clog-level bounds (2clog2 n+2 <= Rmax, c <= Dmax with c the honest bound you find,
   Emax whatever the proofs need) — same conclusion (the O(n) bound over PEMProtocol n 1).
3. For every (b): STOP on it and report the exact counting argument (file:line, what quantity must exceed
   what, why) — that is where the paper-side probabilistic argument differs and we will design the
   replacement together. Do not weaken or fake.

## HARD RULES (automode: NO effort cap; lake build SSExactMajority.UpperBound.Time.LogWindows (or the keystone
module) until clean; no sorry/axiom/native_decide; commit [Xiang-proxy]; report the classification table +
landed theorem names to HANDOFF/outbox/cxfix-report.md.)
