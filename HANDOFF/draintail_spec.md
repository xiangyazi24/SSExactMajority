# Prove the drain-tail is small: nail non-vacuity of PEM_expectedParallelTime_On_faithful

## Goal
drainNoWakeTail n K Dmax := (n:ENNReal) * (C(K,Dmax):ENNReal) * ((2:ENNReal)*(n:ENNReal)inv)^Dmax
  (definition in AnswerEpidemicBridge.lean:9).
We must show this tail is small in the operative regime (Dmax >= n, K = O(n log n)), so that the hypothesis
hTail (drainNoWakeTail n K Dmax <= pE/2) in PEM_expectedParallelTime_On_faithful is genuinely SATISFIABLE
together with the epidemic window — i.e. the keystone is NOT vacuous.

## Target theorem (NEW file SSExactMajority/UpperBound/Time/DrainTailBound.lean — you own it)
Prove (clean closed-form upper bound):
  drainNoWakeTail_le_geom :
    forall {n K Dmax : N}, 0 < n -> 11 * K <= n * Dmax ->
      drainNoWakeTail n K Dmax <= (n : ENNReal) * ((2 : ENNReal)inv) ^ Dmax
and the corollary showing it tends below any positive constant:
  drainNoWakeTail_lt_top_and_small : with Dmax >= n it is <= n * (1/2)^n, hence (state precisely) for the
  purpose of the audit, n * (2inv)^n is eventually below any positive epsilon. If a full asymptotic is heavy,
  at MINIMUM deliver drainNoWakeTail_le_geom (the closed form) + a lemma
    drainNoWakeTail_le_geom_at_Dmax_ge_n : 0<n -> n<=Dmax -> 11*K <= n*Dmax ->
        drainNoWakeTail n K Dmax <= (n:ENNReal) * (2inv)^n
  (monotone in exponent since 2inv <= 1).

## Math derivation (use it; find exact Mathlib lemma names)
drainNoWakeTail = n * C(K,Dmax) * (2/n)^Dmax. Want <= n*(1/2)^Dmax, i.e. C(K,Dmax)*(4/n)^Dmax <= 1, i.e.
C(K,Dmax) <= (n/4)^Dmax.
Use C(K,Dmax) <= K^Dmax / Dmax!  (Mathlib: search Nat.choose_le_pow_div_factorial or
Nat.choose_le_pow ... ; if only choose * factorial <= ... forms exist, derive it).
Use Dmax! >= (Dmax/e)^Dmax (real Stirling-type lower bound; Mathlib Analysis Stirling, or
Nat.factorial bounds). Then K^Dmax/Dmax! <= K^Dmax (e/Dmax)^Dmax = (eK/Dmax)^Dmax. With 4eK <= n*Dmax
(implied by 11*K <= n*Dmax since 4e < 11) get (eK/Dmax) <= n/4, so <= (n/4)^Dmax. QED.
Work in Real then cast to ENNReal, or directly in ENNReal/NNReal — whichever Mathlib supports cleanly for
the choose/factorial inequalities. If the e-bound lemma is painful, ANY explicit factorial lower bound
Dmax! >= (Dmax/c)^Dmax for a concrete c works — just change 11 to ceil(4c) in the hypothesis. Document the
constant you land on.

## Why 11*K <= n*Dmax is the right regime (for the report, not the proof)
At Dmax >= n and K = c*n*clog n (the epidemic window), 11*c*n*clog n <= n*n holds for n large
(11 c clog n <= n). So hTail is satisfiable at the epidemic window; combined with the standard-epidemic
hypothesis this shows the keystone hypothesis bundle is jointly satisfiable (non-vacuous).

## HARD RULES (automode: NO effort cap — grind until the math is wrong or Mathlib genuinely lacks the API)
New file DrainTailBound.lean is yours; do NOT edit other files (import AnswerEpidemicBridge for the def).
Iterate lake build SSExactMajority.UpperBound.Time.DrainTailBound until clean. No sorry/axiom/native_decide.
Commit clean with [Xiang-proxy]. Report theorem names + file:line + the final constant + whether the
asymptotic-to-zero is included, to HANDOFF/outbox/cxfix-report.md.
