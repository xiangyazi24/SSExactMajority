# Codex task (uisai1): combined-potential expected drift (the quantitative heart)

Feed the PROVEN `Probability.expectedHittingTime_le_of_drift` (DriftHittingTime.lean) with a
COMBINED potential whose per-step EXPECTED drift is negative (transient increases allowed —
that's the whole point of using the drift theorem, since phiCount/#Resetting are non-monotone).

NEW file `SSExactMajority/UpperBound/Time/CombDrift.lean`.

## Potential (lexicographic; pick weights so it works)
`φ D := W2 * phiCount D + W1 * (n - settledInHeapCount D) + (∑ w, (D w).1.timer)`
with `W1` ≥ (max timer-sum swing + 1) and `W2` ≥ (W1·n + max ranking swing + 1), so a phiCount
decrease dominates a ranking increase, which dominates a timer change. (Adjust the middle
"ranking incompleteness" term to whatever monotone-ish heap measure is cleanest; if a clean
one is elusive, drop it and use φ = W2*phiCount + Σ timer and rely on the timer term + the
fact that in the MAC region phiCount doesn't increase.)

## The obligation (this is the quantitative core)
Prove the per-step expected-drift inequality on a region R (start: post-seed correct region,
e.g. bounded ∧ "median answer not .phi" so propagation can't spread .phi):
`∑' D, stepDist P hn C D * (φ D) + ε ≤ φ C`  for all non-goal C in R, with ε = 1/(n(n-1)).
Equivalently `∑_{i≠j} (φ(C.step i j) - φ C) ≤ -1`: count pairs, show net decrease ≥ 1.
- timer-draining pairs (median↔max etc.): decrease the timer term.
- recruitment pairs: decrease ranking-incompleteness.
- propagation pairs at timer=0: decrease phiCount (big W2 drop).
- reset pairs (collision same-rank Settled / error errorcount=0 Unsettled): bound their COUNT
  and weight; in region R show they are outnumbered by progress pairs (net ≤ -1).
Then Goal := phiCount=0 ∧ InSswap (⟹ consensus via isConsensusConfig_of_InSswap_phiCount_zero),
apply the drift theorem: E[T] ≤ φ(C₀)/ε = poly.

## FIRST sub-goal
Just prove the NET-COUNT drift inequality `∑_{i≠j}(φ(step)-φ) ≤ -1` on R (pure finite
combinatorics over pairs + the per-step effect lemmas, incl. proven ConvStep). Report the
exact R you need. If a clean R is elusive, report the precise obstruction (which reset pairs
can't be outnumbered) so Opus refines φ/R.

## HARD RULES
- NO sorry/axiom/native_decide. Blocked → exact obstruction to
  HANDOFF/outbox/codex-combdrift-report.md. Don't weaken to trivial.
- ONLY CombDrift.lean. Self-verify lake env lean. NEVER lake build. Report status precisely.
