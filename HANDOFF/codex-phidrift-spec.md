# Codex task (uisai1): per-step expected drift of phiCount (feeds the PROVEN drift theorem)

We now have `Probability.expectedHittingTime_le_of_drift` (DriftHittingTime.lean, PROVEN):
if `∑' D, stepDist P hn C D * φ D + ε ≤ φ C` on the non-goal region, then
`E[T to Goal] ≤ φ(C₀)/ε`. We need to feed it with φ = phiCount (or determine it doesn't work).

NEW file `SSExactMajority/UpperBound/Time/PhiDrift.lean`.

## Concrete question (compute/bound the drift)
For φ = phiCount, P = PEMProtocolCoupled, on region R (start with R = InSswap ∧ ResAns
(majorityAnswer); broaden if needed), is there ε > 0 (e.g. ε = 1/(n(n-1))) with
`∑' D, stepDist P hn C D * (phiCount D) + ε ≤ phiCount C` for all non-consensus C in R?

stepDist = uniform over the n(n-1) ordered distinct pairs (see ExpectedTime stepDist def).
So `∑' D, stepDist C D * phiCount D = (1/(n(n-1))) * ∑_{i≠j} phiCount (C.step P i j)`.
The drift is negative iff `∑_{i≠j} (phiCount(C.step i j) - phiCount C) ≤ -ε·n(n-1)`, i.e.
the number of pairs that DECREASE phiCount exceeds those that INCREASE it by ≥ ε·n(n-1).

## First sub-goal (most valuable)
Prove or refute: **in region R, the per-step expected phiCount drift is ≤ -1/(n(n-1))**
(at least one more decreasing pair than increasing, when phiCount > 0 and not consensus).
- Decreasing pairs: a `.phi` agent meets a non-`.phi` partner and gets resolved (recruitment
  phi-correction / decision). Count them ≥ (something · phiCount).
- Increasing pairs: the median-`.phi` propagation (PhiDescent.lean's phiCex shows this) and
  recruitment phi-wipe. Bound them.
- If decreasing ≥ increasing + 1 always (phiCount>0), drift ≤ -1/(n(n-1)); apply the drift theorem.
If you find R is too weak (drift not negative), report the exact obstruction and propose the
minimal strengthening of R that makes it negative (this guides the potential design).

## HARD RULES
- NO sorry/axiom/native_decide. Blocked → exact computation + obstruction to
  HANDOFF/outbox/codex-phidrift-report.md. Don't weaken to trivial.
- ONLY PhiDrift.lean. Self-verify `PATH=$HOME/.elan/bin:$PATH lake env lean
  SSExactMajority/UpperBound/Time/PhiDrift.lean`. NEVER lake build. Report status precisely.
