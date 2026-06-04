# Codex task (uisai1): global Lyapunov foundation — reset-mass drift on IsBoundedConfig

ROUTE (settled): no phase-invariant region works (scheduler interleaves phases). Use the ONE
provably-closed region IsBoundedConfig (PEMProtocolCoupled_preserves_bounded) + a GLOBAL
potential, feeding expectedHittingTime_le_of_drift (DriftHittingTime.lean).

NEW file SSExactMajority/UpperBound/Time/GlobalDrift.lean.

## This task: the RESET-MASS component (foundation of the supermartingale)
Define on ALL configs: `resetMass C := ∑ w, (C w).1.resetcount`.
Investigate its per-step EXPECTED change on IsBoundedConfig:
  Δ(C) := (∑' D, stepDist P hn C D * resetMass D) − resetMass C.
Determine precisely:
1. Which ordered pairs DECREASE resetMass (rc-drain steps: a Resetting/draining agent steps, rc−1).
   Quantify: how many such pairs, each contributing −1. Lower-bound the count on a non-stable config.
2. Which pairs INCREASE resetMass (fresh resets: collision same-rank Settled → rc:=Rmax; error
   monitoring Unsettled errorcount=0 → rc:=Rmax). Quantify the max increase (≤Rmax per such pair)
   and bound the COUNT of such pairs.
3. State the per-step expected-drift fact you can PROVE: either Δ ≤ −ε on some explicit subregion,
   OR Δ ≤ (small positive) with an explicit bound on the positive part (the compensator).

## Deliverable
- `resetMass` def + `resetMass_step_eq` (per-step change as a sum over the chosen pair's effect).
- The drain-pair witness lemma + count bound; the reset-pair max-increase + count bound.
- A REPORT (HANDOFF/outbox/codex-global-report.md) stating the exact per-step expected drift
  inequality you can prove for resetMass on IsBoundedConfig, and whether fresh resets can be
  bounded per-step or need a global total-increase (compensator) argument. This determines the
  weight structure of the full global φ.

## HARD RULES
- NO sorry/axiom/native_decide. Prove what you can; report the exact obstruction for the rest.
- ONLY GlobalDrift.lean. Self-verify lake env lean. NEVER lake build. Be quantitative
  (exact pair counts, exact rc bounds) — this drives the global potential's weights.
