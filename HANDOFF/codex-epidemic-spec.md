# Codex task (uisai1): explicit epidemic propagation bound (replaces the +B propagation part)

SCOPE (A). The +B in allR_to_consensus (bounded_config_consensus_uniform_le) covers Phase2
(dormant→consensus = [12] ranking [cited] + Kanaya epidemic/swap/decision). This task makes the
EPIDEMIC PROPAGATION part explicit — the genuine Kanaya piece currently only finite (<⊤).

## The epidemic
During Propagate-Reset (Resetting agents), the correct opinion overwrites ϕ via the one-way epidemic:
Protocol/Transition.lean:51-54 — if a₀.answer=ϕ ∧ a₁.answer≠ϕ then a₀ adopts a₁.answer (and symmetric).
So `phiCount` (BurmanConvergenceFinal:3412, #agents with answer=ϕ) is MONOTONE NON-INCREASING during
reset (one-way: non-ϕ never becomes ϕ except the deliberate clear at reset start). NOTE the earlier
phiCount non-monotonicity (PhiDescent) was the SWAP phase; during Propagate-Reset the epidemic branch
is one-way.

## Target (explicit poly, NOT <⊤)
```
theorem epidemic_phiCount_to_zero_expected_le
  (hn4 : 4 ≤ n) (C) (hSeed : <a correct-answer seed exists ∧ all-Resetting-or-epidemic region>)
  (hBounded : ...) :
  Probability.expectedHittingTime P hn C (fun D => phiCount D = 0 ∧ <all non-ϕ = correct>)
    ≤ (explicit poly, e.g. c * n * n * H_n or c*n*n — coupon/epidemic scale O(n log n) seq)
```
via variable-descent on φ = phiCount: per-step, a ϕ-agent meeting a non-ϕ agent decreases phiCount;
with k = phiCount and (n-k) non-ϕ agents, the number of good (ϕ, non-ϕ) ordered pairs is 2k(n-k), so
one-step descent prob ≥ 2k(n-k)/(n(n-1)). Coupon/epidemic sum: Σ_k n(n-1)/(2k(n-k)) = O(n log n) seq.
Use expectedHittingTime_le_of_variable_descent_until_goal with pRate k = 2k(n-k)/(n(n-1)) (or a clean
lower bound on it). REUSE epidemic_timer_branch_to_consensus / phase4_propagate_no_reset_of_eq_answer /
transitionPEM_prePhase4_propagate_answer (BurmanConvergenceFinal) if they give the per-step epidemic fact.

## FIRST sub-goal
The one-step epidemic descent witness: in the reset/epidemic region with phiCount=k>0, a (ϕ,non-ϕ)
pair decreases phiCount, prob ≥ 2k(n-k)/(n(n-1)) (count the good pairs). Then the variable-descent
E[T] bound. If the region (when is the epidemic branch active / one-way) is subtle, report the exact
region needed.

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide. Grind or precise obstruction to HANDOFF/outbox/codex-epidemic-report.md.
- New file SSExactMajority/UpperBound/Time/EpidemicBound.lean. Self-verify lake env lean (project root). NEVER lake build.
