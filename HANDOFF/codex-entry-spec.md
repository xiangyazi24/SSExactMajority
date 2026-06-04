# Codex task (uisai1): expected-time ENTRY link — dormant/bounded → FreshRankingStart

The optimal bound's most concrete missing link. Currently `dormant_to_FreshRankingStart`
(BurmanConvergenceFinal.lean:6985) is QUALITATIVE: `∃ L, FreshRankingStart (runPairs P C L)`.
We need an EXPECTED-TIME version.

NEW file `SSExactMajority/UpperBound/Time/EntryBound.lean`.

## Target (keep faithful; loosen constant to explicit poly c·Rmax·n² + adjust later)
```
theorem dormant_to_FreshRankingStart_expected_le {n Rmax Emax Dmax} [..] [..]
  (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
  (C) (hDormant : IsDormantConfig C) (hBounded : IsBoundedConfig (7*(Rmax+4)+Emax+Dmax) C) :
  Probability.expectedHittingTime (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega:2≤n) C
    (fun D => FreshRankingStart D ∨ IsConsensusConfig D) ≤ ((c * Rmax * n * n : ℕ) : ENNReal)
```

## Approach — convert the qualitative path to a descent E[T]
- The qualitative proof chains phase3a_to_awakening → ... → FreshRankingStart. Identify the
  monotone progress measure along that chain (likely a phase index / awakened-count / rc-level)
  and prove a per-step descent witness (∃ pair advancing it, prob ≥ 1/(n(n-1))).
- Use `Probability.expectedHittingTime_le_of_variable_descent_until_goal` (ExpectedTime.lean:4379)
  OR `expectedHittingTime_le_of_drift` (DriftHittingTime.lean) if transient increases occur.
- Reuse existing rc-level machinery: `rcLevelPotential_*` (RecoveryBound.lean.bak2 / RecoveryBound.lean:
  rcLevelPotential_step_nonincrease, rcLevelPotential_one_step_drop_prob, rcLevelPotential_zero_goal)
  — these already give a NONINCREASING rc-level potential with a per-step drop probability. That is
  very likely the entry descent's backbone (reset wave drains rc).

## FIRST sub-goal (report before the full bound)
Identify the progress measure for dormant→FreshRankingStart and state+prove its per-step descent
witness (or report the exact obstruction + which existing lemma is closest). The rc-level potential
machinery is the strongest lead — check whether `rcLevelPotential = 0` plus awakening implies
FreshRankingStart, which would reduce the entry bound to the existing rc-level drop machinery.

## HARD RULES
- NO sorry/axiom/native_decide in the final theorem. Blocked → exact obstruction to
  HANDOFF/outbox/codex-entry-report.md. ONLY new EntryBound.lean. Self-verify lake env lean.
  NEVER lake build. Report status precisely (PROVED / PROVED-modulo-X / BLOCKED-at-Y).
