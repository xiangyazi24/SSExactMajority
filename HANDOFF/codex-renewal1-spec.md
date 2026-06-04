# Codex task (uisai1): renewal step — awakening→FreshRankingStart E[T] with PROGRESS-INCLUSIVE goal

ROUTE (corrected, verified): optimal bound via renewal/window_mul_inv with constant per-epoch
success = product of per-phase ProbHitWithin (Markov on proven E[T] descents). This task closes the
awakening-phase E[T], previously blocked because Goal=FreshRankingStart made IsAwakeningConfig NOT
all-pair-closed (recruit exits it). FIX: make the recruit-exit PART OF THE GOAL.

Continue in EXISTING SSExactMajority/UpperBound/Time/EntryBound.lean (has awakening_step_descent_witness
/_prob, freshRankingStart_iff_card_zero, all PROVEN).

## Target
```
theorem awakening_to_rankingStarted_expected_le
  (hn4 : 4 ≤ n) (C) (hAwake : IsAwakeningConfig C) :
  Probability.expectedHittingTime (PEMProtocolCoupled' n Rmax Emax Dmax hn) (by omega:2≤n) C
    (fun D => FreshRankingStart D ∨ (∃ k, 2 ≤ k ∧ HeapPrefix D k) ∨ IsConsensusConfig D)
    ≤ (((awakeningResettingFollowers C).card * (n*(n-1)) : ℕ) : ENNReal)
```
via expectedHittingTime_le_of_variable_descent_until_goal (ExpectedTime.lean:4379) with
φ := awakeningResettingFollowers.card, Goal := the progress-inclusive disjunction above,
Inv := IsAwakeningConfig.

## The closure obligation (the crux of THIS task)
hInvStep needs: ∀ C, IsAwakeningConfig C → ¬Goal C → ∀ i j, IsAwakeningConfig (C.step) ∨ Goal (C.step).
i.e. from an awakening non-goal config, EVERY pair either stays awakening or reaches goal. Cases:
- the descent pair (root, resetting-follower): card drops, stays awakening (proven witness).
- a recruit pair (settled root + unsettled): → HeapPrefix grows; show it lands in Goal
  (FreshRankingStart if card hits 0, else HeapPrefix≥2). USE heapPrefix_recruit_step / the existing
  HeapPrefix machinery.
- other pairs (follower-follower, etc.): show IsAwakeningConfig preserved (roles stay
  leader-Settled + followers Unsettled/Resetting). Prove the per-pair role-preservation.
hNonincrease: card non-increasing on non-goal awakening steps (no pair raises the resetting-follower
count without hitting goal). awakening_step_descent_prob gives hp.

## FIRST sub-goal
Prove hInvStep (the all-pair closure with the progress-inclusive goal) — this was the blocker.
If a pair genuinely escapes both awakening and goal, report it EXACTLY (Opus refines the goal).
Then close awakening_to_rankingStarted_expected_le.

## HARD RULES
- NO sorry/axiom/native_decide. Blocked → exact obstruction to HANDOFF/outbox/codex-renewal1-report.md.
- ONLY EntryBound.lean. Self-verify lake env lean. NEVER lake build. Report status precisely.
