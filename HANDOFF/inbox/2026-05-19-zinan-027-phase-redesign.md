---
sender: zinan
receiver: next-session
topic: Phase predicate redesign for Table 2 proofs
status: open
---

# Status

4 sorry in Time.lean, 0 in ExpectedTime.lean. Build clean.

The 4 sorry's are the four Table 2 phase probabilities inside
`PEM_consensus_window_success_prob_bounded`. Everything else is proved.

# Blocker

The phase predicates don't match the paper's phase boundaries:

Paper's phases include timer state:
- Tswap = InSswap ∧ MedianTimerAtLeast 1
- Sdec = InSswap ∧ MedianAnswerCorrect ∧ MedianTimerAtLeast 1
- Stim = IsConsensusConfig

Our current predicates miss MedianTimerAtLeast:
- InSswap (no timer condition)
- InSswap ∧ MedianAnswerCorrect (no timer condition)

Also: `probReached` (exact time t) requires stability (staying in the
target), but InSswap ∧ MedianAnswerCorrect is not absorbing — 
phase4_propagate can break it via reset.

# Fix plan

1. Add timer conditions to phase predicates:
   - Phase 2: InSrank → (InSswap ∧ MedianTimerAtLeast 1) ∨ IsConsensusConfig
   - Phase 3: (InSswap ∧ MedianTimerAtLeast 1) → (InSswap ∧ MedianAnswerCorrect ∧ MedianTimerAtLeast 1)
   - Phase 4: (InSswap ∧ MedianAnswerCorrect ∧ MedianTimerAtLeast 1) → IsConsensusConfig

2. For probReached stability: each phase target should be "reached AND stable
   for the remaining time in the window". The paper's argument shows this by
   controlling the timer and reset probabilities.

3. Alternative: switch to ProbHitWithin-based composition with live-region
   wrappers (Codex wrote `PEM_phase3_live_or_exit_window` as a prototype).

# Key existing tools

- `PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound` (line 1664)
  — requires MedianTimerAtLeast 1
- `PEM_misordered_one_step_descent_prob_lower_bound` (line 888)
  — one-step swap descent
- `ProbHitWithin_ge_one_sub_pow_of_local_one_lower_bound` (line 1866)
  — geometric accumulation with live region
- Ripple: Chernoff (Concentration.lean), Janson geometric (JansonGeometric.lean),
  pair sampling (Scheduler.lean) — need PMF↔Measure bridge

# Files

- `SSExactMajority/UpperBound/Time.lean` — 4 sorry at lines 4261,4265,4270,4275
- `SSExactMajority/Probability/ExpectedTime.lean` — 0 sorry
- `HANDOFF/outbox/2026-05-19-codex-031-phase3-live-exit.md` — Codex's analysis
