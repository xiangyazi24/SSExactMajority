# 2026-05-15 Zinan → Codex #018 — Epidemic self-stabilization (LAST sorry)

## Status of the project

`projects/SSExactMajority`. ONE sorry remains:
`BurmanConvergenceFinal.lean` epidemic field (timer-branch).

Everything else is closed:
- ranking half: 0 sorry (incl. `partial_resetting_to_known_entry`,
  `all_resetting_from_seed_aux`, the 3 fuel-decrease lemmas).
- TWO formalization bugs found + fixed (partial_resetting over-strong
  statement; epidemic signature demanded an unreachable
  `1≤timer@median`). epidemic signature now weakened to
  `(1≤timer@median ∨ IsConsensusConfig)`, mirroring the ranking field.
  Master theorem chain (`BurmanProperties.lean`,
  `MacroStepComposition.lean`) rebuilt to consume the true signature —
  verified green (694 jobs).
- epidemic field structured: **consensus branch fully proven**; only
  the timer-branch `sorry` remains.

## The task: close the timer-branch sorry

In `burmanConvergence_concrete.epidemic` (BurmanConvergenceFinal.lean
~line 1356), the `htimer` case: we have
`InSrank R₁ ∧ (∀μ@median, 2 ≤ timer(R₁ μ))` where
`R₁ = execution P C₀ γ₁ t₁` (P = protocolPEM with rankDeltaOSSR).
Need: `∃ γ t, InSswap(exec) ∧ (∀w answer=majorityAnswer C₀) ∧
(1≤timer@median(exec) ∨ IsConsensusConfig(exec))`.

Since `InSswap ∧ all-correct ⟺ IsConsensusConfig`
(`InStim_iff_IsConsensusConfig`), it suffices to reach
`IsConsensusConfig`. The target is now TRUE (the impossible timer
post-condition was removed by the bug fix).

## Concrete mechanism (verified against Transition.lean)

1. `RankDelta.lean` has ZERO `.answer` references ⇒ `rankDeltaOSSR`
   never touches `.answer`. Ranking is answer-inert.
2. `phase4_propagate` L86-87 / L92-93: a median-mismatch reset makes
   BOTH agents `.Resetting` and the partner COPIES the median answer
   (`b₁ with answer := b₀.answer`).
3. `transitionPEM_prePhase4` L37-42: an agent entering `.Resetting`
   from non-Resetting is wiped to `.phi`. L49-56: while BOTH
   `.Resetting`, a `.phi` agent copies the other's non-`.phi` answer.
   ⇒ one correct (non-phi) Resetting agent spreads correct answer to all.
4. `phase4_decide` writes median `opinionToAnswer x = majorityAnswer`
   (`opinionToAnswer_lower_median_eq_majorityAnswer_even`,
   `opinionToAnswer_median_eq_majorityAnswer_odd`).
5. `reset_fires_at_misorder_median_v_max_odd_timer_zero`
   (ResetCycle.lean:37) is the odd-n reset-fires-with-answer-copy
   primitive — ALREADY PROVEN; need even-n analogs.
6. `majorityAnswer_step_eq` / `majorityAnswer_execution_eq`
   (Step.lean) — `majorityAnswer` invariant under execution.

The self-stabilization cycle (concrete, reuses CLOSED lemmas):
`[InSswap, median correct, some wrong]` → timer-descent to 0 at
median (TimerDescent.lean machinery) → mismatch reset fires (step 5,
answer copied) → drive to all-Resetting reusing the PROVEN
`all_resetting_from_seed_aux` while the phi-spread (step 3) carries
the correct answer to every agent → re-rank reusing the PROVEN
`reach_known_entry_from_any` / `ranking_field_proof` (answer-inert by
step 1; decide writes majorityAnswer by step 4) →
`InSswap ∧ all-correct` = `IsConsensusConfig`.

## Three new lemmas (answer-tracking overlays on CLOSED proofs)

- **A** `reset_fires_answer_copy` (Config.step level): from a
  median-mismatch trigger, one step → both `.Resetting`, both carry
  the (correct) median answer. Wrap
  `reset_fires_at_misorder_median_v_max_odd_timer_zero` +
  `Config.step_fst_state/_snd_state`; add even-n analogs. Note the
  trigger needs `timer = 0` at median, so this is preceded by
  timer-descent (TimerDescent.lean / TimerDescentNoSwap.lean).
- **B** `all_resetting_from_seed_answer`: answer-tracking twin of
  `all_resetting_from_seed_aux` (BurmanConvergenceFinal.lean). Same
  induction on `nonResettingCount`; carry the extra invariant "every
  `.Resetting` agent reached holds `majorityAnswer`", discharged at
  each `propagate_reset` step by the phi-spread (step 3). Reuse
  `propagate_reset_step_nonResettingCount_lt` (BurmanProof.lean:3504).
- **C** `rerank_preserves_all_correct`: thread
  `∀w, answer = majorityAnswer` through `reach_known_entry_from_any` +
  the ranking endpoint. Uses step 1 (rankDelta answer-inert) + step 4
  (decide writes majorityAnswer at median) + `majorityAnswer_*_eq`.

Then the timer-branch = A ∘ B ∘ C, threaded via `runPairs_append` /
`exists_schedule_after_runPairs` (both already used in
`ranking_field_proof`).

## Scope estimate

Comparable to the ranking half (which is now CLOSED). The crucial
de-risking is done: this is an answer-invariant OVERLAY on
already-proven structural lemmas, NOT a new potential function and NOT
a research black-box. Full mechanism + building blocks in
`EPIDEMIC_STRATEGY.md` (committed).

## Constraints

- No `sorry` / `axiom`. Trust nothing without `lake build`.
- Do NOT touch `BurmanProof.lean` (15000 lines, 0 sorry, stable
  foundation) — extend in `BurmanConvergenceFinal.lean`.
- The signature fix (BurmanProperties/MacroStepComposition) is correct
  and verified — build on it, do not revert.
