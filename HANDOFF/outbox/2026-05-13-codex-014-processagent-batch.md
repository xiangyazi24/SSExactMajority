# Codex -> Zinan (outbox/2026-05-13-codex-014)

Sender: Codex
Receiver: Zinan
Topic: inbox 014 processAgent-refactor batch

## Result

Cleared 9 `sorry`s in `SSExactMajority/Convergence/BurmanProof.lean`.

Filled:

- `transitionPEM_collision_both_resetting`
- `trigger_reset_from_all_settled_non_InSrank`
- `rankDeltaOSSR_dormant_leader_wakes`
- `rankDeltaOSSR_dormant_leader_low_dt_wakes`
- `transitionPEM_dormant_dt_decrease`
- `rankDeltaOSSR_both_dormant`
- `rankDeltaOSSR_settled_meets_dormant`
- `transitionPEM_both_dormant_role`
- `transitionPEM_settled_meets_dormant_role`

Patterns used:

- Direct rankDelta dormant traces: `unfold rankDeltaOSSR propagateReset processAgent resetOSSR; simp [...]`.
- Collision wrapper: direct `unfold transitionPEM rankDeltaOSSR; simp [...]` because this theorem is before `transitionPEM_structural_passthrough`.
- Dormant transition wrappers: existing `transitionPEM_structural_passthrough` + `Config.step_fst_state` / `Config.step_snd_state`.

## Verification

- `lake env lean SSExactMajority/Convergence/BurmanProof.lean` passes.
- `lake build SSExactMajority.Convergence.BurmanProof` passes.
- Actual `sorry` lines in `BurmanProof.lean`: 28.

## Remaining blockers / not touched

Left the explicit exception families alone:

- `transitionPEM_structural_passthrough`
- `transitionPEM_unsettled_one_step_progress` and the unsettled cascade
- Phase A/B subproofs under `all_resetting_to_dormant`
- Phase 3/4 sweep and composition lemmas

Also left `propagate_reset_one_step` / `propagate_reset_spreader_state` / `phase2_propagate_reset` as-is. They are before `transitionPEM_structural_passthrough` in the file, so using that wrapper directly would require moving/duplicating the passthrough lemma or doing the old direct unfold path that previously timed out.

