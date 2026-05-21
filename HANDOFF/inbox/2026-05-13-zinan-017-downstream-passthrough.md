# Zinan → Codex (inbox/2026-05-13-zinan-017)

Sender: Zinan
Receiver: Codex
Topic: Fill remaining processAgent-refactor sorry's using NOW-PROVEN structural_passthrough

## BIG NEWS

`transitionPEM_structural_passthrough` IS PROVEN (you did it in your batch clear). Build green.

This unblocks ALL downstream theorems. The pattern is established in `step_both_rc_pos` and `step_leader_dedup`:

```lean
have h_rd := <rankDelta-level trace>
have h_not_both := ... (from h_rd, Role.noConfusion)
have h_pass := transitionPEM_structural_passthrough ...
have h_fst := Config.step_fst_state P C huv
have h_snd := Config.step_snd_state P C huv huv.symm
refine ⟨?_, ?_, ...⟩
· rw [congrArg AgentState.<field> h_fst]; exact h_pass.<index> ▸ h_rd.<index>
...
```

## Task: fill remaining sorry's using this pattern

For each remaining processAgent-refactor sorry:
1. Identify what rankDelta-level trace it needs (most already exist: `rankDeltaOSSR_propagate_reset`, `rankDeltaOSSR_both_rc_pos_role`, etc.)
2. Use structural_passthrough to lift from rankDelta output to transitionPEM output
3. Use Config.step_fst/snd_state to lift to Config.step

Key downstream theorems to fill:
- `propagation_reset_fires_no_swap` (line ~185)
- `propagate_reset_one_step` (line ~528) — needs `rankDeltaOSSR_propagate_reset` + passthrough
- `propagate_reset_spreader_state` (line ~545) — same
- `phase2_propagate_reset` (line ~559) — depends on above two
- `transitionPEM_unsettled_one_step_progress` (line ~452) — needs `rankDeltaOSSR_unsettled_no_resetting_progress` + passthrough
- The cascade: unsettled_one_step_progress, unsettled_branch, phase1

For the Phase 3/4 theorems (lines 1720-1830): many may need additional rankDelta-level traces that don't exist yet. For those, sorry with specific "needs rankDelta trace for <case>" TODO.

## Protocol

Lock + outbox + tmux ping. Run `lake build` to verify. Report sorry count delta.

— Zinan
