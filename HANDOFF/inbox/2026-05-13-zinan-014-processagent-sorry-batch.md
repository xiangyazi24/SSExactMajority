# Zinan → Codex (inbox/2026-05-13-zinan-014)

Sender: Zinan
Receiver: Codex
Topic: Batch clear processAgent-refactor sorry's

## State

Pushed 31864064. Build green, 37 sorries. Phase A+B structure done with 3 localized dt sorries.

## Your task: clear the ~15 processAgent-refactor sorry's

These are ALL theorems whose proofs broke when `e3a8badc` extracted `processAgent` from an inline `let` to a toplevel `def`. The fix pattern is identical for each:

### Fix pattern

OLD (broken):
```lean
unfold rankDeltaOSSR propagateReset resetOSSR
simp only [...]
split_ifs <;> simp_all <;> omega
```

NEW (working, proven for `rankDeltaOSSR_dormant_dt_decrease` and `rankDeltaOSSR_leader_dedup_step`):
```lean
unfold rankDeltaOSSR propagateReset processAgent resetOSSR
simp [hypothesis1, hypothesis2, ..., show_dt_ne_zero, ...]
```

Just add `processAgent` to the unfold list, then `simp` with the hypotheses. The `simp` needs `delaytimer - 1 ≠ 0` for rc=0 cases (derive via `omega` from dt > 1 hypothesis).

### Which sorry's to fix

```bash
grep -n "TODO(processAgent-refactor)" BurmanProof.lean
```

For each: try the fix pattern. If `simp` doesn't close, try `split_ifs <;> simp_all`. If THAT doesn't close within default heartbeats, bump to `set_option maxHeartbeats 8000000`.

If a specific theorem still fails after 2 attempts, leave it sorry'd and note in outbox.

### Exceptions — DO NOT touch these

- `transitionPEM_structural_passthrough` — this is a different kind of sorry (generalize/rw issue, not processAgent)
- `transitionPEM_unsettled_one_step_progress` — wrapper around rankDelta trace
- `all_resetting_to_dormant` and its Phase A/B sub-proofs — those are dt/schedule issues
- Any theorem I proved (propagateReset_both_rc_pos_stay, _rc, _leader_fst, propagateReset_recruits, rankDeltaOSSR_both_rc_pos_role, step_both_rc_pos, step_leader_dedup, drain_pair_rc) — LEAVE THESE ALONE

### Protocol

Lock + outbox with per-theorem status + tmux signed ping `Codex: outbox 014 ready` + Enter. Co-author tag.

— Zinan
