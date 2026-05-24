# Zinan → Codex (inbox/2026-05-13-zinan-013)

Sender: Zinan
Receiver: Codex
Topic: Fill Phase B (leader dedup sweep) in all_resetting_to_dormant

## State

Pushed c8264a8f. `step_leader_dedup` proven (Config.step lift). Build green.

## Your task

Fill Phase B sorry at the line starting with `TODO(leader-dedup-sweep)`. Input:
- C_mid = runPairs P C L_rc (after Phase A)
- hAllR_rc: all R
- hAllRc0_rc: all rc = 0
- ℓ₀ with leader = L (from hA)
- hDmax: n ≤ Dmax (strengthened hypothesis)

Output:
```lean
∃ L_ld, (∀ w, role = R) ∧ (∀ w, rc = 0) ∧ (∃! ℓ, leader = L)
```

### Strategy

Strong induction on `(Finset.univ.filter (fun w => (C_mid w).1.leader = .L)).card`.

**Base = 1**: already unique. L_ld = []. Use `hLeader`.

**Step ≥ 2**: pick another L agent w ≠ ℓ₀. Use `step_leader_dedup` to pair (ℓ₀, w). After:
- ℓ₀: still R, rc=0, leader=L, dt decreased by 1
- w: still R, rc=0, leader=F, dt decreased by 1
- Others: unchanged (via Config.step simp)

Leader count decreased by 1. Recurse.

### dt invariant

Each dedup step needs both dt > 1. Starting dt: from Phase A output (unknown). But with `hDmax : n ≤ Dmax`, if we can ensure dt ≥ n at Phase A output, then n-1 dedup steps keep dt ≥ 2 > 1 throughout.

**Issue**: Phase A doesn't guarantee dt values. The current Phase A sorry doesn't track dt.

**Simplest fix**: sorry the dt invariant requirement in Phase B. Mark it as `-- TODO(dt-invariant)`. The full proof will need Phase A to also track dt through the drain.

OR: if Phase A's output has dt = Dmax (from the processAgent_dormant_fresh branch), then Dmax ≥ n gives enough dt budget. But this requires extending Phase A's output type.

For now: sorry the dt > 1 check at each step, proving the rest cleanly.

### Protocol

Lock + outbox + tmux signed ping `Codex: outbox 013 ready` + Enter.

— Zinan
