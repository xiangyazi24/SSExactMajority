# Zinan → Codex (inbox/2026-05-13-zinan-010)

Sender: Zinan
Receiver: Codex
Topic: Fill Phase A (rc countdown) in `all_resetting_to_dormant`

## State

Pushed `a88bf97d`. `all_resetting_to_dormant` now has two sorry'd phases:
- Phase A (rc countdown): line ~751, sorry
- Phase B (leader dedup): line ~764, sorry

Composition is proven (runPairs_append). Build green, 36 sorries.

## Your task: fill Phase A

Phase A needs:
```lean
∃ L_rc : List (Fin n × Fin n),
    (∀ w, (runPairs P C L_rc w).1.role = .Resetting) ∧
    (∀ w, (runPairs P C L_rc w).1.resetcount = 0) ∧
    (∃ ℓ, (runPairs P C L_rc ℓ).1.leader = .L)
```

Given: `hAllReset : ∀ w, (C w).1.role = .Resetting` and `hLeader : ∃ ℓ, (C ℓ).1.leader = .L`.

### Strategy

Strong induction on `(Finset.univ.filter (fun w : Fin n => 0 < (C w).1.resetcount)).card`.

**Base (count = 0):** all rc already 0. Return `L_rc = []`. Use hAllReset and hLeader directly.

**Step (count ≥ 2):** pick two agents u, v with rc > 0 (extract from filter card ≥ 2). Use `drain_pair_rc` to drain them. After drain:
- u, v have rc = 0, role = R
- Others unchanged
- Filter card decreased by ≥ 2 (could be exactly 2)
- Leader preserved (drain_pair_rc preserves leader? CHECK — drain_pair_rc doesn't expose leader. May need to add leader claim to drain_pair_rc's output, or separately track via `h_others w : runPairs ... w = C w` for w ≠ u, v)

Recurse.

**Step (count = 1):** sorry this case with TODO. Needs dt management (the lone rc>0 agent paired with rc=0 partner).

### Key technical note

`drain_pair_rc` gives `∀ w, w ≠ u → w ≠ v → runPairs P C L w = C w`. This means LEADER of agents other than u, v is PRESERVED (because their whole state is preserved). For u, v themselves, we don't know their leader after drain — but we don't need to. We just need ∃ ℓ with leader = L. If the original leader was NOT u or v, it's still L (by the ∀ w clause). If it WAS u or v... hmm, drain_pair_rc doesn't guarantee leader preservation for the drained pair.

Actually looking at drain_pair_rc's output: it gives role=R and rc=0 for u, v. Doesn't say anything about leader. Inside the drain, `step_both_rc_pos` calls `rankDeltaOSSR_both_rc_pos_role` which calls propagateReset + dedup. The dedup MIGHT change leader (if both L → second becomes F).

So after drain, leader of u, v might change. But we just need ∃ ANY leader=L. If there were multiple leaders initially, at least one survives after drain. If there was exactly one and it was among u, v... then after dedup it might stay or move.

For the simplest implementation: **choose u, v NOT including the leader ℓ** (since n ≥ 4, we have at least 4 agents; if ≥ 2 have rc > 0, we can find two that aren't ℓ... unless ℓ itself has rc > 0).

Hmm. If ℓ has rc > 0 and we drain it, leader might change. Actually propagateReset_both_rc_pos preserves leader (our new propagateReset_both_rc_pos_full would show this if proven). But we only have _stay (role) and _rc (rc). Leader isn't tracked.

SIMPLEST FIX: choose one of the two drain agents to be ℓ (the leader). After drain, ℓ's leader is preserved through propagateReset (leader field unchanged by Phase 2 sync; dedup only changes SECOND agent's leader to F). So if ℓ is the FIRST agent in the pair (u = ℓ), ℓ.leader stays L.

So: always drain (ℓ, w) where ℓ is the leader. First agent's leader preserved.

This means: Phase A always pairs the leader with another rc>0 agent. After drain, leader ℓ has rc=0 but leader=L preserved. Other agent w has rc=0, leader=F (from dedup if was L, or unchanged if was F).

After all drains: only ℓ has rc=0 leader=L. Others either rc=0 leader original (if not drained) or rc=0 leader=F (if drained against ℓ and was L).

This gives us `∃ ℓ, leader = L` (ℓ itself). And possibly already unique if all others became F.

**Revised strategy**: always pair with ℓ. Then count = 1 case (ℓ itself is the lone rc>0) is: ℓ.rc > 0, no other has rc > 0. Need to drain ℓ against some rc=0 partner. SORRY this case.

### Protocol

- Lock BurmanProof.lean
- 2 attempts → blocker
- Co-Authored-By + outbox + tmux signed ping `Codex: outbox 010 ready`

— Zinan
