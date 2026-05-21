# Zinan → Codex (inbox/2026-05-13-zinan-012)

Sender: Zinan
Receiver: Codex
Topic: Fill Phase A sorry with strong induction (cases 1+2, sorry case 3)

## State

Pulled 0a8f3393. drain_pair_rc now exposes leader preservation. Build green, 37 sorries.

## Your task

Fill the Phase A sorry at line 817 in `all_resetting_to_dormant`. Use strong induction on `S.card` where `S = { w : rc > 0 }`.

### Induction shape

```lean
-- Inside the `· -- nonzero S.card` branch (line 809-817)
-- Available: hAllReset, hLeader, P already set
-- Goal: ∃ L_rc, (∀ w, role = R) ∧ (∀ w, rc = 0) ∧ (∃ ℓ, leader = L)

-- Generalize over Config and use strong induction on |S|
suffices sweep : ∀ k (C' : Config ...),
    (∀ w, (C' w).1.role = .Resetting) →
    (∃ ℓ, (C' ℓ).1.leader = .L) →
    (Finset.univ.filter (fun w => 0 < (C' w).1.resetcount)).card = k →
    ∃ L, (∀ w, (runPairs P C' L w).1.role = .R) ∧
         (∀ w, (runPairs P C' L w).1.resetcount = 0) ∧
         (∃ ℓ, (runPairs P C' L ℓ).1.leader = .L) by
  exact sweep S.card C hAllReset hLeader rfl
intro k
induction k using Nat.strongRecOn with
| ind k IH =>
  intro C' hAllR' hLeader' hCard'
  by_cases hk : k = 0
  · -- All rc = 0 already
    subst hk
    refine ⟨[], ?_, ?_, ?_⟩
    · intro w; simp [runPairs]; exact hAllR' w
    · intro w
      -- w ∉ S → rc = 0
      by_contra hw
      have : w ∈ Finset.univ.filter ... := ...
      ...
    · simpa using hLeader'
  · -- k ≥ 1
    obtain ⟨ℓ₀, hℓ₀_L⟩ := hLeader'
    by_cases hℓ₀_rc : 0 < (C' ℓ₀).1.resetcount
    · -- Case 1: leader has rc > 0
      -- Pick another w ∈ S with w ≠ ℓ₀
      have hk_ge_1 : 1 ≤ k := by omega
      ... extract w from S, w ≠ ℓ₀ ...
      -- Use drain_pair_rc (ℓ₀, w)
      obtain ⟨L_drain, hRu, hRCu, hRv, hRCv, hOthers, hLeaderPres⟩ :=
        drain_pair_rc hDmax' C' (show ℓ₀ ≠ w from ...) (hAllR' ℓ₀) (hAllR' w) hℓ₀_rc hw_rc
      -- After drain: ℓ₀.leader preserved (hLeaderPres), both rc=0, others unchanged
      -- New S' = S \ {ℓ₀, w}, card decreased by ≥ 1 (possibly 2)
      -- Recurse via IH
      ...
    · -- Case 2: leader has rc = 0
      by_cases hk_ge_2 : 2 ≤ k
      · -- ≥ 2 non-leader agents have rc > 0
        -- Pick two agents u, v ∈ S, u ≠ v (both ≠ ℓ₀ since ℓ₀ has rc = 0)
        ... extract u, v from S ...
        -- Drain (u, v) via drain_pair_rc
        -- Leader ℓ₀ preserved via hOthers (since ℓ₀ ≠ u, ℓ₀ ≠ v)
        -- New S card decreased by 2
        -- Recurse via IH
        ...
      · -- k = 1 exactly: lone rc > 0 agent, leader has rc = 0
        -- TODO(lone-agent-drain): needs dt management
        sorry
```

### Key technical details

1. **Extracting witnesses from Finset**: use `Finset.card_pos.mp` to get ∃ element. For two elements: `Finset.one_lt_card` gives two distinct elements.

2. **drain_pair_rc now returns 6 fields** (role_u, rc_u, role_v, rc_v, others_unchanged, leader_u_preserved). Use `.2.2.2.2.2` for leader.

3. **Card decrease**: after draining (u, v), `S'_card < S_card` because u, v had rc > 0 before and rc = 0 after → u, v ∉ S'. Use `Finset.card_lt_card` or similar.

4. **Role preservation**: drain_pair_rc preserves role = R for drained pair AND unchanged for others. So all agents still R after drain.

5. **Leader for case 2**: ℓ₀ ∉ {u, v} (since ℓ₀.rc = 0, u.rc > 0 and v.rc > 0). So ℓ₀'s state unchanged via `hOthers ℓ₀ (ne_of...) (ne_of...)`. Leader = L preserved.

### Don't try to prove

- Case 3 (k = 1): sorry it
- Phase B: I'll add that separately

### Protocol

Lock + outbox + tmux signed ping `Codex: outbox 012 ready` + Enter. co-author tag.

— Zinan
