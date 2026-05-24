# Zinan → Codex (inbox/2026-05-13-zinan-008)

Sender: Zinan
Receiver: Codex
Topic: Build the multi-agent drain layer toward `all_resetting_to_dormant`

## Status

Outbox 007 acked. `drain_pair_rc` PROVEN (`a995e895`). 0 errors, 37 sorries.

## Goal of this round

Push toward filling `all_resetting_to_dormant`. The main lemma at line 653 currently is:

```lean
theorem all_resetting_to_dormant
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hLeader : ∃ ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      IsDormantConfig (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  sorry
```

## The math (what we need to schedule)

`IsDormantConfig` = all Resetting + all rc=0 + ∃! leader L + all leader ∈ {L, F}.

Starting from "all Resetting + ∃ leader L", we must schedule to reach the above. Three sub-tasks:

### A. rc countdown (some agents have rc > 0 → all rc = 0)

`drain_pair_rc` handles ONE pair with both rc > 0. To drain ALL agents:

- If only ONE agent has rc > 0: pair it with any rc=0 agent.  But `drain_pair_rc` needs BOTH > 0. So we need a new lemma `drain_one_against_zero` for "one rc > 0, other rc = 0, dt ≥ K big enough".  这个有 dt 管理细节(参考 inbox 003 里我对 propagateReset 的 dt trace 分析)。
- If ≥ 2 agents have rc > 0: pair them, drain via `drain_pair_rc`. Reduces count by 2.

Strategy: induction on `Finset.card { w | (C w).1.resetcount > 0 }` (number of rc-positive agents).

### B. Leader dedup (multiple L → unique L)

`rankDeltaOSSR`'s outer dedup if (line 130-132 of `Protocol/RankDelta.lean`) fires when both inputs are L + both Resetting. After: second's leader → F.

需要 trace 这一步并迭代,每次 dedup 一个非主 leader。

Strategy: induction on `Finset.card { w | (C w).1.leader = .L }`. When this is 1, we have unique leader.

### C. Compose

After A + B, all conditions for `IsDormantConfig` hold. The 4th clause "all L or F" is trivial since `Leader` is a 2-constructor inductive (provable by cases).

## Your task

Pick the path of least resistance:

**Option 1 (recommended)**: write a STRONG VERSION with stronger hypothesis matching what would come out of phase2_propagate_reset. Something like:

```lean
theorem all_resetting_to_dormant_post_phase2
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax_bound : n ≤ Dmax)  -- stronger Dmax
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hLeader : ∃ ℓ : Fin n, (C ℓ).1.leader = .L)
    -- post-phase2 structure: one source with rc > 0, others have rc=0 with dt fresh:
    (hSourceUnique : ∃ r : Fin n, 0 < (C r).1.resetcount ∧
        ∀ w, w ≠ r → (C w).1.resetcount = 0 ∧ n ≤ (C w).1.delaytimer)
    ...
```

然后通过 drain_pair_rc 处理 source vs another agent。

**Option 2**: write multi-agent drain with TWO sub-lemmas sorry'd (drain_one_against_zero + leader_dedup_step). The compose structure makes the proof CLEAR even if internals defer.

**Option 3**: 直接 sorry but write a 详细 sketch in the proof body (like I did for drain_pair_rc). Document what would go there.

### 约束

- 别尝试 fix transitionPEM_structural_passthrough 的上游 sorry,接受它 sorry'd
- 别 unfold processAgent / propagateReset 直接来,通过现有的 helper
- 2 attempts then file blocker
- outbox 完发 tmux signed ping `Codex: outbox 008 ready` + Enter

—— Lock + outbox + push + Co-Authored-By 标 —— 标准 SOP。

— Zinan
