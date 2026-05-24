# Zinan → Codex (inbox/2026-05-13-zinan-007)

Sender: Zinan
Receiver: Codex
Topic: Fill `drain_pair_rc`'s sorry — mechanical Lean elaborator fiddle work

## State

Pushed commit `7f399a79`. The rc-countdown layer for `all_resetting_to_dormant` is built up except for the sweep itself:

```
propagateReset_both_rc_pos_stay   proven
propagateReset_both_rc_pos_rc     proven (NEW)
rankDeltaOSSR_both_rc_pos_role    proven (NEW)
step_both_rc_pos                  proven modulo passthrough sorry (NEW)
drain_pair_rc                     SORRY with full sketch in /- block comment (NEW)
```

`drain_pair_rc` 在 `BurmanProof.lean` 现在大概 line 791。proof body 是 `sorry`,但 `/-  Sketch (kept for reference): ...  -/` 后面跟着完整的 Lean code 草稿(在 block comment 里),包含 strong induction structure。

## 你的任务

把那个 sketch 从 `/- ... -/` 里挖出来,replacing the `sorry` with a working proof。期间会遇到 Lean elaborator fiddle:

### 已知卡的几处

1. **`rw [hu_rc₁_eq, hv_rc₁_eq, Nat.max_self]`** — 把 (C'.step P u v u).1.resetcount → max(...). 之前 `rw` 不到 pattern。可能要 explicit `change` 或 `conv`。

2. **`Nat.max (a-1) (b-1) = Nat.max a b - 1`** with `0 < a, 0 < b` — `omega` 不直接解,我试了 `simp [Nat.max_def]; split_ifs <;> omega`(line 845-846)。如果 simp 不识别 Nat.max_def,试 `Nat.max_def`、`max_def`、或者手动 `by_cases (C' u).rc ≤ (C' v).rc` + `Nat.max_eq_right`/`Nat.max_eq_left` + `Nat.sub_le_sub_right`。

3. **`simp [Config.step, huv, hwu, hwv]`** for `h_others : ∀ w, w ≠ u → w ≠ v → C'.step P u v w = C' w`。如果 simp 不展开 Config.step,可能要 `unfold Config.step` 先。

4. **结尾的 `simp [runPairs]; exact h_step.1` 等** — 验证 `runPairs P C' [(u, v)] u = C'.step P u v u`。简单的 def equality,可能要 `change` 或 `rfl`。

### 建议测试方式

不要每次都跑整个 `lake build SSExactMajority.Convergence.BurmanProof`(7 分钟太慢)。用 `lake env lean --stdin` 单独测 `drain_pair_rc` 的 proof body,把上下文 minimal-importable 一遍。

或者:把 BurmanProof.lean 切一份 copy 到 `/tmp/drain_test.lean`,只保留 dependencies,iterate 那个文件。

### 兜底

如果你 2 attempts 还不过,**接受 sorry**,outbox 报告精确卡哪一行哪个 tactic,我下次接。不要再扩散攻击面到 transitionPEM 层。

### 协议提醒

- 加 lock `HANDOFF/locks/BurmanProof.lean.lock`(签 `Codex GPT-5.5 session: drain_pair_rc fill / inbox 007`)
- outbox 完发 tmux signed ping `Codex: outbox 007 ready` + Enter,这次别漏
- co-author tag: `Co-Authored-By: Codex (GPT-5.5) <noreply@openai.com>`

— Zinan
