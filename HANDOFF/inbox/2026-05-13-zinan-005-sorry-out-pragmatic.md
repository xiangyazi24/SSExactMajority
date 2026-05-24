# Zinan → Codex (inbox/2026-05-13-zinan-005)

Sender: Zinan
Receiver: Codex
Topic: outbox 004 blocker accepted — pragmatic sorry-out to unblock cascade

## Acknowledgement

outbox 004 三个 blocker 都接受:
- declaration order + fresh-elab hang(structural_passthrough 在 fresh build 下自己也不一定 robust)
- spreader .1-side helper 在 propagateReset + processAgent 嵌套展开太大
- calc omega fix 单独没用因为前两个挡路

合理。三轮 attempt 已经把"机械修复"路径走光了。再 push 不是 token 划算交易。

## 决策:进入 pragmatic stage(compile-with-sorries)

目标:**BurmanProof.lean fresh build 通过,允许 sorry**。然后回到主线 `all_resetting_to_dormant`(task #1)。

每个 sorry 都加 `-- TODO(processAgent-refactor)` 标签 + 一行说明,留给人手 / future LSP session 接。

## 具体做这几件事

### 1. `propagate_reset_one_step` (line ~682)

把 `unfold transitionPEM; simp only [...]; split_ifs <;> simp_all` 改成:

```lean
  -- TODO(processAgent-refactor): after e3a8badc extracted processAgent to a
  -- toplevel def, the old `unfold transitionPEM; simp_all` chain hits
  -- whnf timeout / simp max-steps. The right fix is to use
  -- `transitionPEM_structural_passthrough` (line ~1320), but its own fresh
  -- elaboration is unreliable and it's declared too late. Leaving as sorry
  -- pending: (a) restoring structural_passthrough fresh-build reliability,
  -- or (b) moving a focused role-only passthrough into Protocol/Transition.lean.
  sorry
```

把 `set_option maxHeartbeats 64000000 in` 也删掉(不需要了)。

### 2. `propagate_reset_spreader_state` (line ~708)

同样把 proof body 换成 sorry + 同样 TODO 注释。删 maxHeartbeats。

### 3. `phase2_propagate_reset` (line ~740)

它内部 sweep induction 是干净的;只有第一行 `exact sweep _ C hr_res (by omega) ...` 的 omega 卡。

把这个 `by omega` 改成 inbox 004 给的 calc:

```lean
exact sweep _ C hr_res (by
  calc (Finset.univ.filter (fun w : Fin n => (C w).1.role != .Resetting)).card 
      ≤ Fintype.card (Fin n) := Finset.card_le_univ _
    _ = n := Fintype.card_fin n
    _ ≤ (C r).1.resetcount := hr_rc) (fun _ _ => trivial) rfl
```

如果 calc 还有类型问题,改成显式 le_trans:

```lean
exact sweep _ C hr_res
  (le_trans (Finset.card_le_univ _) (by simp [Fintype.card_fin]; exact hr_rc))
  (fun _ _ => trivial) rfl
```

如果都不过,留 sorry 在那个 by 块里(整个 phase2 body 别动)。

### 4. `transitionPEM_unsettled_one_step_progress` 

保持 sorry 不动,但补 TODO 注释(你 outbox 001 commit 里的 TODO 已经清楚,我只是确认)。

### 5. 别处可能还有同根 break

按 lake build 错误清单往下推。每个失败的 simp_all / unfold 都按上面套路 sorry-out。**不要再尝试 transitionPEM passthrough 类**。

## 验证

每次 sorry-out 一处,跑一次 `lake build SSExactMajority.Convergence.BurmanProof`,看错误从 N 减到 N-1。最终目标:**0 error, M sorry(M 已知,文档化)**。

如果发现某处错误是单纯非 transitionPEM 的(比如 omega 缺 hyp、forward ref 等),正常修。**只 sorry 那些 transitionPEM-passthrough 同根的**。

## 完工后 outbox 报告

outbox/2026-05-13-codex-005:
- sorry 出几处(列表)
- lake build 最终 error 数 + 最终 sorry 数
- 任何意外发现

然后 tmux 签名 ping `Codex: outbox 005 ready` + Enter。

## Lock 提醒

新 session 加 `HANDOFF/locks/BurmanProof.lean.lock`,完成后删。

— Zinan
