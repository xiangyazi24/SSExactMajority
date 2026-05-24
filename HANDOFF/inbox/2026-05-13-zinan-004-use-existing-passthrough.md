# Zinan → Codex (inbox/2026-05-13-zinan-004)

Sender: Zinan
Receiver: Codex
Topic: outbox 003 blocker accepted; use existing `transitionPEM_structural_passthrough` instead

## Acknowledgement

outbox 003 接受。两 route 都卡 whnf timeout / simp max-steps,符合 SOP "≥2 失败 file blocker"。建议 1, 2 都太大动作,我也不想动 Protocol/Transition.lean。建议 3 (留 sorry + 继续 cascade) 我们走。

## 关键发现:已有 `transitionPEM_structural_passthrough` 就是要的工具

文件 line 1320(`transitionPEM_structural_passthrough`)已经证了:

> NOT both Settled 时,transitionPEM 输出 role/leader/rank/children/resetcount/delaytimer **全部** 等于 rankDelta 输出对应字段。
> 只有 answer + timer 可能在 Phase 2/3 变。

它的 proof 用的 pattern(line 1334-1345):

```lean
generalize hrd : rankDelta (s₀, s₁) = rd at h ⊢
obtain ⟨r₀, r₁⟩ := rd
unfold transitionPEM
rw [hrd]
simp only [h, ite_false,
  AgentState.role_with_answer, AgentState.leader_with_answer, ...]
refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> split_ifs <;> rfl
```

这正是 working pattern。你 outbox 003 attempt 里 `rw [hrd] does not see` 失败的原因可能是:
1. stdin 复现里没 import projection lemmas (`AgentState.role_with_answer` 在 `Convergence/RankPreservation.lean` line 36, `@[simp]` 标了)
2. 没做 `obtain ⟨r₀, r₁⟩ := rd` 把 rd 显式拆成 pair

在 BurmanProof.lean 里 import 链已经全在,proof 直接用就行,不要走 stdin minimal repro。

## 任务:把卡的几处改用 structural_passthrough

### A. `propagate_reset_one_step` (line ~682)

现在的 proof:
```lean
  have h_snd := Config.step_snd_state P C₀ hrv hrv.symm
  have h_rd := rankDeltaOSSR_propagate_reset (Rmax := Rmax) hr_res hr_rc hv_not hDmax
  suffices h : (transitionPEM ... (C₀ r, C₀ v)).2.role = .Resetting by
    rw [congrArg AgentState.role h_snd]; exact h
  unfold transitionPEM
  simp only [h_rd, ...]
  split_ifs <;> simp_all [...]
```

改写:
```lean
  have h_snd := Config.step_snd_state P C₀ hrv hrv.symm
  have h_rd := rankDeltaOSSR_propagate_reset (Rmax := Rmax) hr_res hr_rc hv_not hDmax
  -- h_rd : (rankDeltaOSSR Rmax Emax Dmax hn (C₀ r, C₀ v)).2.role = .Resetting
  -- rankDelta output.2.role = .Resetting ⇒ NOT both Settled
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn (C₀ r, C₀ v)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn (C₀ r, C₀ v)).2.role = .Settled) := by
    intro ⟨_, h2⟩; rw [h_rd] at h2; exact Role.noConfusion h2
  have h_pass := transitionPEM_structural_passthrough h_not_both
  -- h_pass.2.2.2.2.2.2.1 是 t.2.role = r.2.role
  rw [congrArg AgentState.role h_snd, h_pass.2.2.2.2.2.2.1]
  exact h_rd
```

注意 `transitionPEM_structural_passthrough` 返回 12-tuple,role/.../delaytimer 对 .1 和 .2 各 6 个字段。t.2.role = r.2.role 在 7 个 .1 字段之后的第 1 个,即 `.2.2.2.2.2.2.1`。请你打 ?_ 验一下 index。

### B. `propagate_reset_spreader_state` (line ~708)

同样的改写。这个证 r 那边 t.1.role = .Resetting ∧ t.1.resetcount = (C₀ r).1.resetcount - 1。

用 `rankDeltaOSSR_propagate_reset` 给 .2.role,但 .1 的 role + rc 还得用某 rankDeltaOSSR helper(可能要看现在有什么)。然后用 structural_passthrough 把它从 rd 转到 t。看一下 rankDeltaOSSR 在 hr_res ∧ hr_rc ∧ hv_not 时 .1 的 role/rc 是什么——按 Protocol/RankDelta.lean 的 propagateReset 推应该是 r 自己(因为 r 是 spreader,Phase 1 recruit 把 v 吸进去,r 不动;Phase 2 sync 把 r.rc 改成 max-1)。已有 `propagateReset_recruits` 给 .2.role,可能没有 .1 那边对应 lemma。**如果没有就新加一个**(parallel to propagateReset_recruits,叫 `propagateReset_spreader_rc_decrement`,证 .1.role = .Resetting ∧ .1.resetcount = max(s.rc-1,0))。

### C. line 696 `phase2_propagate_reset` 的 sweep omega

inbox 001 列过:`(by omega)` 缺 `filter.card ≤ n`。我之前手工试过 `Finset.card_le_univ` + `simp at h1` + `.trans hr_rc` 类型不匹配,revert 了。

你试试不带 `simp at h1` 直接 transitivity:
```lean
have hle : (Finset.univ.filter ...).card ≤ (C r).1.resetcount := by
  calc (Finset.univ.filter _).card 
      ≤ Fintype.card (Fin n) := Finset.card_le_univ _
    _ = n := Fintype.card_fin n
    _ ≤ (C r).1.resetcount := hr_rc
exact sweep _ C hr_res hle (fun _ _ => trivial) rfl
```

`calc` 不做 simp 归一化,filter 形式保留,类型应该匹配。

### D. `transitionPEM_unsettled_one_step_progress` 留 sorry 不动

按你 outbox 003 建议 3,这个 sorry 标 TODO 不动,等 file 整体 compile 通过再回来。

## 整体计划

1. 做 A, B, C(用 structural_passthrough + calc 的 omega 链)
2. lake build 看错误清单往下推
3. 第二轮 build error 报回 outbox 004
4. **outbox 完务必 tmux 签名 ping**(`Codex: outbox 004 ready` + Enter)

把 lock 重新加上 `HANDOFF/locks/BurmanProof.lean.lock`。

— Zinan
