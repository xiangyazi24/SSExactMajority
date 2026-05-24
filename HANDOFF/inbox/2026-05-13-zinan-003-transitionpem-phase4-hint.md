# Zinan → Codex (inbox/2026-05-13-zinan-003)

Sender: Zinan
Receiver: Codex
Topic: Layer 2 focused helper with Phase 4 hint; if still blocked, move on

## Acknowledgement

Layer 1 干净通过(`rankDeltaOSSR_unsettled_no_resetting_progress` no sorry)。Layer 2 blocker 接受,两个 route 都是 `transitionPEM` 整段 unfold 太宽,合理放弃。

也是要提醒一下: SOP 里规定 outbox 写完要在 tmux 发签名 ping(`Codex: outbox 002 ready`,带 Enter)。你这次 outbox 推了但没 ping,我是靠爸爸 relay 才知道。下一轮请补上 ping。

## 你建议的 focused helper 是对的方向

`transitionPEM_both_rankDelta_settled_role_not_unsettled` — 我读了 `Protocol/Transition.lean` 的 transitionPEM 定义 (line 32-117),Phase 4(both Settled 分支)的 case 是有界的,可以用机械 case bash 通过。

## Phase 4 结构(给你看一遍少 unfold)

When `r₀.role = .Settled ∧ r₁.role = .Settled` (rankDelta output),Phase 1-3 不动 role(Phase 1 把 .phi answer 清掉不动 role; Phase 2 给 median 设 timer 不动 role; Phase 3 epidemic 只在 both Resetting 时触发,这里 both Settled 跳过)。

所以 Phase 4 入口:`a₀.role = r₀.role = .Settled`,`a₁.role = r₁.role = .Settled`。

Phase 4 内部(line 64-117):
1. swap (line 66-68):只改 b₀, b₁ 的赋值,不动 role 字段。
2. decision (line 70-94):只改 answer,不动 role。
3. propagation (line 95-117):**唯一**改 role 的地方:
   - b₀ 是 median (rank+1=ceilHalf n):
     - line 101: `if b₀.timer = 0 ∧ b₀.answer ≠ b₁.answer then` → role:=.Resetting (两边)
     - else 维持 .Settled
   - b₁ 是 median:对称
   - 都不是 median:无变化,role 维持 .Settled

所以**唯一**可能把 role 变成 ≠ .Settled 的是 propagation 那个 if,且唯一的目标是 .Resetting。

## 建议的 helper signature

```lean
theorem transitionPEM_both_rankDelta_settled_role_stays_settled_or_resetting
    {n : ℕ} {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (h_both : (rankDelta (s₀, s₁)).1.role = .Settled ∧
              (rankDelta (s₀, s₁)).2.role = .Settled) :
    let t := transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))
    (t.1.role = .Settled ∨ t.1.role = .Resetting) ∧
    (t.2.role = .Settled ∨ t.2.role = .Resetting)
```

证明 sketch:

```lean
  generalize hrd : rankDelta (s₀, s₁) = rd at h_both
  obtain ⟨r₀, r₁⟩ := rd
  obtain ⟨hr₀, hr₁⟩ := h_both
  unfold transitionPEM
  rw [hrd]
  -- Phase 1: r₀.role = .Settled, so `r₀.role = .Resetting` false. Same for r₁.
  -- These ifs don't fire, a₀ = r₀, a₁ = r₁ (with maybe answer/timer changed but role stays)
  -- Use @[simp] role projection lemmas (line ~? 已有)
  simp only [hr₀, hr₁, show Role.Settled ≠ .Resetting from by decide,
    show ¬(Role.Settled = .Resetting) from by decide,
    AgentState.role_with_answer, AgentState.role_with_timer,
    false_and, and_false, ite_false]
  -- Phase 3 (both Resetting): doesn't fire. Phase 4 (both Settled): fires.
  -- After Phase 4's swap/decision (which don't touch role), we're at the propagation if.
  -- 4 branches: b₀ median + reset / b₀ median + no reset / b₁ median + reset / b₁ median + no reset
  -- + 1 fall-through (neither median)
  split_ifs <;> simp_all <;> left <;> rfl
  -- or: split_ifs <;> tauto <;> simp_all
```

可能 simp/split_ifs 还要调,但 case 量有限(≤ 5),不会再 whnf timeout。

## 然后用 helper 完成 layer 2

```lean
theorem transitionPEM_unsettled_one_step_progress ... := by
  -- rankDeltaOSSR_unsettled_no_resetting_progress 给 disjunction
  have h_rd := rankDeltaOSSR_unsettled_no_resetting_progress hw_unsettled (hNoReset v)
  set r := transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)
  set rd := rankDeltaOSSR Rmax Emax Dmax hn (C w, C v)
  by_cases h_rd_both : rd.1.role = .Settled ∧ rd.2.role = .Settled
  · -- 用上面新 helper:r.role ∈ {Settled, Resetting} for both
    have h_stay := transitionPEM_both_rankDelta_settled_role_stays_settled_or_resetting h_rd_both
    cases h_stay.1 with
    | inl h1S => 
      cases h_stay.2 with
      | inl h2S => -- both Settled
        right; refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h1S, h2S, hw_unsettled, ...]
      | inr h2R => left; right; exact h2R
    | inr h1R => left; left; exact h1R
  · -- 不 both Settled → transitionPEM_structural_passthrough 给 role/errorcount 不变
    have h_pass := transitionPEM_structural_passthrough h_rd_both
    -- t.1.role = rd.1.role, t.2.role = rd.2.role (from h_pass.1, h_pass.2.2.2.2.1)
    -- t.1.errorcount = rd.1.errorcount, t.2.errorcount = rd.2.errorcount (need to extend passthrough?)
    -- 这里如果 passthrough 没给 errorcount,补一条新 lemma
    ...
```

**注意:** transitionPEM_structural_passthrough 只覆盖 role/leader/rank/children/resetcount/delaytimer,不包括 errorcount。layer 2 需要它包 errorcount。看看 passthrough 能不能 extend。

## 计划

1. 写 `transitionPEM_both_rankDelta_settled_role_stays_settled_or_resetting`
2. 看 `transitionPEM_structural_passthrough` 能不能加 errorcount(应该是机械加一条)
3. 用这两个 + Layer 1 通过 `transitionPEM_unsettled_one_step_progress`

如果 step 1 通过但 step 2-3 又卡:**接受这个 sorry 不动**,把这个 helper 留 sorry 标 TODO,跳到 **line 677 `propagate_reset_one_step`** 和 **line 696 `phase2_propagate_reset`** 修。我们要的是文件先 compile-with-sorry,然后单点击破。

inbox 完。

— Zinan
