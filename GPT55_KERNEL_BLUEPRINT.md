Channel: exact_mj (explicit; tmux window: family)
Task c5de57ad [#4] submitted, pipe waiting (timeout 1190s)...
I’ll reframe sections 1–3 as Lean-oriented definitions, schedules, and lemma signatures, first checking existing names so the plan matches the repository rather than inventing interfaces.

I’ll avoid the opaque ranking_from_all_resetting route and instead spell out the explicit safe-schedule blueprint, separating the measures, schedule phases, and lemma signatures.

下面重发并细化 section 1–3。先给一个重要修正：完整 kernel 最稳的落点不是 all_resetting_uniform_to_InSswap_uniform，而是 all_resetting_uniform_to_InSswap_ResAns。
如果初始 all-Resetting 里没有 .L leader，显式 schedule 可能必须经过 Unsettled timeout 产生新 .L reset，这个分支会把 newly-Resetting 的 answer wipe 成 .phi。所以“全程 uniform m₀”一般过强；但 ResAns m₀ := ∀ w, answer=m₀ ∨ answer=.phi 是正确不变量。最后再用你已有的 phiCount/cycle_potential_reaches_consensus 把 InSswap ∧ ResAns 推到 IsConsensusConfig。

RankingEndpoint 现有定义也支持这个分阶段视角：它只是 InSrank ∧ (timer≥2@median ∨ IsConsensusConfig)，并不承诺 answer endpoint。

BurmanProof

 InStim_iff_IsConsensusConfig 则是最终把 InSswap + InSout 关成 IsConsensusConfig 的桥。

Sets

1. 势函数 / 终止测度的精确定义
1.1 Tree/ranking phase：未招聘目标 rank 数

你要避免 opaque ranking_from_all_resetting，所以 binary-tree ranking 阶段需要一个显式 partial-tree invariant。最干净的测度是“还有多少 target rank 没有被 Settled agent 占据”。

Lean 定义建议：

lean
def settledRanks (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter
    (fun ρ : Fin n =>
      ∃ w : Fin n, (C w).1.role = .Settled ∧ (C w).1.rank = ρ)

def unrecruitedTargetRanks (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ \ settledRanks C

def unrecruitedTargetRankCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (unrecruitedTargetRanks C).card

但在 Lean 里 Finset.sdiff 有时麻烦，等价地写成 filter 更好：

lean
def unrecruitedTargetRanks (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter
    (fun ρ : Fin n =>
      ¬ ∃ w : Fin n, (C w).1.role = .Settled ∧ (C w).1.rank = ρ)

def unrecruitedTargetRankCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (unrecruitedTargetRanks C).card

每次合法 recruit：

lean
Settled parent with children<2 × Unsettled child

产生一个新 child rank：

lean
childRank = 2 * parent.rank.val + parent.children + 1

这个 rank 以前未被占据，step 后被 child 占据，所以 unrecruitedTargetRankCount 严格下降。现有 rankDeltaOSSR_recruits 已经给了这个 childRank trace。

BurmanProof

实际更强、更好 induction 的 invariant 是 prefix 版本：

lean
def BinaryTreePrefix (C : Config (AgentState n) Opinion n) (k : ℕ) : Prop :=
  k ≤ n ∧
  (∀ ρ : Fin n, ρ.val < k →
    ∃! w : Fin n,
      (C w).1.role = .Settled ∧ (C w).1.rank = ρ) ∧
  (∀ w : Fin n, (C w).1.role = .Settled → (C w).1.rank.val < k) ∧
  (∀ w : Fin n, k ≤ (C w).1.rank.val → (C w).1.role ≠ .Settled)

然后测度就是：

lean
def treeRemaining (k : ℕ) : ℕ := n - k

如果你按 BFS rank order recruit，即先处理 rank 0 的 child 1,2，再 rank 1 的 child 3,4，等等，那么第 k 步后已占据 ranks < k，下一个目标 rank 正好是 k。这个比任意 unrecruitedTargetRanks 更容易证明 parent ready。

1.2 Swap phase：misorderedCount

数学定义：

lean
def MisorderedPair (C : Config (AgentState n) Opinion n) (u v : Fin n) : Prop :=
  (C u).1.rank < (C v).1.rank ∧
  (C u).2 = Opinion.B ∧
  (C v).2 = Opinion.A

def misorderedCountExplicit (C : Config (AgentState n) Opinion n) : ℕ :=
  ((Finset.univ.product Finset.univ).filter
    (fun p : Fin n × Fin n => MisorderedPair C p.1 p.2)).card

如果项目已有 misorderedCount，继续用已有定义；这个只是精确数学形式。InSswap 就是 InSrank 加上 “rank 与 input 排序一致”：A iff rank.val < nAOf C。

Sets

每次选择一个 answer-safe misordered pair 做 phase4_swap，misorderedCount 严格下降。已有 swap machinery 大概率已经证明了普通 misorder decrease；你需要加的是 answer-safe 选择。

1.3 Answer-safety predicate：MedianSafeAnswerInput

不要只写“median-safe C”。真正需要的是：你计划调度的每个 pair，transitionPEM 后两端 answer 仍在允许集合里。

对于 uniform 版本：

lean
def PairUniformAnswerSafe
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (m₀ : Answer)
    (C : Config (AgentState n) Opinion n)
    (u v : Fin n) : Prop :=
  let out :=
    transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (C u, C v)
  out.1.answer = m₀ ∧ out.2.answer = m₀

但完整 kernel 更应使用 ResAns：

lean
def AnswerInResAns (m₀ : Answer) (a : Answer) : Prop :=
  a = m₀ ∨ a = .phi

def PairResAnsSafe
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (m₀ : Answer)
    (C : Config (AgentState n) Opinion n)
    (u v : Fin n) : Prop :=
  let out :=
    transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (C u, C v)
  AnswerInResAns m₀ out.1.answer ∧
  AnswerInResAns m₀ out.2.answer

然后：

lean
def MedianSafeAnswerInput
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (m₀ : Answer)
    (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ u v : Fin n,
    ScheduledPairAllowed C u v →
      PairResAnsSafe (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) m₀ C u v

这里 ScheduledPairAllowed 不要做成全局“任意 pair”，否则太强。建议分相位定义：

lean
inductive ScheduledPairAllowed
    (C : Config (AgentState n) Opinion n) (u v : Fin n) : Prop
  | reset_pair :
      (C u).1.role = .Resetting →
      (C v).1.role = .Resetting →
      ScheduledPairAllowed C u v
  | recruit_pair :
      (C u).1.role = .Settled →
      (C v).1.role = .Unsettled →
      (C u).1.children < 2 →
      2 * (C u).1.rank.val + (C u).1.children + 1 < n →
      ScheduledPairAllowed C u v
  | safe_swap_pair :
      InSrank C →
      MisorderedPair C u v →
      PairResAnsSafe (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) m₀ C u v →
      ScheduledPairAllowed C u v

在 Lean 中这可能要拆成三个 local lemmas，而不是一个 inductive predicate；但数学结构就是这个。

1.4 Lexicographic / staged composition

不要试图做一个全局 monotone：

lean
wrongAnswerCount

它会被 reset 打爆。正确形式是 nested phase proof：

lean
Phase.ResetNormalize : resetFuel / nonResettingCount / rc budget
Phase.TreeRank       : unrecruitedTargetRankCount 或 n-k
Phase.SafeSwap       : misorderedCount
Phase.AnswerRepair   : phiCount under InSswap ∧ ResAns
Phase.Done           : IsConsensusConfig

严格说不是一个单一 Nat 势函数，而是：

lean
Outer:
  eventually reach InSswap ∧ ResAns

Then:
  use phiCount macro-potential under Pinv := InSswap ∧ ResAns

如果你非要一个 Lean 里的 lex relation，可定义：

lean
inductive SafePhase
  | reset
  | tree
  | swap
  | repair
  | done
  deriving DecidableEq

def phaseRank : SafePhase → ℕ
  | .reset  => 4
  | .tree   => 3
  | .swap   => 2
  | .repair => 1
  | .done   => 0

def localMeasure (φ : SafePhase) (C : Config (AgentState n) Opinion n) : ℕ :=
  match φ with
  | .reset  => resetFuel C
  | .tree   => unrecruitedTargetRankCount C
  | .swap   => misorderedCount C
  | .repair => phiCount C
  | .done   => 0

def stagedMeasure (φ : SafePhase) (C : Config (AgentState n) Opinion n) : ℕ × ℕ :=
  (phaseRank φ, localMeasure φ C)

但实际证明中最好不要真的用这个全局 measure；直接写阶段 lemma 更少痛苦。

2. 显式 deterministic schedule 的 phase 结构
Phase A：all-Resetting normalize / sync

输入：

lean
∀ w, (C w).1.role = .Resetting
∀ w, (C w).1.answer = m₀
m₀ = majorityAnswer C

目标不是马上 InSrank，而是：

lean
FreshRankingStart C₁ ∧ ResAns m₀ C₁ ∧ majorityAnswer C₁ = majorityAnswer C

FreshRankingStart 已定义为一个 Settled root rank 0 children 0，其余 Unsettled。

BurmanProof

schedule 结构：

若存在 .L leader：
用 Resetting–Resetting interactions 做 leader dedup / rc sync / drain to dormant。只调度 Resetting pairs，因此 answer 不会离开 {m₀, .phi}；在初始全 m₀ 且不产生 new Resetting 的子段里甚至保持全 m₀。

若没有 .L leader：
让 follower dormant agents wake to Unsettled；再用 Unsettled errorcount timeout 产生 .L reset seed。这个 seed 可能 answer .phi，所以此处是你必须放弃 uniform、改用 ResAns m₀ 的地方。随后 reset propagation 仍保持 ResAns.

唤醒唯一 leader：
.L Resetting rc=0 wake 成 Settled rank 0；其它 .F agents wake/settle into Unsettled. 这个阶段只需要保持 ResAns.

Lean 子引理：

lean
theorem all_resetting_uniform_to_fresh_start_ResAns
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hAllR : ∀ w, (C w).1.role = .Resetting)
    (hm : m₀ = majorityAnswer C)
    (hAns : ∀ w, (C w).1.answer = m₀) :
    ∃ L,
      let C₁ := runPairs
        (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      FreshRankingStart C₁ ∧
      ResAns m₀ C₁ ∧
      majorityAnswer C₁ = majorityAnswer C

用到：

rankDeltaOSSR_answer_preserved / propagateReset_answer_preserved

step_preserves_ResAns_of_not_both_settled

transitionPEM_phase4_of_not_both_settled

majorityAnswer_step_eq / runPairs/execution invariance。majorityAnswer step/execution invariance 已在 Step.lean。

Step

Phase B：binary-tree recruit

从 FreshRankingStart 出发，按 BFS rank order recruit：

queue parent rank 0

parent rank 0 recruits child rank 1, then 2

parent rank 1 recruits child rank 3, then 4

parent rank 2 recruits child rank 5, then 6

...

直到 ranks 0..n-1 都被占据

每一步调度：

lean
(parentWithRank p, someUnsettledChild)

其中 child 被赋予：

lean
childRank = 2 * p + parent.children + 1

这个就是 rankDeltaOSSR_recruits 的 trace。

BurmanProof

关键 answer 安全：

rankDelta recruit 本身不改 answer；

prePhase4 只在 newly Resetting 时 wipe answer，但 recruit 是 Settled/Unsettled → Settled/Settled，不是 Resetting；

phase4 会在 both Settled 后运行，但通常 decision 不触发，除非新 recruit 或 parent 位于 median-relevant ranks；

若 decision 触发，要证明写入 answer 仍是 m₀ 或 .phi。这里有两条路：

推荐：在 tree phase 只维护 ResAns，不强求 uniform。
如果 decision 写错为非 m₀/non-phi，那就坏；所以要保证所有可能触发的 decision 写入 m₀。这由 MedianSafeAnswerInput 保证。

更具体的 recruit-safe lemma：

lean
theorem recruit_step_preserves_ResAns_if_decision_safe
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    {p child : Fin n}
    (hp : (C p).1.role = .Settled)
    (hc : (C child).1.role = .Unsettled)
    (hchildren : (C p).1.children < 2)
    (hvalid : 2 * (C p).1.rank.val + (C p).1.children + 1 < n)
    (hRes : ResAns m₀ C)
    (hDecisionSafe :
      PairResAnsSafe (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) m₀ C p child) :
    let C₁ := C.step
      (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p child
    ResAns m₀ C₁

然后 tree induction：

lean
theorem fresh_start_ResAns_to_InSrank_safe
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hFresh : FreshRankingStart C)
    (hm : m₀ = majorityAnswer C)
    (hRes : ResAns m₀ C) :
    ∃ L,
      let C₁ := runPairs
        (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C₁ ∧
      ResAns m₀ C₁ ∧
      MedianSafeForSwap m₀ C₁ ∧
      majorityAnswer C₁ = majorityAnswer C

这里 MedianSafeForSwap 是给 swap phase 用的安全选择谓词。

Phase C：第一次允许 both-Settled decision

你不需要“禁止 both-Settled phase4_decide”。你需要更精确地说：

第一次可能影响 median answer 的 both-Settled interaction，要么 decision branch 不触发，要么触发后写入 m₀。

具体：

recruit 阶段：只有 parent × newly recruited child。你可以选 child，使其在成为 median rank 时，其 opinion 满足 opinionToAnswer = m₀。
对 odd n，唯一 median rank 是 ceilHalf n - 1，这个 rank 必须由 majority-side opinion agent 填上。
对 even n，lower/upper median pair 的 decision output 要符合 majority/tie。tie 时 outT；非 tie 时避免 exact median-pair disagreement decision。

swap 阶段：如果一个 misordered swap 涉及 median rank，phase4_swap 先交换 states，再 phase4_decide；所以要证明 post-swap 拿到 median rank 的 input 是 majority-side input。
这不是 InSswap 全局定理，而是局部 arithmetic lemma。

建议定义：

lean
def PairDecidesTo
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (m₀ : Answer)
    (C : Config (AgentState n) Opinion n)
    (u v : Fin n) : Prop :=
  let a := phase4_swap (C u).1 (C v).1 (C u).2 (C v).2
  let b := phase4_decide n a.1 a.2 (C u).2 (C v).2
  b.1.answer = m₀ ∧ b.2.answer = m₀

Then prove local lemmas:

lean
theorem odd_median_swap_decides_majority
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hm : m₀ = majorityAnswer C)
    (hpar : ¬ n % 2 = 0)
    -- pair chosen so after swap median-rank state is paired with majority-side input
    ... :
    PairDecidesTo (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) m₀ C u v
lean
theorem even_boundary_decision_safe_or_avoid
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hm : m₀ = majorityAnswer C)
    (hpar : n % 2 = 0) :
    -- either tie exact boundary writes outT=m₀,
    -- or non-tie schedule chooses a non-boundary swap, so phase4_decide does not fire

This is the key “first decide is safe” statement.

Phase D：safe swap sorting

Use misorderedCount.

At each state:

If InSswap, stop.

Else choose a misordered pair (u,v) that is answer-safe.

Important scheduling trick:

For even non-tie, avoid exact lower/upper median pair if its decision would be unsafe. Use a non-adjacent swap crossing over the unsafe boundary.
If lower median rank has wrong-side input, there exists a majority-side agent beyond the upper median, not exactly the upper median; swap with that agent instead.
Symmetric for B majority.

For tie, exact median pair decision writes .outT, which is m₀, so it is safe.

The central existence lemma:

lean
theorem exists_answer_safe_misordered_pair
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hSrank : InSrank C)
    (hNotSwap : ¬ InSswap C)
    (hm : m₀ = majorityAnswer C)
    (hRes : ResAns m₀ C)
    (hMedSafe : MedianSafeForSwap m₀ C) :
    ∃ u v : Fin n,
      u ≠ v ∧
      MisorderedPair C u v ∧
      PairResAnsSafe (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) m₀ C u v

Step lemma:

lean
theorem answer_safe_swap_step_decreases
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    {u v : Fin n}
    (hSrank : InSrank C)
    (huv : u ≠ v)
    (hMis : MisorderedPair C u v)
    (hSafe : PairResAnsSafe (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) m₀ C u v)
    (hRes : ResAns m₀ C) :
    let C₁ := C.step
      (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v
    InSrank C₁ ∧
    ResAns m₀ C₁ ∧
    misorderedCount C₁ < misorderedCount C

Then strongRec:

lean
theorem InSrank_ResAns_safe_to_InSswap_ResAns
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hSrank : InSrank C)
    (hm : m₀ = majorityAnswer C)
    (hRes : ResAns m₀ C)
    (hMedSafe : MedianSafeForSwap m₀ C) :
    ∃ L,
      let C₁ := runPairs
        (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSswap C₁ ∧
      ResAns m₀ C₁ ∧
      majorityAnswer C₁ = majorityAnswer C
Phase E：answer repair via phiCount

Once at:

lean
InSswap C ∧ ResAns m₀ C ∧ m₀ = majorityAnswer C

you do not need uniform. Use existing:

lean
cycle_potential_reaches_consensus

with:

lean
Pinv C := InSswap C ∧ ResAns m₀ C
φ C := phiCount C

The required macro-step is already essentially in your ammo:

If phiCount = 0, then ResAns implies all answers are m₀; with m₀ = majorityAnswer C, get InSout, then InStim, then IsConsensusConfig.

If median wrong/phi, median_wrong_decision_step decreases wrongAnswerCount, and under ResAns, phiCount_eq_wrongAnswerCount_of_resAns.

If median correct and some nonmedian phi, use trigger_correct_reset_from_InSrank + all_resetting_from_seed_answer_aux to reset and refill to all-Resetting with all m₀, then rerun safe ranking/swap.

3. 完整 Lean 证明骨架
3.1 核心存在引理：safe ranking + safe swap

我建议这个是主 kernel，而不是 ranking_from_all_resetting。

lean
theorem exists_safe_ranking_and_swap_schedule
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hFresh : FreshRankingStart C)
    (hm : m₀ = majorityAnswer C)
    (hRes : ResAns m₀ C) :
    ∃ L : List (Fin n × Fin n),
      let C₁ := runPairs
        (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSswap C₁ ∧
      ResAns m₀ C₁ ∧
      majorityAnswer C₁ = majorityAnswer C

Main proof skeleton:

lean
set P := protocolPEM ...
-- Phase B: explicit binary tree recruit.
obtain ⟨Lrank, hRank, hResRank, hMedSafe, hMajRank⟩ :=
  fresh_start_ResAns_to_InSrank_safe hn4 hFresh hm hRes

let Crank := runPairs P C Lrank

-- Phase D: safe swap.
obtain ⟨Lswap, hSwap, hResSwap, hMajSwap⟩ :=
  InSrank_ResAns_safe_to_InSswap_ResAns
    (C := Crank) hRank
    (by rw [hMajRank]; exact hm) hResRank hMedSafe

refine ⟨Lrank ++ Lswap, ?_⟩
rw [runPairs_append]
exact ⟨hSwap, hResSwap, hMajRank.trans hMajSwap⟩

Sublemmas needed:

lean
theorem fresh_start_ResAns_to_InSrank_safe
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hFresh : FreshRankingStart C)
    (hm : m₀ = majorityAnswer C)
    (hRes : ResAns m₀ C) :
    ∃ L,
      let C₁ := runPairs
        (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C₁ ∧
      ResAns m₀ C₁ ∧
      MedianSafeForSwap m₀ C₁ ∧
      majorityAnswer C₁ = majorityAnswer C

Use:

rankDeltaOSSR_recruits

rankDeltaOSSR_answer_preserved

transitionPEM_phase4_of_not_both_settled when applicable

phase4_propagate_no_reset_of_eq_answer

majorityAnswer_step_eq

lean
theorem recruit_step_preserves_ResAns_if_decision_safe
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    {p child : Fin n}
    (hp : (C p).1.role = .Settled)
    (hc : (C child).1.role = .Unsettled)
    (hchildren : (C p).1.children < 2)
    (hvalid : 2 * (C p).1.rank.val + (C p).1.children + 1 < n)
    (hRes : ResAns m₀ C)
    (hSafe : PairResAnsSafe (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) m₀ C p child) :
    let C₁ := C.step
      (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p child
    ResAns m₀ C₁
lean
theorem InSrank_ResAns_safe_to_InSswap_ResAns
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hSrank : InSrank C)
    (hm : m₀ = majorityAnswer C)
    (hRes : ResAns m₀ C)
    (hMedSafe : MedianSafeForSwap m₀ C) :
    ∃ L,
      let C₁ := runPairs
        (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSswap C₁ ∧
      ResAns m₀ C₁ ∧
      majorityAnswer C₁ = majorityAnswer C

Proof by strong recursion on misorderedCount C:

lean
by_cases hSwap : InSswap C
  exact ⟨[], hSwap, hRes, rfl⟩
else
  obtain ⟨u,v,huv,hMis,hSafe⟩ :=
    exists_answer_safe_misordered_pair hSrank hSwap hm hRes hMedSafe
  have hStep :=
    answer_safe_swap_step_decreases hSrank huv hMis hSafe hRes
  recurse on C.step P u v
lean
theorem exists_answer_safe_misordered_pair
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hSrank : InSrank C)
    (hNotSwap : ¬ InSswap C)
    (hm : m₀ = majorityAnswer C)
    (hRes : ResAns m₀ C)
    (hMedSafe : MedianSafeForSwap m₀ C) :
    ∃ u v : Fin n,
      u ≠ v ∧
      MisorderedPair C u v ∧
      PairResAnsSafe (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) m₀ C u v

This is the combinatorial heart.

Use:

if a safe non-median misorder exists, choose it;

if only unsafe candidate is even median boundary, prove tie makes it safe, or non-tie gives a non-boundary alternative;

if odd median crossing, prove post-swap median input is majority-side, so decision writes m₀.

lean
theorem answer_safe_swap_step_decreases
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    {u v : Fin n}
    (hSrank : InSrank C)
    (huv : u ≠ v)
    (hMis : MisorderedPair C u v)
    (hSafe : PairResAnsSafe (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) m₀ C u v)
    (hRes : ResAns m₀ C) :
    let C₁ := C.step
      (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v
    InSrank C₁ ∧
    ResAns m₀ C₁ ∧
    MedianSafeForSwap m₀ C₁ ∧
    misorderedCount C₁ < misorderedCount C

Use:

existing swap decrease lemma or swap_step_decreases_at_misorder_of_role_settled;

hSafe for endpoint answers;

other agents unchanged;

majorityAnswer_step_eq;

local arithmetic to update MedianSafeForSwap.

3.2 From all-Resetting uniform to InSswap ∧ ResAns

This replaces the too-strong uniform version.

lean
theorem all_resetting_uniform_to_InSswap_ResAns
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hAllR : ∀ w, (C w).1.role = .Resetting)
    (hm : m₀ = majorityAnswer C)
    (hAns : ∀ w, (C w).1.answer = m₀) :
    ∃ L : List (Fin n × Fin n),
      let C₁ := runPairs
        (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSswap C₁ ∧
      ResAns m₀ C₁ ∧
      majorityAnswer C₁ = majorityAnswer C

Main proof skeleton:

lean
set P := protocolPEM ...

have hRes0 : ResAns m₀ C := by
  intro w
  exact Or.inl (hAns w)

obtain ⟨Lfresh, hFresh, hResFresh, hMajFresh⟩ :=
  all_resetting_uniform_to_fresh_start_ResAns
    hn4 hEmax hDmax hAllR hm hAns

let Cfresh := runPairs P C Lfresh

obtain ⟨Lsafe, hSwap, hResSwap, hMajSafe⟩ :=
  exists_safe_ranking_and_swap_schedule
    hn4 hEmax hDmax hFresh
    (by rw [hMajFresh]; exact hm)
    hResFresh

refine ⟨Lfresh ++ Lsafe, ?_⟩
rw [runPairs_append]
exact ⟨hSwap, hResSwap, hMajFresh.trans hMajSafe⟩

Sublemma:

lean
theorem all_resetting_uniform_to_fresh_start_ResAns
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hAllR : ∀ w, (C w).1.role = .Resetting)
    (hm : m₀ = majorityAnswer C)
    (hAns : ∀ w, (C w).1.answer = m₀) :
    ∃ L,
      let C₁ := runPairs
        (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      FreshRankingStart C₁ ∧
      ResAns m₀ C₁ ∧
      majorityAnswer C₁ = majorityAnswer C

Use existing reset/dormant/wake machinery, plus:

rankDeltaOSSR_answer_preserved

propagateReset_answer_preserved

step_preserves_ResAns_of_not_both_settled

if an Unsettled timeout wipe occurs, show the new answer is .phi, hence still ResAns.

3.3 Final kernel after section 3

Not full code, but exact proof shape:

lean
theorem all_resetting_uniform_consensus_final
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hAllR : ∀ w, (C w).1.role = .Resetting)
    (hm : m₀ = majorityAnswer C)
    (hAns : ∀ w, (C w).1.answer = m₀) :
    ∃ γ t,
      IsConsensusConfig
        (execution
          (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
          C γ t)

Proof:

Run all_resetting_uniform_to_InSswap_ResAns, get list L₁, state C₁.

Convert runPairs to scheduler prefix with exists_schedule_of_runPairs.

On C₁, apply cycle_potential_reaches_consensus with:

lean
Pinv C := InSswap C ∧ ResAns m₀ C
φ C := phiCount C

Macro-step cases:

phiCount=0: ResAns gives all answer m₀; with m₀ = majorityAnswer C₁, build InSout, then InStim, then IsConsensusConfig via InStim_iff_IsConsensusConfig.

phiCount>0 and median phi/wrong: use median_wrong_decision_step, phiCount_eq_wrongAnswerCount_of_resAns.

median correct + nonmedian phi: use trigger_correct_reset_from_InSrank + all_resetting_from_seed_answer_aux, then recursively all_resetting_uniform_to_InSswap_ResAns.

This is the final loop: safe explicit schedule into InSswap ∧ ResAns; then answer-repair macro by phiCount; then InStim_iff_IsConsensusConfig.
