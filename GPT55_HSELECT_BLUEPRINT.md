Channel: exact_mj (explicit; tmux window: family)
Task 1e3f3041 [#5] submitted, pipe waiting (timeout 1190s)...
I’ll first align the existing predicates, phase4 traces, and witness lemmas, then frame the proof around selecting an answer-safe misordered pair rather than forcing a false global invariant.

I’ll now focus the blueprint into a Lean-task decomposition for hSelect, separating geometric pair selection from local PairResAnsSafe transition facts.

下面给的是可落地的 hSelect / combinatorial heart 结构。先说两个必要修正，否则这个 lemma 会在 Lean 里反复撞墙：

exists_answer_safe_misordered_pair 必须带上
hm : m₀ = majorityAnswer D，否则 phase4_decide 写出 majorityAnswer D 时无法证明写入值属于 {m₀, .phi}。

如果要产出你列出的 timer-safe 8-way disjunction，还必须带上 median timer invariant，至少：

lean
hTimer : ∀ μ, (D μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (D μ).1.timer

否则存在 InSrank ∧ ¬InSswap 但唯一可选 misorder 触碰 median 且 median timer=0 的配置，无法满足你 disjunction 中的 1≤timer / 2≤timer cases。

InSswap 的语义就是 InSrank 加 input-by-rank sortedness，A iff rank below nAOf; 所以 ¬ InSswap 给 misordered pair 的标准内容是 rank-low B 与 rank-high A。

Sets

 Phase4 的风险点来自 phase4_swap → phase4_decide → phase4_propagate 的固定顺序。

Transition

0. 建议精确定义

先把 witness disjunction 命名，否则后面证明会不可读：

lean
def rank1 (D : Config (AgentState n) Opinion n) (u : Fin n) : ℕ :=
  (D u).1.rank.val + 1

def MisorderedPair (D : Config (AgentState n) Opinion n) (u v : Fin n) : Prop :=
  (D u).1.rank < (D v).1.rank ∧
  (D u).2 = Opinion.B ∧
  (D v).2 = Opinion.A

def AnswerInResAns (m₀ : Answer) (a : Answer) : Prop :=
  a = m₀ ∨ a = .phi

def PairResAnsSafe
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (m₀ : Answer)
    (D : Config (AgentState n) Opinion n)
    (u v : Fin n) : Prop :=
  let out :=
    transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (D u, D v)
  AnswerInResAns m₀ out.1.answer ∧
  AnswerInResAns m₀ out.2.answer

然后定义你那 8-way 大 disjunction：

lean
def AnswerSafeMisorderCase
    (D : Config (AgentState n) Opinion n)
    (u v : Fin n) : Prop :=
  (rank1 D u ≠ ceilHalf n ∧ rank1 D v ≠ ceilHalf n) ∨

  (¬ n % 2 = 0 ∧
    rank1 D u = ceilHalf n ∧
    rank1 D v ≠ n ∧
    1 ≤ (D u).1.timer) ∨

  (¬ n % 2 = 0 ∧
    rank1 D u = ceilHalf n ∧
    rank1 D v = n ∧
    2 ≤ (D u).1.timer) ∨

  (n % 2 = 0 ∧
    rank1 D u = n / 2 ∧
    rank1 D v = n / 2 + 1 ∧
    4 ≤ n) ∨

  (¬ n % 2 = 0 ∧
    rank1 D v = ceilHalf n ∧
    1 ≤ (D v).1.timer) ∨

  (n % 2 = 0 ∧
    rank1 D v = n / 2 ∧
    1 ≤ (D v).1.timer ∧
    4 ≤ n) ∨

  (n % 2 = 0 ∧
    rank1 D u = n / 2 ∧
    rank1 D v ≠ n / 2 + 1 ∧
    rank1 D v ≠ n ∧
    1 ≤ (D u).1.timer ∧
    4 ≤ n) ∨

  (n % 2 = 0 ∧
    rank1 D u = n / 2 ∧
    rank1 D v = n ∧
    2 ≤ (D u).1.timer ∧
    4 ≤ n)

最终 hSelect 的正确签名建议是：

lean
theorem exists_answer_safe_misordered_pair
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hm : m₀ = majorityAnswer D)
    (hS : InSrank D)
    (hRes : ResAns m₀ D)
    (hTimer : ∀ μ, rank1 D μ = ceilHalf n → 2 ≤ (D μ).1.timer)
    (hNotSwap : ¬ InSswap D) :
    ∃ u v : Fin n,
      MisorderedPair D u v ∧
      AnswerSafeMisorderCase D u v ∧
      PairResAnsSafe
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        m₀ D u v

如果你后续的 step lemma 要保持 InSrank，建议再加强为：

lean
PairNoResetAndResAnsSafe m₀ D u v

因为 PairResAnsSafe 只管 answer，不能阻止 phase4_propagate reset 破坏 InSrank。

1. 选择算法：几何分类

设 misordered pair 是：

lean
rank_u < rank_v, input_u = B, input_v = A

也就是 rank-low B 与 rank-high A。phase4_swap 会交换 state，但 input 不交换；所以 swap 后：

低 rank state 落到 A input 位置；

高 rank state 落到 B input 位置。

因此如果 touched rank 是 odd median：

若 rank_u = median，swap 后 median rank 搭配 A input，decision 写 .outA。

若 rank_v = median，swap 后 median rank 搭配 B input，decision 写 .outB。

这就是 odd case 的核心。

Step 1：先找非 median misorder

先证：

lean
lemma exists_nonmedian_misorder_or_all_misorders_touch_median
    (hMis : ∃ u v, MisorderedPair D u v) :
    (∃ u v,
       MisorderedPair D u v ∧
       rank1 D u ≠ ceilHalf n ∧
       rank1 D v ≠ ceilHalf n) ∨
    (∀ u v,
       MisorderedPair D u v →
       rank1 D u = ceilHalf n ∨ rank1 D v = ceilHalf n)

若左支成立，直接选择该 pair，对应 disjunct 1。
为什么安全：phase4_decide 不触碰 odd median；even 时 ceilHalf n = n/2，没有 lower-median rank，所以 even median-pair decision 也不会触发。phase4_propagate 的 outer median checks 也不触发。answer 只来自原 states，hRes 直接给 PairResAnsSafe。

具体安全 lemma：

lean
theorem PairResAnsSafe_of_nonmedian_misorder
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    {u v : Fin n}
    (hS : InSrank D)
    (hRes : ResAns m₀ D)
    (hMis : MisorderedPair D u v)
    (hu_ne_med : rank1 D u ≠ ceilHalf n)
    (hv_ne_med : rank1 D v ≠ ceilHalf n) :
    PairResAnsSafe
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      m₀ D u v

Proof chain:

u ≠ v from rank inequality.

all Settled from hS.

ranks distinct from hS.ranks_inj.

rankDeltaOSSR_settled_distinct_ranks gives rankDelta identity.

prePhase4 no wipe because no Resetting and already Settled.

swap fires by hMis.

decision no-op because no median / no lower median.

propagate no-op because no median.

answers are just swapped original answers; hRes u, hRes v.

Step 2：若所有 misorders touch median，split parity
Odd case

Let hodd : ¬ n % 2 = 0.

Use majority split:

lean
nAOf D > nBOf D  -- A majority, m₀ = .outA
nAOf D < nBOf D  -- B majority, m₀ = .outB

Odd has no tie. You need helper:

lean
lemma majorityAnswer_eq_outA_of_gt
    (hm : m₀ = majorityAnswer D)
    (hgt : nAOf D > nBOf D) :
    m₀ = .outA

lemma majorityAnswer_eq_outB_of_lt
    (hm : m₀ = majorityAnswer D)
    (hlt : nAOf D < nBOf D) :
    m₀ = .outB
Odd + A majority

If no nonmedian misorder exists, any inversion must touch median. For A majority, unsafe orientation rank_v = median cannot be the only possibility; counting forces existence of a misorder with rank_u = median and input_v=A above it. Intuition: A majority means sorted median should be A; if an A at median is being crossed by B below, there is still an A above or a nonmedian inversion.

Formal helper:

lean
theorem odd_Amajor_all_touch_median_exists_lower_median_misorder
    {D : Config (AgentState n) Opinion n}
    (hS : InSrank D)
    (hodd : ¬ n % 2 = 0)
    (hA : nAOf D > nBOf D)
    (hMisExists : ∃ u v, MisorderedPair D u v)
    (hAllTouch :
      ∀ u v, MisorderedPair D u v →
        rank1 D u = ceilHalf n ∨ rank1 D v = ceilHalf n) :
    ∃ u v,
      MisorderedPair D u v ∧
      rank1 D u = ceilHalf n

Then split rank1 D v = n.

If v is not max: use disjunct 2. Timer 1≤timer_u from hTimer u.

If v is max: use disjunct 3. Timer 2≤timer_u from hTimer u.

Safety lemma:

lean
theorem PairResAnsSafe_of_odd_lower_median_Amajor
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    {u v : Fin n}
    (hm : m₀ = majorityAnswer D)
    (hA : nAOf D > nBOf D)
    (hS : InSrank D)
    (hRes : ResAns m₀ D)
    (hodd : ¬ n % 2 = 0)
    (hMis : MisorderedPair D u v)
    (hu_med : rank1 D u = ceilHalf n) :
    PairResAnsSafe
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      m₀ D u v

After swap, median rank state is paired with input v, which is A; odd decision writes opinionToAnswer A = .outA = m₀.

Odd + B majority

Symmetric. Counting gives misorder with rank_v = median:

lean
theorem odd_Bmajor_all_touch_median_exists_upper_median_misorder
    {D : Config (AgentState n) Opinion n}
    (hS : InSrank D)
    (hodd : ¬ n % 2 = 0)
    (hB : nAOf D < nBOf D)
    (hMisExists : ∃ u v, MisorderedPair D u v)
    (hAllTouch :
      ∀ u v, MisorderedPair D u v →
        rank1 D u = ceilHalf n ∨ rank1 D v = ceilHalf n) :
    ∃ u v,
      MisorderedPair D u v ∧
      rank1 D v = ceilHalf n

Use disjunct 5. Timer from hTimer v.

Safety:

lean
theorem PairResAnsSafe_of_odd_upper_median_Bmajor
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    {u v : Fin n}
    (hm : m₀ = majorityAnswer D)
    (hB : nAOf D < nBOf D)
    (hS : InSrank D)
    (hRes : ResAns m₀ D)
    (hodd : ¬ n % 2 = 0)
    (hMis : MisorderedPair D u v)
    (hv_med : rank1 D v = ceilHalf n) :
    PairResAnsSafe
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      m₀ D u v

After swap, median rank state is paired with input u, which is B; decision writes .outB = m₀.

Even case

Let heven : n % 2 = 0, ceilHalf n = n/2.

Split:

lean
nAOf D = nBOf D  -- tie, m₀ = .outT
nAOf D > nBOf D  -- A majority, m₀ = .outA
nAOf D < nBOf D  -- B majority, m₀ = .outB
Even tie

If no nonmedian misorder exists, the only possible inversion touching lower median must be exact boundary:

lean
rank_u+1 = n/2
rank_v+1 = n/2+1

Counting helper:

lean
theorem even_tie_all_touch_lower_exists_boundary_misorder
    {D : Config (AgentState n) Opinion n}
    (hn4 : 4 ≤ n)
    (hS : InSrank D)
    (heven : n % 2 = 0)
    (hTie : nAOf D = nBOf D)
    (hMisExists : ∃ u v, MisorderedPair D u v)
    (hAllTouch :
      ∀ u v, MisorderedPair D u v →
        rank1 D u = n / 2 ∨ rank1 D v = n / 2) :
    ∃ u v,
      MisorderedPair D u v ∧
      rank1 D u = n / 2 ∧
      rank1 D v = n / 2 + 1

Use disjunct 4.

Safety:

lean
theorem PairResAnsSafe_of_even_boundary_tie
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    {u v : Fin n}
    (hm : m₀ = majorityAnswer D)
    (hTie : nAOf D = nBOf D)
    (hS : InSrank D)
    (hRes : ResAns m₀ D)
    (heven : n % 2 = 0)
    (hMis : MisorderedPair D u v)
    (hu_lower : rank1 D u = n / 2)
    (hv_upper : rank1 D v = n / 2 + 1) :
    PairResAnsSafe
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      m₀ D u v

Even decision sees unequal inputs B/A and writes .outT; tie gives m₀=.outT.

Even + A majority

Avoid exact boundary because it writes .outT, unsafe. Counting forces a non-boundary A above lower median:

lean
theorem even_Amajor_all_touch_lower_exists_lower_nonboundary_misorder
    {D : Config (AgentState n) Opinion n}
    (hn4 : 4 ≤ n)
    (hS : InSrank D)
    (heven : n % 2 = 0)
    (hA : nAOf D > nBOf D)
    (hMisExists : ∃ u v, MisorderedPair D u v)
    (hAllTouch :
      ∀ u v, MisorderedPair D u v →
        rank1 D u = n / 2 ∨ rank1 D v = n / 2) :
    ∃ u v,
      MisorderedPair D u v ∧
      rank1 D u = n / 2 ∧
      rank1 D v ≠ n / 2 + 1

Then split rank1 D v = n.

If v ≠ n: disjunct 7, 1≤timer_u.

If v = n: disjunct 8, 2≤timer_u.

Safety:

lean
theorem PairResAnsSafe_of_even_lower_nonboundary_Amajor
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    {u v : Fin n}
    (hm : m₀ = majorityAnswer D)
    (hA : nAOf D > nBOf D)
    (hS : InSrank D)
    (hRes : ResAns m₀ D)
    (heven : n % 2 = 0)
    (hMis : MisorderedPair D u v)
    (hu_lower : rank1 D u = n / 2)
    (hv_not_upper : rank1 D v ≠ n / 2 + 1) :
    PairResAnsSafe
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      m₀ D u v

Here phase4_decide no-ops because not exact lower/upper pair. If propagate sees lower median, its answer remains ResAns; with timer conditions you additionally prove no reset for InSrank preservation.

Even + B majority

Counting gives lower median on v side:

lean
theorem even_Bmajor_all_touch_lower_exists_v_lower_misorder
    {D : Config (AgentState n) Opinion n}
    (hn4 : 4 ≤ n)
    (hS : InSrank D)
    (heven : n % 2 = 0)
    (hB : nAOf D < nBOf D)
    (hMisExists : ∃ u v, MisorderedPair D u v)
    (hAllTouch :
      ∀ u v, MisorderedPair D u v →
        rank1 D u = n / 2 ∨ rank1 D v = n / 2) :
    ∃ u v,
      MisorderedPair D u v ∧
      rank1 D v = n / 2

Use disjunct 6.

Safety:

lean
theorem PairResAnsSafe_of_even_v_lower_Bmajor
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    {u v : Fin n}
    (hm : m₀ = majorityAnswer D)
    (hB : nAOf D < nBOf D)
    (hS : InSrank D)
    (hRes : ResAns m₀ D)
    (heven : n % 2 = 0)
    (hMis : MisorderedPair D u v)
    (hv_lower : rank1 D v = n / 2) :
    PairResAnsSafe
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      m₀ D u v

After swap, lower median rank is paired with B input (u), which matches B majority. In many subcases decision no-ops; if lower/upper triggers, output is either B-major safe or handled by avoiding boundary.

2. exists_answer_safe_misordered_pair proof skeleton
lean
theorem exists_answer_safe_misordered_pair
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hm : m₀ = majorityAnswer D)
    (hS : InSrank D)
    (hRes : ResAns m₀ D)
    (hTimer : ∀ μ, rank1 D μ = ceilHalf n → 2 ≤ (D μ).1.timer)
    (hNotSwap : ¬ InSswap D) :
    ∃ u v : Fin n,
      MisorderedPair D u v ∧
      AnswerSafeMisorderCase D u v ∧
      PairResAnsSafe
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        m₀ D u v := by
  classical

  -- 1. Standard inversion extraction.
  obtain ⟨u₀, v₀, hMis₀⟩ :=
    exists_misordered_of_not_InSswap hS hNotSwap

  -- 2. First try a non-median misorder.
  by_cases hNonMed :
      ∃ u v,
        MisorderedPair D u v ∧
        rank1 D u ≠ ceilHalf n ∧
        rank1 D v ≠ ceilHalf n
  · obtain ⟨u, v, hMis, huN, hvN⟩ := hNonMed
    refine ⟨u, v, hMis, ?_, ?_⟩
    · exact Or.inl ⟨huN, hvN⟩
    · exact
        PairResAnsSafe_of_nonmedian_misorder
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hS hRes hMis huN hvN

  -- 3. Otherwise every misorder touches median/lower-median.
  have hAllTouch :
      ∀ u v,
        MisorderedPair D u v →
        rank1 D u = ceilHalf n ∨ rank1 D v = ceilHalf n := by
    intro u v hMis
    by_contra hbad
    push_neg at hbad
    exact hNonMed ⟨u, v, hMis, hbad.1, hbad.2⟩

  by_cases heven : n % 2 = 0
  · -- Even
    by_cases hTie : nAOf D = nBOf D
    · -- even tie: boundary exact pair.
      obtain ⟨u, v, hMis, huL, hvU⟩ :=
        even_tie_all_touch_lower_exists_boundary_misorder
          hn4 hS heven hTie ⟨u₀, v₀, hMis₀⟩
          (by
            intro u v hMis
            have h := hAllTouch u v hMis
            -- ceilHalf n = n/2 in even case
            simpa [rank1, ceilHalf] using h)
      refine ⟨u, v, hMis, ?_, ?_⟩
      · exact
          Or.inr <| Or.inr <| Or.inr <|
            Or.inl ⟨heven, huL, hvU, hn4⟩
      · exact
          PairResAnsSafe_of_even_boundary_tie
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hm hTie hS hRes heven hMis huL hvU

    · have hNonTie : nAOf D ≠ nBOf D := hTie
      by_cases hA : nAOf D > nBOf D
      · -- A majority: lower median u, non-boundary v.
        obtain ⟨u, v, hMis, huL, hvNotUpper⟩ :=
          even_Amajor_all_touch_lower_exists_lower_nonboundary_misorder
            hn4 hS heven hA ⟨u₀, v₀, hMis₀⟩
            (by
              intro u v hMis
              have h := hAllTouch u v hMis
              simpa [rank1, ceilHalf] using h)
        refine ⟨u, v, hMis, ?_, ?_⟩
        · by_cases hvMax : rank1 D v = n
          · -- disjunct 8
            have htu : 2 ≤ (D u).1.timer := by
              apply hTimer u
              have hceil : ceilHalf n = n / 2 := by
                unfold ceilHalf; omega
              rwa [hceil]
            exact
              Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
                ⟨heven, huL, hvMax, htu, hn4⟩
          · -- disjunct 7
            have htu : 1 ≤ (D u).1.timer := by
              have h2 : 2 ≤ (D u).1.timer := by
                apply hTimer u
                have hceil : ceilHalf n = n / 2 := by
                  unfold ceilHalf; omega
                rwa [hceil]
              omega
            exact
              Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
                ⟨heven, huL, hvNotUpper, hvMax, htu, hn4⟩
        · exact
            PairResAnsSafe_of_even_lower_nonboundary_Amajor
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hm hA hS hRes heven hMis huL hvNotUpper

      · -- B majority: since not tie and not A-major.
        have hB : nAOf D < nBOf D := by omega
        obtain ⟨u, v, hMis, hvL⟩ :=
          even_Bmajor_all_touch_lower_exists_v_lower_misorder
            hn4 hS heven hB ⟨u₀, v₀, hMis₀⟩
            (by
              intro u v hMis
              have h := hAllTouch u v hMis
              simpa [rank1, ceilHalf] using h)
        refine ⟨u, v, hMis, ?_, ?_⟩
        · have htv : 1 ≤ (D v).1.timer := by
            have h2 : 2 ≤ (D v).1.timer := by
              apply hTimer v
              have hceil : ceilHalf n = n / 2 := by
                unfold ceilHalf; omega
              rwa [hceil]
            omega
          exact
            Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
              ⟨heven, hvL, htv, hn4⟩
        · exact
            PairResAnsSafe_of_even_v_lower_Bmajor
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hm hB hS hRes heven hMis hvL

  · -- Odd
    have hodd : ¬ n % 2 = 0 := heven
    by_cases hA : nAOf D > nBOf D
    · obtain ⟨u, v, hMis, huMed⟩ :=
        odd_Amajor_all_touch_median_exists_lower_median_misorder
          hS hodd hA ⟨u₀, v₀, hMis₀⟩ hAllTouch
      refine ⟨u, v, hMis, ?_, ?_⟩
      · by_cases hvMax : rank1 D v = n
        · have htu : 2 ≤ (D u).1.timer := hTimer u huMed
          exact Or.inr <| Or.inr <| Or.inl
            ⟨hodd, huMed, hvMax, htu⟩
        · have htu : 1 ≤ (D u).1.timer := by
            have h2 := hTimer u huMed
            omega
          exact Or.inr <| Or.inl
            ⟨hodd, huMed, hvMax, htu⟩
      · exact
          PairResAnsSafe_of_odd_lower_median_Amajor
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hm hA hS hRes hodd hMis huMed

    · have hB : nAOf D < nBOf D := by
        -- odd excludes equality via total nA+nB=n and parity
        have hsum := nAOf_add_nBOf D
        omega
      obtain ⟨u, v, hMis, hvMed⟩ :=
        odd_Bmajor_all_touch_median_exists_upper_median_misorder
          hS hodd hB ⟨u₀, v₀, hMis₀⟩ hAllTouch
      refine ⟨u, v, hMis, ?_, ?_⟩
      · have htv : 1 ≤ (D v).1.timer := by
          have h2 := hTimer v hvMed
          omega
        exact
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
            ⟨hodd, hvMed, htv⟩
      · exact
          PairResAnsSafe_of_odd_upper_median_Bmajor
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hm hB hS hRes hodd hMis hvMed

This is the proof tree. The “hard” parts are the counting lemmas in odd/even cases; they are pure finite-order arithmetic over ranks and inputs, independent of transition semantics.

3. PairResAnsSafe 的机械证明链

所有 concrete PairResAnsSafe_of_* lemmas share the same skeleton.

General transition normal form under InSrank misordered pair

First prove a reusable normal form:

lean
theorem transitionPEM_InSrank_misordered_eq_phase4
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hS : InSrank D)
    (hMis : MisorderedPair D u v) :
    transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (D u, D v)
    =
    transitionPEM_phase4 n Rmax
      ((D u).1, (D v).1) (D u).2 (D v).2

Actually after unfolding transitionPEM, this says prePhase4 is identity and phase4 receives original states.

Proof:

hu_settled := hS.allSettled u, hv_settled := hS.allSettled v.

u ≠ v from hMis.1.

rank_ne : (D u).1.rank ≠ (D v).1.rank by injectivity.

rankDeltaOSSR_satisfies_fix or rankDeltaOSSR_settled_distinct_ranks.

prePhase4:

no Resetting entry wipe because s.role = Settled.

no timer init because s₀.role = Settled already.

no Resetting pair phi-spread.

transition enters phase4.

Misordered swap fires
lean
theorem phase4_swap_of_misordered
    {D : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hMis : MisorderedPair D u v) :
    phase4_swap (D u).1 (D v).1 (D u).2 (D v).2 =
      ((D v).1, (D u).1)

Proof: unfold phase4_swap; hMis is exactly condition.

Decision safety lemmas

Use concrete lemmas by case.

Nonmedian case
lean
theorem phase4_decide_noop_of_nonmedian_misordered
    {D : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hMis : MisorderedPair D u v)
    (hu_ne_med : rank1 D u ≠ ceilHalf n)
    (hv_ne_med : rank1 D v ≠ ceilHalf n) :
    phase4_decide n (D v).1 (D u).1 (D u).2 (D v).2 =
      ((D v).1, (D u).1)

For even, derive no lower/upper pair from hu_ne_med, hv_ne_med, ceilHalf = n/2. For odd, no rank equals median.

Then:

lean
theorem PairResAnsSafe_of_nonmedian_misorder ... := by
  rw [transitionPEM_InSrank_misordered_eq_phase4 hS hMis]
  unfold transitionPEM_phase4
  simp [hS.allSettled u, hS.allSettled v]
  rw [phase4_swap_of_misordered hMis]
  rw [phase4_decide_noop_of_nonmedian_misordered hMis hu_ne_med hv_ne_med]
  -- phase4_propagate no-op since neither rank median
  unfold phase4_propagate
  simp [hu_ne_med, hv_ne_med]
  exact ⟨hRes v, hRes u⟩
Odd lower median A-major

After swap, output pair is (state_v, state_u) but decision assigns median state state_u using input v=A.

lean
theorem phase4_decide_odd_lower_median_misorder_writes_outA
    {D : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hodd : ¬ n % 2 = 0)
    (hMis : MisorderedPair D u v)
    (hu_med : rank1 D u = ceilHalf n) :
    let p := phase4_decide n (D v).1 (D u).1 (D u).2 (D v).2
    p.2.answer = .outA

Because (D v).2 = A.

Then m₀=.outA from hm + hA.

Need also show p.1.answer remains ResAns: it is either old (D v).1.answer, or if v also median impossible by rank inequality. So hRes v.

Propagate after decision:

If no reset, output answers ResAns.

If reset, copied answer is from median side, which is ResAns/m₀.
For no-reset preserving InSrank, use timer cases separately.

Generic propagate answer lemma:

lean
theorem phase4_propagate_preserves_PairResAns
    {Rmax : ℕ}
    {b₀ b₁ : AgentState n} {m₀ : Answer}
    (h₀ : AnswerInResAns m₀ b₀.answer)
    (h₁ : AnswerInResAns m₀ b₁.answer) :
    let out := phase4_propagate n Rmax b₀ b₁
    AnswerInResAns m₀ out.1.answer ∧
    AnswerInResAns m₀ out.2.answer

Proof by unfolding phase4_propagate; reset branch copies one of b₀.answer/b₁.answer, both already ResAns.

This lemma is extremely useful: it means all PairResAnsSafe lemmas only need to show phase4_decide output answers are ResAns.

Odd upper median B-major

Symmetric: median state v after swap is first component, paired with input u=B, decision writes .outB=m₀.

Even boundary tie

After swap, exact lower/upper order is reversed component-wise, but phase4_decide has two branches. Inputs are B/A and unequal, so it writes .outT to both. Tie gives m₀=.outT.

lean
theorem phase4_decide_even_boundary_tie_writes_outT
    {D : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (heven : n % 2 = 0)
    (hMis : MisorderedPair D u v)
    (hu_lower : rank1 D u = n / 2)
    (hv_upper : rank1 D v = n / 2 + 1) :
    let p := phase4_decide n (D v).1 (D u).1 (D u).2 (D v).2
    p.1.answer = .outT ∧ p.2.answer = .outT
Even nonboundary cases

If exact lower/upper not present, phase4_decide no-ops. Then ResAns follows from original answers.

For lower median but v≠upper:

lean
theorem phase4_decide_even_lower_nonboundary_noop
    (heven : n % 2 = 0)
    (hMis : MisorderedPair D u v)
    (hu_lower : rank1 D u = n / 2)
    (hv_not_upper : rank1 D v ≠ n / 2 + 1) :
    phase4_decide n (D v).1 (D u).1 (D u).2 (D v).2 =
      ((D v).1, (D u).1)

For v lower median B-major case, also no exact lower/upper pair after swap unless u is upper, impossible since rank_u<rank_v=lower.

4. Counting / geometry lemmas: exact proof ideas

These are pure rank/input lemmas. Prove them by converting agents to their rank values.

Useful helper from InSrank:

lean
theorem InSrank.exists_agent_at_rank
    (hS : InSrank D) (ρ : Fin n) :
    ∃ w, (D w).1.rank = ρ

If not already available, it follows from injective map Fin n → Fin n, finite same cardinal ⇒ surjective.

Then define:

lean
def inputAtRank (D) (hS : InSrank D) (ρ : Fin n) : Opinion :=
  (D (Classical.choose (hS.exists_agent_at_rank ρ))).2

But in Lean, avoid defining this globally; use obtain ⟨wρ, hwρ⟩.

Counting lemma pattern:

nAOf D = number of A agents.

If A majority odd, then at least ceilHalf n A agents.

If every misorder touches median and no lower-median-Amajor candidate exists, then all A above/below force sortedness, contradiction.

For example odd A-major:

lean
theorem odd_Amajor_all_touch_median_exists_lower_median_misorder ... := by
  -- Let medRank := ⟨ceilHalf n - 1, ...⟩
  -- Get med agent μ.
  obtain ⟨μ, hμrank⟩ := hS.exists_at_rank ...
  by_cases hμB : (D μ).2 = Opinion.B
  · -- Since A-major, there exists A above median.
    obtain ⟨v, hvA, hv_rank_gt_med⟩ := exists_A_above_median_of_Amajor_and_median_B ...
    exact ⟨μ, v, misordered, μ_med⟩
  · -- median is A. Any misorder touching median must be v=median.
    -- Since hMisExists, obtain u v hMis. hAllTouch forces v=median.
    -- If all misorders are of this unsafe orientation, A-major gives another A above
    -- or a nonmedian inversion; contradiction to no-nonmedian.

The actual Lean-friendly path may be to prove contrapositive:

lean
if A-major and no nonmedian misorder and no lower-median misorder,
then InSswap

Then contradiction with hNotSwap.

Similarly for even A-major/B-major.

5. How PairResAnsSafe follows mechanically

For each selected pair:

rankDelta identity

lean
have huS := hS.allSettled u
have hvS := hS.allSettled v
have huv : u ≠ v := ...
have hrank_ne : (D u).1.rank ≠ (D v).1.rank := ...
have hRD :=
  rankDeltaOSSR_settled_distinct_ranks huS hvS hrank_ne

prePhase4 identity on answers
Since both old roles are Settled, no new Resetting wipe; no phi-spread.

swap fires
MisorderedPair exactly matches phase4_swap condition.

decide output ResAns
Case-specific:

no decision: old answers, use hRes.

odd lower A-major: writes .outA=m₀.

odd upper B-major: writes .outB=m₀.

even tie boundary: writes .outT=m₀.

even nonboundary: no decision.

propagate preserves ResAns
Use this new generic lemma:

lean
theorem phase4_propagate_preserves_PairResAns
    {Rmax : ℕ}
    {b₀ b₁ : AgentState n} {m₀ : Answer}
    (h₀ : b₀.answer = m₀ ∨ b₀.answer = .phi)
    (h₁ : b₁.answer = m₀ ∨ b₁.answer = .phi) :
    let out := phase4_propagate n Rmax b₀ b₁
    (out.1.answer = m₀ ∨ out.1.answer = .phi) ∧
    (out.2.answer = m₀ ∨ out.2.answer = .phi)

This is simpler and stronger than relying on phase4_propagate_no_reset_of_eq_answer. It handles reset branches too, because reset only copies one of the two already-safe answers.

If downstream needs InSrank preservation, add a separate no-reset lemma using your 8-way timer disjunction:

lean
theorem phase4_propagate_no_reset_of_safe_case
    {Rmax : ℕ}
    {D : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hCase : AnswerSafeMisorderCase D u v)
    ... :
    let out := transitionPEM ...
    out.1.role = .Settled ∧ out.2.role = .Settled

This separation is important:
PairResAnsSafe is answer-only and easy;
AnswerSafeMisorderCase + timer is for no reset / InSrank preservation / misorderedCount decrease.

6. 最终建议的 proof dependency order

Implement in this order:

Definitions:

rank1

MisorderedPair

AnswerInResAns

PairResAnsSafe

AnswerSafeMisorderCase

Mechanical transition lemmas:

transitionPEM_InSrank_misordered_eq_phase4

phase4_swap_of_misordered

phase4_propagate_preserves_PairResAns

Concrete PairResAnsSafe lemmas:

PairResAnsSafe_of_nonmedian_misorder

PairResAnsSafe_of_odd_lower_median_Amajor

PairResAnsSafe_of_odd_upper_median_Bmajor

PairResAnsSafe_of_even_boundary_tie

PairResAnsSafe_of_even_lower_nonboundary_Amajor

PairResAnsSafe_of_even_v_lower_Bmajor

Pure combinatorial existence lemmas:

exists_misordered_of_not_InSswap

exists_nonmedian_misorder_or_all_misorders_touch_median

odd A/B majority forced orientation lemmas

even tie/A/B forced orientation lemmas

Final:

exists_answer_safe_misordered_pair

That final proof is then mostly case-splitting and exact PairResAnsSafe_of_* ....
