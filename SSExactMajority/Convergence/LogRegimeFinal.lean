import SSExactMajority.Convergence.LogRegimeConvergence
import SSExactMajority.Convergence.BurmanConvergenceFinal

namespace SSEM

/-- Strong form of `CorrectResetSeed` for the log-regime re-entry:
the seed still has the exact reset fuel `Rmax`, and the existing answer
invariant is the one required by
`log_seed_uniform_leader_to_FreshRankingStart_resAns_noPhi_log`. -/
def CorrectResetSeedStrong
    (Rmax : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  (∃ r : Fin n,
    (C r).1.role = .Resetting ∧
    (C r).1.resetcount = Rmax ∧
    (C r).1.leader = .L ∧
    (C r).1.answer = majorityAnswer C) ∧
  (∀ w : Fin n,
    (C w).1.role = .Resetting →
    0 < (C w).1.resetcount ∧
    (C w).1.answer = majorityAnswer C)

theorem CorrectResetSeedStrong.toCorrectResetSeed
    {Rmax : ℕ} {C : Config (AgentState n) Opinion n}
    (hN_lt_Rmax : nonResettingCount C < Rmax)
    (hSeed : CorrectResetSeedStrong Rmax C) :
    CorrectResetSeed C := by
  rcases hSeed with ⟨⟨r, hr_role, hr_rc, hr_L, hr_ans⟩, hAllAns⟩
  refine ⟨⟨r, hr_role, ?_, hr_L, hr_ans⟩, ?_⟩
  · simpa [hr_rc] using hN_lt_Rmax
  · intro w hw
    exact hAllAns w hw

theorem CorrectResetSeedStrong_of_step_pair
    {Y : Type*} {P : Protocol (AgentState n) Opinion Y}
    {Rmax : ℕ} {C : Config (AgentState n) Opinion n} {u v : Fin n}
    (hRmax_pos : 0 < Rmax)
    (hC : InSrank C) (huv : u ≠ v)
    (hu_role : (C.step P u v u).1.role = .Resetting)
    (hu_rc : (C.step P u v u).1.resetcount = Rmax)
    (hu_L : (C.step P u v u).1.leader = .L)
    (hu_ans : (C.step P u v u).1.answer = majorityAnswer (C.step P u v))
    (_hv_role : (C.step P u v v).1.role = .Resetting)
    (hv_rc : (C.step P u v v).1.resetcount = Rmax)
    (hv_ans : (C.step P u v v).1.answer = majorityAnswer (C.step P u v)) :
    CorrectResetSeedStrong Rmax (C.step P u v) := by
  refine ⟨⟨u, hu_role, hu_rc, hu_L, hu_ans⟩, ?_⟩
  intro w hw
  by_cases hwu : w = u
  · subst w
    refine ⟨?_, hu_ans⟩
    rw [hu_rc]
    exact hRmax_pos
  · by_cases hwv : w = v
    · subst w
      refine ⟨?_, hv_ans⟩
      rw [hv_rc]
      exact hRmax_pos
    · have hw_old : C.step P u v w = C w := by
        unfold Config.step
        simp [huv, hwu, hwv]
      rw [hw_old] at hw
      rw [hC.allSettled w] at hw
      cases hw

theorem fresh_unique_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax) (hDmax_pos : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hFresh : ∀ w : Fin n, FreshResettingAt Dmax C w)
    (hUnique : ∃! ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting := by
    intro w
    exact (hFresh w).1
  have hAllRc0 : ∀ w : Fin n, (C w).1.resetcount = 0 := by
    intro w
    exact (hFresh w).2.1
  obtain ⟨Ldorm, hDormant⟩ :=
    all_resetting_zero_unique_to_dormant
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C hAllReset hAllRc0 hUnique
  let C₁ : Config (AgentState n) Opinion n := runPairs P C Ldorm
  obtain ⟨Lrank, hRank⟩ :=
    dormant_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax_pos hDmax_pos C₁
      (by simpa [C₁, P] using hDormant)
  refine ⟨Ldorm ++ Lrank, ?_⟩
  rw [runPairs_append]
  change RankingEndpoint (runPairs P C₁ Lrank)
  exact hRank

theorem reset_snapshot_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hReset :
      ∃ r : Fin n, (C r).1.role = .Resetting ∧
        Rmax ≤ (C r).1.resetcount ∧ (C r).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hn2 : 2 ≤ n := by omega
  have hRmax_pos : 0 < Rmax := by omega
  have hDmax_pos : 0 < Dmax := by omega
  rcases hReset with ⟨r, hr_role, hr_rc, hr_L⟩
  obtain ⟨Lfresh, hFresh, hUnique⟩ :=
    all_fresh_unique_from_log_seed_no_answer
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax1 hn2 C r hr_role
      (Nat.le_trans hRlog hr_rc) hr_L
  let C₁ : Config (AgentState n) Opinion n := runPairs P C Lfresh
  obtain ⟨Lrank, hRank⟩ :=
    fresh_unique_to_RankingEndpoint_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax_pos hDmax_pos C₁
      (by simpa [C₁, P] using hFresh)
      (by simpa [C₁, P] using hUnique)
  refine ⟨Lfresh ++ Lrank, ?_⟩
  rw [runPairs_append]
  change RankingEndpoint (runPairs P C₁ Lrank)
  exact hRank

theorem step_reset_snapshot_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n} {u v : Fin n}
    (hStep :
      let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      let C' := C.step P u v
      (C' u).1.role = .Resetting ∧ (C' u).1.resetcount = Rmax ∧
        (C' u).1.leader = .L ∧
      (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
        (C' v).1.leader = .L ∧
      ∀ y : Fin n, (C' y).1.role = .Resetting →
        (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C ((u, v) :: L)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  change
    (C₁ u).1.role = .Resetting ∧ (C₁ u).1.resetcount = Rmax ∧
      (C₁ u).1.leader = .L ∧
    (C₁ v).1.role = .Resetting ∧ (C₁ v).1.resetcount = Rmax ∧
      (C₁ v).1.leader = .L ∧
    ∀ y : Fin n, (C₁ y).1.role = .Resetting →
      (C₁ y).1.resetcount = Rmax ∧ (C₁ y).1.leader = .L at hStep
  rcases hStep with ⟨hu_role, hu_rc, hu_L, _hv_role, _hv_rc, _hv_L, _hSnapshot⟩
  have hReset :
      ∃ r : Fin n, (C₁ r).1.role = .Resetting ∧
        Rmax ≤ (C₁ r).1.resetcount ∧ (C₁ r).1.leader = .L := by
    refine ⟨u, hu_role, ?_, hu_L⟩
    rw [hu_rc]
  obtain ⟨L, hEndpoint⟩ :=
    reset_snapshot_to_RankingEndpoint_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog C₁ hReset
  refine ⟨L, ?_⟩
  rw [runPairs_cons]
  change RankingEndpoint (runPairs P C₁ L)
  exact hEndpoint

theorem ranking_goal_of_step_reset_snapshot_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n} {u v : Fin n}
    (hStep :
      let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      let C' := C.step P u v
      (C' u).1.role = .Resetting ∧ (C' u).1.resetcount = Rmax ∧
        (C' u).1.leader = .L ∧
      (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
        (C' v).1.leader = .L ∧
      ∀ y : Fin n, (C' y).1.role = .Resetting →
        (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog (C := C) (u := u) (v := v) hStep
  exact
    ranking_goal_of_runPairs_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := (u, v) :: L) hEndpoint

theorem InSrank_misorder_step_to_RankingEndpoint_or_InSrank_decrease_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v)) :
    (∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
          C ((u, v) :: L))) ∨
    (InSrank
        (C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) ∧
      misorderedCount
        (C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) <
      misorderedCount C) := by
  by_cases hrole :
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (C u, C v)).1.role = .Settled ∧
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (C u, C v)).2.role = .Settled
  · exact Or.inr
      (swap_step_decreases_at_misorder_of_role_settled
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        rankDeltaOSSR_satisfies_fix hC hMis hrole)
  · have hstep :=
      InSrank_misorder_step_reset_snapshot_of_not_both_settled
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hC hMis hrole
    obtain ⟨L, hEndpoint⟩ :=
      step_reset_snapshot_to_RankingEndpoint_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog (C := C) (u := u) (v := v) hstep
    exact Or.inl ⟨L, hEndpoint⟩

theorem InSrank_reaches_RankingEndpoint_or_InSswap_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C) :
    (∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L)) ∨
    (∃ L : List (Fin n × Fin n),
      InSswap
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let motive : ℕ → Prop := fun k =>
    ∀ C : Config (AgentState n) Opinion n,
      InSrank C →
      misorderedCount C = k →
      (∃ L : List (Fin n × Fin n), RankingEndpoint (runPairs P C L)) ∨
      (∃ L : List (Fin n × Fin n), InSswap (runPairs P C L))
  have hmain : ∀ k, motive k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro C hC hcount
      by_cases hk0 : k = 0
      · have hzero : misorderedCount C = 0 := by
          rw [hcount, hk0]
        exact Or.inr ⟨[], by
          simpa [P] using
            (InSswap_of_InSrank_of_count_zero hC hzero)⟩
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hpos : 0 < misorderedCount C := by
          rw [hcount]
          exact hkpos
        obtain ⟨u, v, hMis⟩ := exists_misordered_of_pos_count hpos
        have hstep :=
          InSrank_misorder_step_to_RankingEndpoint_or_InSrank_decrease_log
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hDmax1 hRlog hC hMis
        rcases hstep with hEndpoint | hDec
        · rcases hEndpoint with ⟨L, hEndpoint⟩
          exact Or.inl ⟨(u, v) :: L, by
            simpa [P] using hEndpoint⟩
        · rcases hDec with ⟨hCstep, hlt⟩
          let Cstep : Config (AgentState n) Opinion n := C.step P u v
          have hlt_k : misorderedCount Cstep < k := by
            dsimp [Cstep, P]
            rw [← hcount]
            exact hlt
          have hrec := ih (misorderedCount Cstep) hlt_k Cstep hCstep rfl
          rcases hrec with hEndpoint | hSwap
          · rcases hEndpoint with ⟨L, hEndpoint⟩
            exact Or.inl ⟨(u, v) :: L, by
              change RankingEndpoint (runPairs P (C.step P u v) L)
              exact hEndpoint⟩
          · rcases hSwap with ⟨L, hSwap⟩
            exact Or.inr ⟨(u, v) :: L, by
              change InSswap (runPairs P (C.step P u v) L)
              exact hSwap⟩
  have h := hmain (misorderedCount C) C hC rfl
  simpa [P] using h

theorem InSrank_timer_zero_no_swap_diff_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧
      (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have hstep :=
    trigger_reset_from_InSrank_timer_zero_no_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC hμv hμ_med hv_no_med h_timer h_no_swap hpar h_post_diff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog (C := C) (u := μ) (v := v) hstep
  exact ⟨(μ, v) :: L, hEndpoint⟩

theorem InSswap_even_lower_timer_zero_wrong_nonupper_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hSwap : InSswap C)
    (hpar : n % 2 = 0)
    {μ w : Fin n} (hμw : μ ≠ w)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hw_not_upper : (C w).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 0)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hw_wrong : (C w).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have hw_not_lower : (C w).1.rank.val + 1 ≠ n / 2 := by
    intro hw_lower
    apply hμw
    apply hSwap.ranks_inj
    apply Fin.eq_of_val_eq
    have hμ_val : (C μ).1.rank.val = n / 2 - 1 := by omega
    have hw_val : (C w).1.rank.val = n / 2 - 1 := by omega
    exact hμ_val.trans hw_val.symm
  have h_no_swap :
      ¬((C μ).1.rank < (C w).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C w).2 = Opinion.A) :=
    hSwap.swap_condition_false μ w
  have hdiff : (C μ).1.answer ≠ (C w).1.answer := by
    intro hsame
    exact hw_wrong (by rw [← hsame, hμ_correct])
  have hstep :=
    trigger_reset_from_InSrank_even_lower_timer_zero_no_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap.toInSrank hμw hpar hμ_lower hw_not_lower hw_not_upper h_timer
      h_no_swap hdiff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog (C := C) (u := μ) (v := w) hstep
  exact ⟨(μ, w) :: L, hEndpoint⟩

theorem InSswap_even_lower_timer_one_same_then_zero_wrong_nonupper_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hSwap : InSswap C)
    (hpar : n % 2 = 0)
    {μ v w : Fin n} (hμv : μ ≠ v) (hμw : μ ≠ w) (hwv : w ≠ v)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hw_not_upper : (C w).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 1)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hv_correct : (C v).1.answer = majorityAnswer C)
    (hw_wrong : (C w).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P μ v
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hSwap.swap_condition_false μ v
  have h_same : (C μ).1.answer = (C v).1.answer := by
    rw [hμ_correct, hv_correct]
  obtain ⟨hμ_state, hv_state, hothers⟩ :=
    no_reset_even_lower_max_timer_one_step_state
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_same
  have hC₁_swap_pack :=
    no_reset_even_lower_max_timer_one_step_InSswap
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_same
  have hC₁_swap : InSswap C₁ := by
    simpa [C₁, P] using hC₁_swap_pack.1
  have hμ_timer₁ : (C₁ μ).1.timer = 0 := by
    simpa [C₁, P] using hC₁_swap_pack.2.1
  have hμ_lower₁ : (C₁ μ).1.rank.val + 1 = n / 2 := by
    simpa [C₁, P] using hC₁_swap_pack.2.2.2
  have hw_state₁ : C₁ w = C w := by
    simpa [C₁, P] using hothers w hμw.symm hwv
  have hmaj₁ : majorityAnswer C₁ = majorityAnswer C := by
    simpa [C₁, P] using
      (majorityAnswer_step_eq
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  have hμ_correct₁ : (C₁ μ).1.answer = majorityAnswer C₁ := by
    rw [hmaj₁]
    simpa [C₁, P] using hC₁_swap_pack.2.2.1.trans hμ_correct
  have hw_not_upper₁ : (C₁ w).1.rank.val + 1 ≠ n / 2 + 1 := by
    rw [hw_state₁]
    exact hw_not_upper
  have hw_wrong₁ : (C₁ w).1.answer ≠ majorityAnswer C₁ := by
    rw [hw_state₁, hmaj₁]
    exact hw_wrong
  obtain ⟨Ltail, hEndpoint⟩ :=
    InSswap_even_lower_timer_zero_wrong_nonupper_to_RankingEndpoint_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog hC₁_swap hpar hμw hμ_lower₁ hw_not_upper₁
      hμ_timer₁ hμ_correct₁ hw_wrong₁
  refine ⟨(μ, v) :: Ltail, ?_⟩
  change RankingEndpoint (runPairs P (C.step P μ v) Ltail)
  exact hEndpoint

theorem InSswap_even_lower_timer_one_max_wrong_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hSwap : InSswap C)
    (hpar : n % 2 = 0)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hv_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hSwap.swap_condition_false μ v
  have hdiff : (C μ).1.answer ≠ (C v).1.answer := by
    intro hsame
    exact hv_wrong (by rw [← hsame, hμ_correct])
  have hstep :=
    trigger_reset_from_InSrank_even_lower_timer_one_max_no_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap hdiff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog (C := C) (u := μ) (v := v) hstep
  exact ⟨(μ, v) :: L, hEndpoint⟩

theorem InSswap_bad_even_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    (hpar : n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let motive : ℕ → Prop := fun k =>
    ∀ C : Config (AgentState n) Opinion n,
      BadRankingStart C →
      InSswap C →
      wrongAnswerCount C = k →
      ∃ L : List (Fin n × Fin n), RankingEndpoint (runPairs P C L)
  have hmain : ∀ k, motive k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro C hbad hSwap hcount
      by_cases hk0 : k = 0
      · have hzero : wrongAnswerCount C = 0 := by
          rw [hcount, hk0]
        have hConsensus :=
          isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero hSwap hzero
        exact ⟨[], by
          simp only [runPairs_nil]
          exact ⟨hSwap.toInSrank, Or.inr hConsensus⟩⟩
      · obtain ⟨μ, hμ_med, htimer⟩ := hbad.exists_median_timer_zero_or_one
        have hceil : ceilHalf n = n / 2 := by
          unfold ceilHalf
          omega
        have hμ_lower : (C μ).1.rank.val + 1 = n / 2 := by
          rwa [hceil] at hμ_med
        have h_upper_lt : n / 2 < n := by omega
        obtain ⟨ν, hν_rank⟩ :=
          hSwap.toInSrank.exists_at_rank (by omega) (⟨n / 2, h_upper_lt⟩ : Fin n)
        have hν_upper : (C ν).1.rank.val + 1 = n / 2 + 1 := by
          rw [hν_rank]
        have hμν : μ ≠ ν := by
          intro h
          subst ν
          omega
        have hdecision
            (hwrong_pair :
              (C μ).1.answer ≠ majorityAnswer C ∨
                (C ν).1.answer ≠ majorityAnswer C) :
            ∃ L : List (Fin n × Fin n), RankingEndpoint (runPairs P C L) := by
          let C₁ : Config (AgentState n) Opinion n := C.step P μ ν
          have hdec :=
            InSswap_even_median_pair_decision_decreases
              (trank := Rmax) (Rmax := Rmax)
              (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
              rankDeltaOSSR_satisfies_fix hSwap hμν hpar hμ_lower hν_upper hn4
              hwrong_pair
          have hC₁_swap : InSswap C₁ := by
            simpa [C₁, P] using hdec.1
          have hlt : wrongAnswerCount C₁ < k := by
            rw [← hcount]
            simpa [C₁, P] using hdec.2
          by_cases hDone : RankingEndpoint C₁
          · exact ⟨[(μ, ν)], by
              simp only [runPairs_cons, runPairs_nil]
              change RankingEndpoint C₁
              exact hDone⟩
          · have hbad₁ : BadRankingStart C₁ := ⟨hC₁_swap.toInSrank, hDone⟩
            obtain ⟨Ltail, htail⟩ := ih (wrongAnswerCount C₁) hlt C₁ hbad₁ hC₁_swap rfl
            exact ⟨(μ, ν) :: Ltail, by
              change RankingEndpoint (runPairs P (C.step P μ ν) Ltail)
              exact htail⟩
        by_cases hμ_wrong : (C μ).1.answer ≠ majorityAnswer C
        · exact hdecision (Or.inl hμ_wrong)
        · have hμ_correct : (C μ).1.answer = majorityAnswer C := not_not.mp hμ_wrong
          obtain ⟨w, hw_wrong⟩ := hbad.exists_wrong_answer_of_InSswap hSwap
          rcases htimer with htimer0 | htimer1
          · by_cases hw_upper : (C w).1.rank.val + 1 = n / 2 + 1
            · have hw_eq_ν : w = ν := by
                apply hSwap.ranks_inj
                apply Fin.eq_of_val_eq
                have hw_val : (C w).1.rank.val = n / 2 := by omega
                have hν_val : (C ν).1.rank.val = n / 2 := by omega
                exact hw_val.trans hν_val.symm
              subst w
              exact hdecision (Or.inr hw_wrong)
            · have hμw : μ ≠ w := by
                intro h
                subst w
                exact hw_wrong hμ_correct
              exact
                InSswap_even_lower_timer_zero_wrong_nonupper_to_RankingEndpoint_log
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hn4 hDmax1 hRlog hSwap hpar hμw hμ_lower hw_upper htimer0
                  hμ_correct hw_wrong
          · obtain ⟨ρ, hμρ, hρ_max⟩ :=
              hSwap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
            by_cases hρ_wrong : (C ρ).1.answer ≠ majorityAnswer C
            · exact
                InSswap_even_lower_timer_one_max_wrong_to_RankingEndpoint_log
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hn4 hDmax1 hRlog hSwap hpar hμρ hμ_lower hρ_max htimer1
                  hμ_correct hρ_wrong
            · have hρ_correct : (C ρ).1.answer = majorityAnswer C := not_not.mp hρ_wrong
              by_cases hw_upper : (C w).1.rank.val + 1 = n / 2 + 1
              · have hw_eq_ν : w = ν := by
                  apply hSwap.ranks_inj
                  apply Fin.eq_of_val_eq
                  have hw_val : (C w).1.rank.val = n / 2 := by omega
                  have hν_val : (C ν).1.rank.val = n / 2 := by omega
                  exact hw_val.trans hν_val.symm
                subst w
                exact hdecision (Or.inr hw_wrong)
              · have hμw : μ ≠ w := by
                  intro h
                  subst w
                  exact hw_wrong hμ_correct
                have hwρ : w ≠ ρ := by
                  intro h
                  subst w
                  exact hw_wrong hρ_correct
                exact
                  InSswap_even_lower_timer_one_same_then_zero_wrong_nonupper_to_RankingEndpoint_log
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    hn4 hDmax1 hRlog hSwap hpar hμρ hμw hwρ hμ_lower hρ_max
                    hw_upper htimer1 hμ_correct hρ_correct hw_wrong
  simpa [P, motive] using hmain (wrongAnswerCount C) C hbad hSwap rfl

theorem BadRankingStart_even_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C)
    (hpar : n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain hReach :=
    InSrank_reaches_RankingEndpoint_or_InSswap_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog hbad.1
  rcases hReach with hEndpoint | hSwapReach
  · exact hEndpoint
  · obtain ⟨L₁, hSwap₁⟩ := hSwapReach
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    by_cases hDone : RankingEndpoint C₁
    · exact ⟨L₁, by simpa [C₁, P] using hDone⟩
    · have hbad₁ : BadRankingStart C₁ := by
        exact ⟨by simpa [C₁, P] using hSwap₁.toInSrank, hDone⟩
      have hSwapC₁ : InSswap C₁ := by
        simpa [C₁, P] using hSwap₁
      obtain ⟨L₂, hEndpoint₂⟩ :=
        InSswap_bad_even_to_RankingEndpoint_log
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog hbad₁ hSwapC₁ hpar
      refine ⟨L₁ ++ L₂, ?_⟩
      rw [runPairs_append]
      change RankingEndpoint (runPairs P C₁ L₂)
      exact hEndpoint₂

theorem InSswap_bad_timer_zero_wrong_nonmedian_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    {μ w : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hw_no_med : (C w).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (hpar : ¬ n % 2 = 0)
    (hw_wrong : (C w).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have hμw : μ ≠ w := by
    intro h
    subst w
    exact hw_no_med hμ_med
  have h_no_swap :
      ¬((C μ).1.rank < (C w).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C w).2 = Opinion.A) :=
    hSwap.swap_condition_false μ w
  have h_post_diff : opinionToAnswer (C μ).2 ≠ (C w).1.answer := by
    rw [opinionToAnswer_median_eq_majorityAnswer_odd hSwap hμ_med hpar]
    exact hw_wrong.symm
  exact
    InSrank_timer_zero_no_swap_diff_to_RankingEndpoint_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog hbad.1 hμw hμ_med hw_no_med h_timer
      h_no_swap hpar h_post_diff

theorem InSswap_bad_timer_zero_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    {μ : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (hpar : ¬ n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  by_cases hOnly : ∀ w : Fin n, w ≠ μ → (C w).1.answer = majorityAnswer C
  · exact
      InSswap_bad_timer_zero_only_median_wrong_to_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hSwap hμ_med h_timer hpar hOnly
  · push_neg at hOnly
    obtain ⟨w, hwm, hw_wrong⟩ := hOnly
    have hw_no_med : (C w).1.rank.val + 1 ≠ ceilHalf n := by
      intro hw_med
      apply hwm
      apply hSwap.ranks_inj
      apply Fin.eq_of_val_eq
      have hμ_val : (C μ).1.rank.val = ceilHalf n - 1 := by omega
      have hw_val : (C w).1.rank.val = ceilHalf n - 1 := by omega
      exact hw_val.trans hμ_val.symm
    exact
      InSswap_bad_timer_zero_wrong_nonmedian_to_RankingEndpoint_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog hbad hSwap hμ_med hw_no_med h_timer hpar hw_wrong

theorem InSrank_timer_one_max_no_swap_diff_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧
      (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have hstep :=
    trigger_reset_from_InSrank_timer_one_max_no_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC hn4 hμv hμ_med hv_max h_timer h_no_swap hpar h_post_diff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog (C := C) (u := μ) (v := v) hstep
  exact ⟨(μ, v) :: L, hEndpoint⟩

theorem InSrank_timer_one_max_no_swap_same_then_zero_no_swap_diff_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v w : Fin n} (hμv : μ ≠ v) (hμw : μ ≠ w) (hwv : w ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hw_no_med : (C w).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap_max : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_no_swap_w : ¬((C μ).1.rank < (C w).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C w).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_same_max : opinionToAnswer (C μ).2 = (C v).1.answer)
    (h_post_diff_w : opinionToAnswer (C μ).2 ≠ (C w).1.answer) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P μ v
  have hstep :=
    no_reset_no_swap_max_timer_one_step_InSrank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC hn4 hμv hμ_med hv_max h_timer h_no_swap_max hpar h_post_same_max
  have hC₁ : InSrank C₁ := hstep.1
  have hμ_timer₁ : (C₁ μ).1.timer = 0 := hstep.2.1
  have hμ_med₁ : (C₁ μ).1.rank.val + 1 = ceilHalf n := hstep.2.2.2
  have hw_state₁ : C₁ w = C w := by
    dsimp [C₁, P]
    simp [Config.step, hμv, hμw.symm, hwv]
  have hμ_input₁ : (C₁ μ).2 = (C μ).2 := by
    dsimp [C₁, P]
    simp [Config.step, hμv]
  have hμ_rank₁ : (C₁ μ).1.rank = (C μ).1.rank := by
    have htrace :=
      no_reset_no_swap_max_timer_one_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        (hRank := rankDeltaOSSR_satisfies_fix)
        (C := C) hC hn4 hμv hμ_med hv_max h_timer h_no_swap_max hpar h_post_same_max
    have hfst := Config.step_fst_state P C hμv
    dsimp [C₁]
    rw [hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.rank =
      (C μ).1.rank
    rw [htrace]
  have hw_no_med₁ : (C₁ w).1.rank.val + 1 ≠ ceilHalf n := by
    rw [hw_state₁]
    exact hw_no_med
  have h_no_swap_w₁ :
      ¬((C₁ μ).1.rank < (C₁ w).1.rank ∧
        (C₁ μ).2 = Opinion.B ∧ (C₁ w).2 = Opinion.A) := by
    rintro ⟨hrank, hB, hA⟩
    exact h_no_swap_w ⟨by rwa [hμ_rank₁, hw_state₁] at hrank,
      by rwa [hμ_input₁] at hB,
      by rwa [hw_state₁] at hA⟩
  have h_post_diff_w₁ : opinionToAnswer (C₁ μ).2 ≠ (C₁ w).1.answer := by
    rw [hμ_input₁, hw_state₁]
    exact h_post_diff_w
  obtain ⟨Ltail, hEndpoint⟩ :=
    InSrank_timer_zero_no_swap_diff_to_RankingEndpoint_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog hC₁ hμw hμ_med₁ hw_no_med₁ hμ_timer₁
      h_no_swap_w₁ hpar h_post_diff_w₁
  refine ⟨(μ, v) :: Ltail, ?_⟩
  change RankingEndpoint (runPairs P (C.step P μ v) Ltail)
  exact hEndpoint

theorem InSswap_bad_timer_one_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    {μ : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (C μ).1.timer = 1)
    (hpar : ¬ n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  obtain ⟨v, hμv, hv_max⟩ :=
    hSwap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
  have h_no_swap_max :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hSwap.swap_condition_false μ v
  have h_median_correct :
      opinionToAnswer (C μ).2 = majorityAnswer C :=
    opinionToAnswer_median_eq_majorityAnswer_odd hSwap hμ_med hpar
  by_cases hv_wrong : (C v).1.answer ≠ majorityAnswer C
  · have h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer := by
      rw [h_median_correct]
      exact hv_wrong.symm
    exact
      InSrank_timer_one_max_no_swap_diff_to_RankingEndpoint_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog hbad.1 hμv hμ_med hv_max h_timer
        h_no_swap_max hpar h_post_diff
  · have hv_correct : (C v).1.answer = majorityAnswer C := by
      exact not_not.mp hv_wrong
    by_cases hOnly : ∀ w : Fin n, w ≠ μ → (C w).1.answer = majorityAnswer C
    · exact
        InSswap_bad_timer_one_only_median_wrong_to_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hSwap hμ_med h_timer hpar hOnly
    · push_neg at hOnly
      obtain ⟨w, hwm, hw_wrong⟩ := hOnly
      have hwv : w ≠ v := by
        intro h
        subst w
        exact hw_wrong hv_correct
      have hw_no_med : (C w).1.rank.val + 1 ≠ ceilHalf n := by
        intro hw_med
        apply hwm
        apply hSwap.ranks_inj
        apply Fin.eq_of_val_eq
        have hμ_val : (C μ).1.rank.val = ceilHalf n - 1 := by omega
        have hw_val : (C w).1.rank.val = ceilHalf n - 1 := by omega
        exact hw_val.trans hμ_val.symm
      have h_no_swap_w :
          ¬((C μ).1.rank < (C w).1.rank ∧
            (C μ).2 = Opinion.B ∧ (C w).2 = Opinion.A) :=
        hSwap.swap_condition_false μ w
      have h_post_same_max : opinionToAnswer (C μ).2 = (C v).1.answer := by
        rw [h_median_correct, hv_correct]
      have h_post_diff_w : opinionToAnswer (C μ).2 ≠ (C w).1.answer := by
        rw [h_median_correct]
        exact hw_wrong.symm
      exact
        InSrank_timer_one_max_no_swap_same_then_zero_no_swap_diff_to_RankingEndpoint_log
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog hbad.1 hμv hwm.symm hwv hμ_med hv_max hw_no_med h_timer
          h_no_swap_max h_no_swap_w hpar h_post_same_max h_post_diff_w

theorem InSswap_bad_odd_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    (hpar : ¬ n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  obtain ⟨μ, hμ_med, htimer⟩ := hbad.exists_median_timer_zero_or_one
  rcases htimer with htimer0 | htimer1
  · exact
      InSswap_bad_timer_zero_to_RankingEndpoint_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog hbad hSwap hμ_med htimer0 hpar
  · exact
      InSswap_bad_timer_one_to_RankingEndpoint_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog hbad hSwap hμ_med htimer1 hpar

theorem BadRankingStart_odd_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C)
    (hpar : ¬ n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain hReach :=
    InSrank_reaches_RankingEndpoint_or_InSswap_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog hbad.1
  rcases hReach with hEndpoint | hSwapReach
  · exact hEndpoint
  · obtain ⟨L₁, hSwap₁⟩ := hSwapReach
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    by_cases hDone : RankingEndpoint C₁
    · exact ⟨L₁, by simpa [C₁, P] using hDone⟩
    · have hbad₁ : BadRankingStart C₁ := by
        exact ⟨by simpa [C₁, P] using hSwap₁.toInSrank, hDone⟩
      have hSwapC₁ : InSswap C₁ := by
        simpa [C₁, P] using hSwap₁
      obtain ⟨L₂, hEndpoint₂⟩ :=
        InSswap_bad_odd_to_RankingEndpoint_log
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog hbad₁ hSwapC₁ hpar
      refine ⟨L₁ ++ L₂, ?_⟩
      rw [runPairs_append]
      change RankingEndpoint (runPairs P C₁ L₂)
      exact hEndpoint₂

theorem ranking_from_InSrank_by_parity_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  by_cases hDone : RankingEndpoint C
  · exact
      ranking_goal_of_runPairs_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := [])
        (by simpa using hDone)
  · have hbad : BadRankingStart C := ⟨hSrank, hDone⟩
    by_cases hpar : n % 2 = 0
    · obtain ⟨L, hEndpoint⟩ :=
        BadRankingStart_even_to_RankingEndpoint_log
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog hbad hpar
      exact
        ranking_goal_of_runPairs_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L) hEndpoint
    · obtain ⟨L, hEndpoint⟩ :=
        BadRankingStart_odd_to_RankingEndpoint_log
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog hbad hpar
      exact
        ranking_goal_of_runPairs_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L) hEndpoint

theorem phase1_no_reset_trigger_snapshot_or_InSrank_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∨
        (∃ w : Fin n, (C' w).1.role = .Resetting ∧
          (C' w).1.resetcount = Rmax ∧ (C' w).1.leader = .L ∧
          ∀ y : Fin n, (C' y).1.role = .Resetting →
            (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change ∃ L : List (Fin n × Fin n),
      let C' := runPairs P C L
      InSrank C' ∨
        (∃ w : Fin n, (C' w).1.role = .Resetting ∧
          (C' w).1.resetcount = Rmax ∧ (C' w).1.leader = .L ∧
          ∀ y : Fin n, (C' y).1.role = .Resetting →
            (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L)
  have hReach :
      ∃ L : List (Fin n × Fin n),
        (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting ∧
          (runPairs P C L w).1.resetcount = Rmax ∧
          (runPairs P C L w).1.leader = .L ∧
          ∀ y : Fin n, (runPairs P C L y).1.role = .Resetting →
            (runPairs P C L y).1.resetcount = Rmax ∧
            (runPairs P C L y).1.leader = .L) ∨
        (∀ w : Fin n, (runPairs P C L w).1.role = .Settled) := by
    by_cases hUn : ∃ w : Fin n, (C w).1.role = .Unsettled
    · simpa [P] using
        unsettled_branch_eventually_reset_snapshot_or_allSettled
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 C hUn hNoReset
    · refine ⟨[], Or.inr ?_⟩
      intro w
      simp only [runPairs_nil]
      have hnotU : (C w).1.role ≠ .Unsettled := by
        intro hw
        exact hUn ⟨w, hw⟩
      have hnotR : (C w).1.role ≠ .Resetting := hNoReset w
      cases hrole : (C w).1.role with
      | Resetting => exact False.elim (hnotR hrole)
      | Settled => rfl
      | Unsettled => exact False.elim (hnotU hrole)
  rcases hReach with ⟨L₀, hReach⟩
  rcases hReach with hResetAfter | hAllSettled
  · refine ⟨L₀, ?_⟩
    exact Or.inr hResetAfter
  · set C₀ := runPairs P C L₀
    have hAllSettled₀ : ∀ w : Fin n, (C₀ w).1.role = .Settled := by
      intro w
      simpa [C₀] using hAllSettled w
    by_cases hSrank : InSrank C₀
    · refine ⟨L₀, ?_⟩
      exact Or.inl hSrank
    · obtain ⟨u, v, huv, hcol⟩ :=
        trigger_reset_from_all_settled_non_InSrank_with_leader
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C₀ := C₀) hAllSettled₀ hSrank
      have hsnap :
          ∀ y : Fin n, (runPairs P C₀ [(u, v)] y).1.role = .Resetting →
            (runPairs P C₀ [(u, v)] y).1.resetcount = Rmax ∧
            (runPairs P C₀ [(u, v)] y).1.leader = .L := by
        intro y hy_reset
        by_cases hyu : y = u
        · subst y
          exact ⟨by simpa [P, runPairs] using hcol.2.1,
            by simpa [P, runPairs] using hcol.2.2.1⟩
        · by_cases hyv : y = v
          · subst y
            exact ⟨by simpa [P, runPairs] using hcol.2.2.2.2.1,
              by simpa [P, runPairs] using hcol.2.2.2.2.2⟩
          · have hy_state : runPairs P C₀ [(u, v)] y = C₀ y := by
              simp [runPairs, Config.step, huv, hyu, hyv]
            have hy_settled : (runPairs P C₀ [(u, v)] y).1.role = .Settled := by
              rw [hy_state]
              exact hAllSettled₀ y
            rw [hy_settled] at hy_reset
            cases hy_reset
      refine ⟨L₀ ++ [(u, v)], ?_⟩
      rw [runPairs_append]
      refine Or.inr ⟨u, ?_, ?_, ?_, ?_⟩
      · change (runPairs P C₀ [(u, v)] u).1.role = .Resetting
        simpa [P, runPairs] using hcol.1
      · change (runPairs P C₀ [(u, v)] u).1.resetcount = Rmax
        simpa [P, runPairs] using hcol.2.1
      · change (runPairs P C₀ [(u, v)] u).1.leader = .L
        simpa [P, runPairs] using hcol.2.2.1
      · intro y hy_reset
        change (runPairs P C₀ [(u, v)] y).1.resetcount = Rmax ∧
          (runPairs P C₀ [(u, v)] y).1.leader = .L
        exact hsnap y hy_reset

theorem ranking_of_no_reset_with_bad_start_handler_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting)
    (hBad :
      ∀ Cbad : Config (AgentState n) Opinion n,
        BadRankingStart Cbad →
        ∃ L : List (Fin n × Fin n),
          RankingEndpoint
            (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) Cbad L)) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, h₁⟩ :=
    phase1_no_reset_trigger_snapshot_or_InSrank_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C hNoReset
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  rcases h₁ with hSrank | hSnapshot
  · by_cases hDone : RankingEndpoint C₁
    · exact
        ranking_goal_of_runPairs_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L₁) (by simpa [C₁, P] using hDone)
    · obtain ⟨L₂, hEndpoint₂⟩ := hBad C₁ ⟨by simpa [C₁, P] using hSrank, hDone⟩
      have hEndpoint_total :
          RankingEndpoint (runPairs P C (L₁ ++ L₂)) := by
        rw [runPairs_append]
        change RankingEndpoint (runPairs P C₁ L₂)
        exact hEndpoint₂
      exact
        ranking_goal_of_runPairs_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L₁ ++ L₂) hEndpoint_total
  · rcases hSnapshot with ⟨r, hr_role, hr_rc, hr_L, _hAllSnapshot⟩
    have hReset :
        ∃ r : Fin n, (C₁ r).1.role = .Resetting ∧
          Rmax ≤ (C₁ r).1.resetcount ∧ (C₁ r).1.leader = .L := by
      refine ⟨r, ?_, ?_, ?_⟩
      · simpa [C₁, P] using hr_role
      · have hrc : (C₁ r).1.resetcount = Rmax := by
          simpa [C₁, P] using hr_rc
        rw [hrc]
      · simpa [C₁, P] using hr_L
    obtain ⟨L₂, hEndpoint₂⟩ :=
      reset_snapshot_to_RankingEndpoint_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C₁ hReset
    have hEndpoint_total :
        RankingEndpoint (runPairs P C (L₁ ++ L₂)) := by
      rw [runPairs_append]
      change RankingEndpoint (runPairs P C₁ L₂)
      exact hEndpoint₂
    exact
      ranking_goal_of_runPairs_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁ ++ L₂) hEndpoint_total

theorem ranking_of_no_reset_by_parity_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  by_cases hpar : n % 2 = 0
  · exact
      ranking_of_no_reset_with_bad_start_handler_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C hNoReset
        (fun Cbad hbad =>
          BadRankingStart_even_to_RankingEndpoint_log
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hDmax1 hRlog hbad hpar)
  · exact
      ranking_of_no_reset_with_bad_start_handler_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C hNoReset
        (fun Cbad hbad =>
          BadRankingStart_odd_to_RankingEndpoint_log
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hDmax1 hRlog hbad hpar)

theorem follower_dormant_or_nonresetting_to_ranking_goal_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hClean : FollowerDormantOrNonResetting C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, hNoReset₁⟩ :=
    follower_dormant_or_nonresetting_to_no_reset
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C hClean
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  have hNoResetC₁ : ∀ w : Fin n, (C₁ w).1.role ≠ .Resetting := by
    simpa [C₁, P] using hNoReset₁
  obtain ⟨γ₂, t₂, hgoal₂⟩ :=
    ranking_of_no_reset_by_parity_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog C₁ hNoResetC₁
  exact
    exists_schedule_after_runPairs
      (Goal := fun C' =>
        InSrank C' ∧
          ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n →
            2 ≤ (C' μ).1.timer) ∨
           IsConsensusConfig C'))
      P C L₁ ⟨γ₂, t₂, by simpa [C₁, P] using hgoal₂⟩

theorem ranking_from_settled_root_zero_resetting_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hℓ_settled : (C ℓ).1.role = .Settled)
    (hℓ_rank0 : (C ℓ).1.rank.val = 0)
    (hℓ_children : (C ℓ).1.children = 0)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hResetZero : ∀ w : Fin n, (C w).1.role = .Resetting → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, hNoReset₁⟩ :=
    settled_root_zero_resetting_to_no_reset
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C hℓ_settled hℓ_rank0 hℓ_children hℓ_L hResetZero
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  have hNoResetC₁ : ∀ w : Fin n, (C₁ w).1.role ≠ .Resetting := by
    simpa [C₁, P] using hNoReset₁
  obtain ⟨γ₂, t₂, hgoal₂⟩ :=
    ranking_of_no_reset_by_parity_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog C₁ hNoResetC₁
  exact
    exists_schedule_after_runPairs
      (Goal := fun C' =>
        InSrank C' ∧
          ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n →
            2 ≤ (C' μ).1.timer) ∨
           IsConsensusConfig C'))
      P C L₁ ⟨γ₂, t₂, by simpa [C₁, P] using hgoal₂⟩

theorem ranking_from_all_resetting_zero_no_leader_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllZero : ∀ w : Fin n, (C w).1.resetcount = 0)
    (hNoLeader : ∀ w : Fin n, (C w).1.leader ≠ .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  have hClean : FollowerDormantOrNonResetting C := by
    intro w
    refine Or.inl ⟨hAllReset w, hAllZero w, ?_⟩
    cases hleader : (C w).1.leader with
    | L => exact False.elim ((hNoLeader w) hleader)
    | F => rfl
  exact
    follower_dormant_or_nonresetting_to_ranking_goal_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog C hClean

theorem ranking_from_all_resetting_zero_unique_leader_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax_pos : 0 < Dmax) (hRmax_pos : 0 < Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllZero : ∀ w : Fin n, (C w).1.resetcount = 0)
    (hUniqueLeader : ∃! ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  have hDormant : IsDormantConfig C := by
    refine ⟨hAllReset, hAllZero, hUniqueLeader, ?_⟩
    intro w
    cases (C w).1.leader <;> simp
  obtain ⟨L, hEndpoint⟩ :=
    dormant_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax_pos hDmax_pos C hDormant
  exact
    ranking_goal_of_runPairs_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L) hEndpoint

set_option maxHeartbeats 8000000 in
theorem ranking_from_all_resetting_zero_with_leader_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllZero : ∀ w : Fin n, (C w).1.resetcount = 0)
    (hHasLeader : ∃ ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  have hRmax_pos : 0 < Rmax := by omega
  suffices go :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        resetLeaderCount C₀ = k →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting) →
        (∀ w : Fin n, (C₀ w).1.resetcount = 0) →
        (∃ ℓ : Fin n, (C₀ ℓ).1.leader = .L) →
        ∃ (γ : DetScheduler n) (t : ℕ),
          InSrank (execution P C₀ γ t) ∧
          ((∀ μ : Fin n,
            (execution P C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
            2 ≤ (execution P C₀ γ t μ).1.timer) ∨
           IsConsensusConfig (execution P C₀ γ t)) by
    simpa [P] using go (resetLeaderCount C) C rfl hAllReset hAllZero hHasLeader
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
    intro C₀ hk hAllR hAll0 hHasL
    by_cases hUnique : ∃! ℓ : Fin n, (C₀ ℓ).1.leader = .L
    · simpa [P] using
        ranking_from_all_resetting_zero_unique_leader_log
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax_pos hRmax_pos C₀ hAllR hAll0 hUnique
    · obtain ⟨ℓ, hℓ_L⟩ := hHasL
      have hOther : ∃ w : Fin n, w ≠ ℓ ∧ (C₀ w).1.leader = .L := by
        by_contra hnone
        push_neg at hnone
        apply hUnique
        refine ⟨ℓ, hℓ_L, ?_⟩
        intro y hyL
        by_contra hy_ne
        exact hnone y hy_ne hyL
      obtain ⟨w, hw_ne_ℓ, hw_L⟩ := hOther
      have hℓw : ℓ ≠ w := hw_ne_ℓ.symm
      by_cases hℓ_high : 1 < (C₀ ℓ).1.delaytimer
      · by_cases hw_high : 1 < (C₀ w).1.delaytimer
        · let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ w
          have hstep :=
            step_leader_dedup_trace
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (ℓ := ℓ) (w := w) hℓw
              (hAllR ℓ) (hAll0 ℓ) (hAllR w) (hAll0 w) hℓ_L hw_L
              hℓ_high hw_high
          have hAllR₁ : ∀ x : Fin n, (C₁ x).1.role = .Resetting := by
            intro x
            by_cases hxℓ : x = ℓ
            · subst x
              exact hstep.1
            · by_cases hxw : x = w
              · subst x
                exact hstep.2.2.2.2.1
              · rw [show C₁ x = C₀ x from hstep.2.2.2.2.2.2.2.2 x hxℓ hxw]
                exact hAllR x
          have hAll0₁ : ∀ x : Fin n, (C₁ x).1.resetcount = 0 := by
            intro x
            by_cases hxℓ : x = ℓ
            · subst x
              exact hstep.2.1
            · by_cases hxw : x = w
              · subst x
                exact hstep.2.2.2.2.2.1
              · rw [show C₁ x = C₀ x from hstep.2.2.2.2.2.2.2.2 x hxℓ hxw]
                exact hAll0 x
          have hHasL₁ : ∃ x : Fin n, (C₁ x).1.leader = .L :=
            ⟨ℓ, hstep.2.2.1⟩
          have hcount_lt : resetLeaderCount C₁ < resetLeaderCount C₀ := by
            simpa [P, C₁] using
              (step_leader_dedup_resetLeaderCount_lt
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C₀) (ℓ := ℓ) (w := w) hℓw
                (hAllR ℓ) (hAll0 ℓ) (hAllR w) (hAll0 w) hℓ_L hw_L
                hℓ_high hw_high)
          have hgoal₁ :=
            IH (resetLeaderCount C₁) (by omega) C₁ rfl hAllR₁ hAll0₁ hHasL₁
          exact
            ranking_goal_of_step_ranking_goal
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (u := ℓ) (v := w)
              (by simpa [P, C₁] using hgoal₁)
        · have hw_low : (C₀ w).1.delaytimer ≤ 1 := by omega
          let C₁ : Config (AgentState n) Opinion n := C₀.step P w ℓ
          have hstep :=
            transitionPEM_dormant_leader_low_dt_L_partner_wakes
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 (C := C₀) (ℓ := w) (w := ℓ) hw_ne_ℓ
              (hAllR w) (hAll0 w) hw_low hw_L (hAllR ℓ) (hAll0 ℓ) hℓ_L
          have hResetZero₁ :
              ∀ x : Fin n, (C₁ x).1.role = .Resetting → (C₁ x).1.resetcount = 0 := by
            intro x hx_reset
            by_cases hxw : x = w
            · subst x
              rw [hstep.1] at hx_reset
              cases hx_reset
            · by_cases hxℓ : x = ℓ
              · subst x
                rcases hstep.2.2.2.2 with hsettled | hreset
                · rw [hsettled] at hx_reset
                  cases hx_reset
                · exact hreset.2.1
              · have hx_old : C₁ x = C₀ x := by
                  dsimp [C₁, P]
                  simp [Config.step, hw_ne_ℓ, hxw, hxℓ]
                rw [hx_old] at hx_reset ⊢
                exact hAll0 x
          have hgoal₁ :=
            ranking_from_settled_root_zero_resetting_log
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 hDmax1 hRlog C₁
              (ℓ := w) hstep.1 hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 hResetZero₁
          exact
            ranking_goal_of_step_ranking_goal
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (u := w) (v := ℓ)
              (by simpa [P, C₁] using hgoal₁)
      · have hℓ_low : (C₀ ℓ).1.delaytimer ≤ 1 := by omega
        let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ w
        have hstep :=
          transitionPEM_dormant_leader_low_dt_L_partner_wakes
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 (C := C₀) (ℓ := ℓ) (w := w) hℓw
            (hAllR ℓ) (hAll0 ℓ) hℓ_low hℓ_L (hAllR w) (hAll0 w) hw_L
        have hResetZero₁ :
            ∀ x : Fin n, (C₁ x).1.role = .Resetting → (C₁ x).1.resetcount = 0 := by
          intro x hx_reset
          by_cases hxℓ : x = ℓ
          · subst x
            rw [hstep.1] at hx_reset
            cases hx_reset
          · by_cases hxw : x = w
            · subst x
              rcases hstep.2.2.2.2 with hsettled | hreset
              · rw [hsettled] at hx_reset
                cases hx_reset
              · exact hreset.2.1
            · have hx_old : C₁ x = C₀ x := by
                dsimp [C₁, P]
                simp [Config.step, hℓw, hxℓ, hxw]
              rw [hx_old] at hx_reset ⊢
              exact hAll0 x
        have hgoal₁ :=
          ranking_from_settled_root_zero_resetting_log
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hDmax1 hRlog C₁
            (ℓ := ℓ) hstep.1 hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 hResetZero₁
        exact
          ranking_goal_of_step_ranking_goal
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C₀) (u := ℓ) (v := w)
            (by simpa [P, C₁] using hgoal₁)

theorem ranking_from_all_resetting_zero_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllZero : ∀ w : Fin n, (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  by_cases hHasLeader : ∃ ℓ : Fin n, (C ℓ).1.leader = .L
  · exact
      ranking_from_all_resetting_zero_with_leader_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C hAllReset hAllZero hHasLeader
  · exact
      ranking_from_all_resetting_zero_no_leader_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C hAllReset hAllZero
        (by
          intro w hwL
          exact hHasLeader ⟨w, hwL⟩)

set_option maxHeartbeats 16000000 in
theorem ranking_from_all_resetting_single_pos_leader_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ v : Fin n}
    (hℓv : ℓ ≠ v)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_pos : 0 < (C ℓ).1.resetcount)
    (hOnlyPos : ∀ w : Fin n, w ≠ ℓ → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  have hv_zero : (C v).1.resetcount = 0 := hOnlyPos v hℓv.symm
  by_cases hv_high : 1 < (C v).1.delaytimer
  · obtain ⟨L₁, hℓ_role₁, hℓ_rc₁, _hℓ_L₁, hv_role₁, hv_rc₁, _hv_F₁, hothers₁⟩ :=
      drain_L_pos_any_zero_to_zero
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax_pos C hℓv (hAllReset ℓ) (hAllReset v) hℓ_pos hv_zero hℓ_L hv_high
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
      intro w
      by_cases hwℓ : w = ℓ
      · subst w
        simpa [C₁, P] using hℓ_role₁
      · by_cases hwv : w = v
        · subst w
          simpa [C₁, P] using hv_role₁
        · dsimp [C₁]
          rw [hothers₁ w hwℓ hwv]
          exact hAllReset w
    have hAllZero₁ : ∀ w : Fin n, (C₁ w).1.resetcount = 0 := by
      intro w
      by_cases hwℓ : w = ℓ
      · subst w
        simpa [C₁, P] using hℓ_rc₁
      · by_cases hwv : w = v
        · subst w
          simpa [C₁, P] using hv_rc₁
        · dsimp [C₁]
          rw [hothers₁ w hwℓ hwv]
          exact hOnlyPos w hwℓ
    have hgoal₁ :=
      ranking_from_all_resetting_zero_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C₁ hAllReset₁ hAllZero₁
    exact
      ranking_goal_of_runPairs_ranking_goal
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁)
        (by simpa [C₁, P] using hgoal₁)
  · have hv_low : (C v).1.delaytimer ≤ 1 := by omega
    by_cases hgt : 1 < (C ℓ).1.resetcount
    · have hstep :=
        step_L_pos_any_zero_gt_one
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          C hℓv (hAllReset ℓ) (hAllReset v) hgt hv_zero hℓ_L
      let C₁ : Config (AgentState n) Opinion n := C.step P ℓ v
      have hℓ_role₁ : (C₁ ℓ).1.role = .Resetting := by
        simpa [C₁, P] using hstep.1
      have hv_role₁ : (C₁ v).1.role = .Resetting := by
        simpa [C₁, P] using hstep.2.1
      have hℓ_rc₁ : (C₁ ℓ).1.resetcount = (C ℓ).1.resetcount - 1 := by
        simpa [C₁, P] using hstep.2.2.1
      have hv_rc₁ : (C₁ v).1.resetcount = (C ℓ).1.resetcount - 1 := by
        simpa [C₁, P] using hstep.2.2.2.1
      have hℓ_pos₁ : 0 < (C₁ ℓ).1.resetcount := by
        rw [hℓ_rc₁]; omega
      have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
        rw [hv_rc₁]; omega
      obtain ⟨L₂, hℓ_fresh₂, hv_fresh₂, hothers₂⟩ :=
        drain_pair_rc_with_both_delay
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax1 C₁ hℓv hℓ_role₁ hv_role₁ hℓ_pos₁ hv_pos₁
      let C₂ : Config (AgentState n) Opinion n := runPairs P C₁ L₂
      have hothers_step : ∀ w : Fin n, w ≠ ℓ → w ≠ v → C₁ w = C w := by
        intro w hwℓ hwv
        simp [C₁, Config.step, P, hℓv, hwℓ, hwv]
      have hAllReset₂ : ∀ w : Fin n, (C₂ w).1.role = .Resetting := by
        intro w
        by_cases hwℓ : w = ℓ
        · subst w
          exact hℓ_fresh₂.1
        · by_cases hwv : w = v
          · subst w
            exact hv_fresh₂.1
          · dsimp [C₂]
            rw [hothers₂ w hwℓ hwv, hothers_step w hwℓ hwv]
            exact hAllReset w
      have hAllZero₂ : ∀ w : Fin n, (C₂ w).1.resetcount = 0 := by
        intro w
        by_cases hwℓ : w = ℓ
        · subst w
          exact hℓ_fresh₂.2.1
        · by_cases hwv : w = v
          · subst w
            exact hv_fresh₂.2.1
          · dsimp [C₂]
            rw [hothers₂ w hwℓ hwv, hothers_step w hwℓ hwv]
            exact hOnlyPos w hwℓ
      have hgoal₂ :=
        ranking_from_all_resetting_zero_log
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog C₂ hAllReset₂ hAllZero₂
      have hgoal₁ :=
        ranking_goal_of_runPairs_ranking_goal
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C₁) (L := L₂)
          (by simpa [C₂, P] using hgoal₂)
      exact
        ranking_goal_of_step_ranking_goal
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (u := ℓ) (v := v)
          (by simpa [C₁, P] using hgoal₁)
    · have hℓ_one : (C ℓ).1.resetcount = 1 := by omega
      cases hv_leader : (C v).1.leader with
      | L =>
          have hstep :=
            step_L_pos_one_L_zero_low
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hDmax_pos C hℓv (hAllReset ℓ) (hAllReset v) hℓ_one hv_zero
              hℓ_L hv_leader hv_low
          let C₁ : Config (AgentState n) Opinion n := C.step P ℓ v
          have hResetZero₁ :
              ∀ w : Fin n, (C₁ w).1.role = .Resetting → (C₁ w).1.resetcount = 0 := by
            intro w hw_reset
            by_cases hwℓ : w = ℓ
            · subst w
              simpa [C₁, P] using hstep.2.1
            · by_cases hwv : w = v
              · subst w
                have hv_settled : (C₁ v).1.role = .Settled := by
                  simpa [C₁, P] using hstep.2.2.2.2.1
                rw [hv_settled] at hw_reset
                cases hw_reset
              · have hw_old : C₁ w = C w := by
                  dsimp [C₁, P]
                  simp [Config.step, hℓv, hwℓ, hwv]
                rw [hw_old] at hw_reset ⊢
                exact hOnlyPos w hwℓ
          have hgoal₁ :=
            ranking_from_settled_root_zero_resetting_log
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 hDmax1 hRlog C₁ (ℓ := v)
              (by simpa [C₁, P] using hstep.2.2.2.2.1)
              (by simpa [C₁, P] using hstep.2.2.2.2.2.1)
              (by simpa [C₁, P] using hstep.2.2.2.2.2.2.1)
              (by simpa [C₁, P] using hstep.2.2.2.2.2.2.2)
              hResetZero₁
          exact
            ranking_goal_of_step_ranking_goal
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C) (u := ℓ) (v := v)
              (by simpa [C₁, P] using hgoal₁)
      | F =>
          have hstep₁ :=
            step_L_pos_one_F_zero_low
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hDmax_pos C hℓv (hAllReset ℓ) (hAllReset v) hℓ_one hv_zero
              hℓ_L hv_leader hv_low
          let C₁ : Config (AgentState n) Opinion n := C.step P ℓ v
          have hstep₂ :=
            transitionPEM_dormant_leader_with_unsettled_follower_wakes
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₁) (ℓ := ℓ) (w := v) hℓv
              (by simpa [C₁, P] using hstep₁.1)
              (by simpa [C₁, P] using hstep₁.2.1)
              (by simpa [C₁, P] using hstep₁.2.2.1)
              (by simpa [C₁, P] using hstep₁.2.2.2.2.1)
              (by simpa [C₁, P] using hstep₁.2.2.2.2.2)
          let C₂ : Config (AgentState n) Opinion n := C₁.step P ℓ v
          have hResetZero₂ :
              ∀ w : Fin n, (C₂ w).1.role = .Resetting → (C₂ w).1.resetcount = 0 := by
            intro w hw_reset
            by_cases hwℓ : w = ℓ
            · subst w
              have hsettled : (C₂ ℓ).1.role = .Settled := by
                simpa [C₂, P] using hstep₂.1
              rw [hsettled] at hw_reset
              cases hw_reset
            · by_cases hwv : w = v
              · subst w
                have hun : (C₂ v).1.role = .Unsettled := by
                  simpa [C₂, P] using hstep₂.2.2.2.2.1
                rw [hun] at hw_reset
                cases hw_reset
              · have hw_old₂ : C₂ w = C₁ w := by
                  dsimp [C₂, P]
                  simp [Config.step, hℓv, hwℓ, hwv]
                have hw_old₁ : C₁ w = C w := by
                  dsimp [C₁, P]
                  simp [Config.step, hℓv, hwℓ, hwv]
                rw [hw_old₂, hw_old₁] at hw_reset ⊢
                exact hOnlyPos w hwℓ
          have hgoal₂ :=
            ranking_from_settled_root_zero_resetting_log
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 hDmax1 hRlog C₂ (ℓ := ℓ)
              (by simpa [C₂, P] using hstep₂.1)
              (by
                have hrank : (C₂ ℓ).1.rank = ⟨0, hn⟩ := by
                  simpa [C₂, P] using hstep₂.2.1
                rw [hrank])
              (by simpa [C₂, P] using hstep₂.2.2.1)
              (by simpa [C₂, P] using hstep₂.2.2.2.1)
              hResetZero₂
          have hgoal₁ :=
            ranking_goal_of_step_ranking_goal
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₁) (u := ℓ) (v := v)
              (by simpa [C₂, P] using hgoal₂)
          exact
            ranking_goal_of_step_ranking_goal
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C) (u := ℓ) (v := v)
              (by simpa [C₁, P] using hgoal₁)

set_option maxHeartbeats 16000000 in
theorem ranking_from_all_resetting_single_pos_follower_F_partner_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {u v : Fin n}
    (huv : u ≠ v)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllF : ∀ w : Fin n, (C w).1.leader = .F)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F)
    (hu_pos : 0 < (C u).1.resetcount)
    (hOnlyPos : ∀ w : Fin n, w ≠ u → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  have hv_zero : (C v).1.resetcount = 0 := hOnlyPos v huv.symm
  by_cases hv_high : 1 < (C v).1.delaytimer
  · obtain ⟨L₁, hu_role₁, hu_rc₁, hu_F₁, hv_role₁, hv_rc₁, hv_F₁, hothers₁⟩ :=
      drain_F_pos_F_zero_to_zero_FF
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax_pos C huv (hAllReset u) (hAllReset v) hu_pos hv_zero
        hu_F hv_F hv_high
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    have hClean₁ : FollowerDormantOrNonResetting C₁ := by
      intro w
      by_cases hwu : w = u
      · subst w
        exact Or.inl ⟨by simpa [C₁, P] using hu_role₁,
          by simpa [C₁, P] using hu_rc₁,
          by simpa [C₁, P] using hu_F₁⟩
      · by_cases hwv : w = v
        · subst w
          exact Or.inl ⟨by simpa [C₁, P] using hv_role₁,
            by simpa [C₁, P] using hv_rc₁,
            by simpa [C₁, P] using hv_F₁⟩
        · dsimp [C₁]
          rw [hothers₁ w hwu hwv]
          exact Or.inl ⟨hAllReset w, hOnlyPos w hwu, hAllF w⟩
    have hgoal₁ :=
      follower_dormant_or_nonresetting_to_ranking_goal_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C₁ hClean₁
    exact
      ranking_goal_of_runPairs_ranking_goal
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁)
        (by simpa [C₁, P] using hgoal₁)
  · have hv_low : (C v).1.delaytimer ≤ 1 := by omega
    by_cases hu_gt : 1 < (C u).1.resetcount
    · have hstep :=
        step_F_pos_F_zero_gt_one
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          C huv (hAllReset u) (hAllReset v) hu_gt hv_zero hu_F hv_F
      let C₁ : Config (AgentState n) Opinion n := C.step P u v
      have hu_role₁ : (C₁ u).1.role = .Resetting := by
        simpa [C₁, P] using hstep.1
      have hv_role₁ : (C₁ v).1.role = .Resetting := by
        simpa [C₁, P] using hstep.2.1
      have hu_rc₁ : (C₁ u).1.resetcount = (C u).1.resetcount - 1 := by
        simpa [C₁, P] using hstep.2.2.1
      have hv_rc₁ : (C₁ v).1.resetcount = (C u).1.resetcount - 1 := by
        simpa [C₁, P] using hstep.2.2.2.1
      have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
        rw [hu_rc₁]; omega
      have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
        rw [hv_rc₁]; omega
      obtain ⟨L₂, hu_role₂, hu_rc₂, hu_F₂, hv_role₂, hv_rc₂, hv_F₂, hothers₂⟩ :=
        drain_pair_rc_FF
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax_pos C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁
          (by simpa [C₁, P] using hstep.2.2.2.2.1)
          (by simpa [C₁, P] using hstep.2.2.2.2.2)
      let C₂ : Config (AgentState n) Opinion n := runPairs P C₁ L₂
      have hothers_step : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
        intro w hwu hwv
        simp [C₁, Config.step, P, huv, hwu, hwv]
      have hClean₂ : FollowerDormantOrNonResetting C₂ := by
        intro w
        by_cases hwu : w = u
        · subst w
          exact Or.inl ⟨by simpa [C₂, P] using hu_role₂,
            by simpa [C₂, P] using hu_rc₂,
            by simpa [C₂, P] using hu_F₂⟩
        · by_cases hwv : w = v
          · subst w
            exact Or.inl ⟨by simpa [C₂, P] using hv_role₂,
              by simpa [C₂, P] using hv_rc₂,
              by simpa [C₂, P] using hv_F₂⟩
          · dsimp [C₂]
            rw [hothers₂ w hwu hwv, hothers_step w hwu hwv]
            exact Or.inl ⟨hAllReset w, hOnlyPos w hwu, hAllF w⟩
      have hgoal₂ :=
        follower_dormant_or_nonresetting_to_ranking_goal_log
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog C₂ hClean₂
      have hgoal₁ :=
        ranking_goal_of_runPairs_ranking_goal
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C₁) (L := L₂)
          (by simpa [C₂, P] using hgoal₂)
      exact
        ranking_goal_of_step_ranking_goal
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (u := u) (v := v)
          (by simpa [C₁, P] using hgoal₁)
    · have hu_one : (C u).1.resetcount = 1 := by omega
      have hstep :=
        step_F_pos_one_F_zero_low
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax_pos C huv (hAllReset u) (hAllReset v) hu_one hv_zero hu_F hv_F hv_low
      let C₁ : Config (AgentState n) Opinion n := C.step P u v
      have hClean₁ : FollowerDormantOrNonResetting C₁ := by
        intro w
        by_cases hwu : w = u
        · subst w
          exact Or.inl ⟨by simpa [C₁, P] using hstep.1,
            by simpa [C₁, P] using hstep.2.1,
            by simpa [C₁, P] using hstep.2.2.1⟩
        · by_cases hwv : w = v
          · subst w
            exact Or.inr (by
              intro hv_reset
              have hv_un : (C₁ v).1.role = .Unsettled := by
                simpa [C₁, P] using hstep.2.2.2.2.1
              rw [hv_un] at hv_reset
              cases hv_reset)
          · dsimp [C₁]
            simp [Config.step, P, huv, hwu, hwv]
            exact Or.inl ⟨hAllReset w, hOnlyPos w hwu, hAllF w⟩
      have hgoal₁ :=
        follower_dormant_or_nonresetting_to_ranking_goal_log
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog C₁ hClean₁
      exact
        ranking_goal_of_step_ranking_goal
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (u := u) (v := v)
          (by simpa [C₁, P] using hgoal₁)

set_option maxHeartbeats 16000000 in
theorem ranking_from_all_resetting_single_pos_follower_L_partner_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {u ℓ : Fin n}
    (hℓu : ℓ ≠ u)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hu_F : (C u).1.leader = .F) (hℓ_L : (C ℓ).1.leader = .L)
    (hu_pos : 0 < (C u).1.resetcount)
    (hOnlyPos : ∀ w : Fin n, w ≠ u → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  have hℓ_zero : (C ℓ).1.resetcount = 0 := hOnlyPos ℓ hℓu
  by_cases hu_gt : 1 < (C u).1.resetcount
  · have hstep :=
      step_L_zero_F_pos_gt_one
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        C hℓu (hAllReset ℓ) (hAllReset u) hℓ_zero hu_gt hℓ_L hu_F
    let C₁ : Config (AgentState n) Opinion n := C.step P ℓ u
    have hℓ_role₁ : (C₁ ℓ).1.role = .Resetting := by
      simpa [C₁, P] using hstep.1
    have hu_role₁ : (C₁ u).1.role = .Resetting := by
      simpa [C₁, P] using hstep.2.1
    have hℓ_rc₁ : (C₁ ℓ).1.resetcount = (C u).1.resetcount - 1 := by
      simpa [C₁, P] using hstep.2.2.1
    have hu_rc₁ : (C₁ u).1.resetcount = (C u).1.resetcount - 1 := by
      simpa [C₁, P] using hstep.2.2.2.1
    have hℓ_pos₁ : 0 < (C₁ ℓ).1.resetcount := by
      rw [hℓ_rc₁]; omega
    have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
      rw [hu_rc₁]; omega
    obtain ⟨L₂, hℓ_fresh₂, hu_fresh₂, hothers₂⟩ :=
      drain_pair_rc_with_both_delay
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax1 C₁ hℓu hℓ_role₁ hu_role₁ hℓ_pos₁ hu_pos₁
    let C₂ : Config (AgentState n) Opinion n := runPairs P C₁ L₂
    have hothers_step : ∀ w : Fin n, w ≠ ℓ → w ≠ u → C₁ w = C w := by
      intro w hwℓ hwu
      simp [C₁, Config.step, P, hℓu, hwℓ, hwu]
    have hAllReset₂ : ∀ w : Fin n, (C₂ w).1.role = .Resetting := by
      intro w
      by_cases hwℓ : w = ℓ
      · subst w
        exact hℓ_fresh₂.1
      · by_cases hwu : w = u
        · subst w
          exact hu_fresh₂.1
        · dsimp [C₂]
          rw [hothers₂ w hwℓ hwu, hothers_step w hwℓ hwu]
          exact hAllReset w
    have hAllZero₂ : ∀ w : Fin n, (C₂ w).1.resetcount = 0 := by
      intro w
      by_cases hwℓ : w = ℓ
      · subst w
        exact hℓ_fresh₂.2.1
      · by_cases hwu : w = u
        · subst w
          exact hu_fresh₂.2.1
        · dsimp [C₂]
          rw [hothers₂ w hwℓ hwu, hothers_step w hwℓ hwu]
          exact hOnlyPos w hwu
    have hgoal₂ :=
      ranking_from_all_resetting_zero_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C₂ hAllReset₂ hAllZero₂
    have hgoal₁ :=
      ranking_goal_of_runPairs_ranking_goal
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C₁) (L := L₂)
        (by simpa [C₂, P] using hgoal₂)
    exact
      ranking_goal_of_step_ranking_goal
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := ℓ) (v := u)
        (by simpa [C₁, P] using hgoal₁)
  · have hu_one : (C u).1.resetcount = 1 := by omega
    by_cases hℓ_high : 1 < (C ℓ).1.delaytimer
    · have hstep :=
        step_L_zero_F_pos
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax_pos C hℓu (hAllReset ℓ) (hAllReset u)
          hℓ_zero hu_pos hℓ_L hu_F hℓ_high
      let C₁ : Config (AgentState n) Opinion n := C.step P ℓ u
      have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
        intro w
        by_cases hwℓ : w = ℓ
        · subst w
          simpa [C₁, P] using hstep.1
        · by_cases hwu : w = u
          · subst w
            simpa [C₁, P] using hstep.2.1
          · dsimp [C₁]
            simp [Config.step, P, hℓu, hwℓ, hwu]
            exact hAllReset w
      have hAllZero₁ : ∀ w : Fin n, (C₁ w).1.resetcount = 0 := by
        intro w
        by_cases hwℓ : w = ℓ
        · subst w
          have hrc : (C₁ ℓ).1.resetcount = (C u).1.resetcount - 1 := by
            simpa [C₁, P] using hstep.2.2.1
          rw [hrc, hu_one]
        · by_cases hwu : w = u
          · subst w
            have hrc : (C₁ u).1.resetcount = (C u).1.resetcount - 1 := by
              simpa [C₁, P] using hstep.2.2.2.1
            rw [hrc, hu_one]
          · dsimp [C₁]
            simp [Config.step, P, hℓu, hwℓ, hwu]
            exact hOnlyPos w hwu
      have hgoal₁ :=
        ranking_from_all_resetting_zero_log
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog C₁ hAllReset₁ hAllZero₁
      exact
        ranking_goal_of_step_ranking_goal
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (u := ℓ) (v := u)
          (by simpa [C₁, P] using hgoal₁)
    · have hℓ_low : (C ℓ).1.delaytimer ≤ 1 := by omega
      have hstep :=
        step_L_zero_F_pos_one_low
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax_pos C hℓu (hAllReset ℓ) (hAllReset u)
          hℓ_zero hu_one hℓ_L hu_F hℓ_low
      let C₁ : Config (AgentState n) Opinion n := C.step P ℓ u
      have hResetZero₁ :
          ∀ w : Fin n, (C₁ w).1.role = .Resetting → (C₁ w).1.resetcount = 0 := by
        intro w hw_reset
        by_cases hwℓ : w = ℓ
        · subst w
          have hsettled : (C₁ ℓ).1.role = .Settled := by
            simpa [C₁, P] using hstep.1
          rw [hsettled] at hw_reset
          cases hw_reset
        · by_cases hwu : w = u
          · subst w
            simpa [C₁, P] using hstep.2.2.2.2.2.1
          · have hw_old : C₁ w = C w := by
              dsimp [C₁, P]
              simp [Config.step, hℓu, hwℓ, hwu]
            rw [hw_old] at hw_reset ⊢
            exact hOnlyPos w hwu
      have hgoal₁ :=
        ranking_from_settled_root_zero_resetting_log
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog C₁ (ℓ := ℓ)
          (by simpa [C₁, P] using hstep.1)
          (by simpa [C₁, P] using hstep.2.1)
          (by simpa [C₁, P] using hstep.2.2.1)
          (by simpa [C₁, P] using hstep.2.2.2.1)
          hResetZero₁
      exact
        ranking_goal_of_step_ranking_goal
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (u := ℓ) (v := u)
          (by simpa [C₁, P] using hgoal₁)

set_option maxHeartbeats 32000000 in
theorem ranking_from_all_resetting_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices go :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        (positiveRcAgents C₀).card = k →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting) →
        ∃ (γ : DetScheduler n) (t : ℕ),
          InSrank (execution P C₀ γ t) ∧
          ((∀ μ : Fin n,
            (execution P C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
            2 ≤ (execution P C₀ γ t μ).1.timer) ∨
           IsConsensusConfig (execution P C₀ γ t)) by
    simpa [P] using go (positiveRcAgents C).card C rfl hAllReset
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
      intro C₀ hcard hAllReset₀
      by_cases hcard0 : k = 0
      · have hAllZero₀ : ∀ w : Fin n, (C₀ w).1.resetcount = 0 := by
          apply positiveRcAgents_eq_zero_iff.mp
          rw [hcard, hcard0]
        simpa [P] using
          ranking_from_all_resetting_zero_log
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hDmax1 hRlog C₀ hAllReset₀ hAllZero₀
      · have hcard_pos : 0 < (positiveRcAgents C₀).card := by
          rw [hcard]
          omega
        obtain ⟨u, hu_pos⟩ :=
          positiveRcAgents_exists_of_card_pos (C := C₀) hcard_pos
        by_cases hSecond : ∃ v : Fin n, v ≠ u ∧ 0 < (C₀ v).1.resetcount
        · obtain ⟨v, hv_ne, hv_pos⟩ := hSecond
          have huv : u ≠ v := hv_ne.symm
          obtain ⟨L₁, hu_fresh₁, hv_fresh₁, hothers₁⟩ :=
            drain_pair_rc_with_both_delay
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hDmax1 C₀ huv (hAllReset₀ u) (hAllReset₀ v) hu_pos hv_pos
          let C₁ : Config (AgentState n) Opinion n := runPairs P C₀ L₁
          have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
            intro w
            by_cases hwu : w = u
            · subst w
              exact hu_fresh₁.1
            · by_cases hwv : w = v
              · subst w
                exact hv_fresh₁.1
              · dsimp [C₁]
                rw [hothers₁ w hwu hwv]
                exact hAllReset₀ w
          have hsub : positiveRcAgents C₁ ⊆ (positiveRcAgents C₀).erase u := by
            intro w hw_mem
            rw [positiveRcAgents, Finset.mem_filter] at hw_mem
            have hw_pos : 0 < (C₁ w).1.resetcount := hw_mem.2
            rw [Finset.mem_erase]
            refine ⟨?_, ?_⟩
            · intro hwu
              subst w
              rw [hu_fresh₁.2.1] at hw_pos
              omega
            · rw [positiveRcAgents, Finset.mem_filter]
              by_cases hwv : w = v
              · subst w
                rw [hv_fresh₁.2.1] at hw_pos
                omega
              · have hwu : w ≠ u := by
                  intro hwu
                  subst w
                  rw [hu_fresh₁.2.1] at hw_pos
                  omega
                have hw_old : C₁ w = C₀ w := hothers₁ w hwu hwv
                have hw_old_pos : 0 < (C₀ w).1.resetcount := by
                  rwa [hw_old] at hw_pos
                exact ⟨Finset.mem_univ w, hw_old_pos⟩
          have hu_mem_old : u ∈ positiveRcAgents C₀ := by
            rw [positiveRcAgents, Finset.mem_filter]
            exact ⟨Finset.mem_univ u, hu_pos⟩
          have hcard₁_lt : (positiveRcAgents C₁).card < k := by
            have hle := Finset.card_le_card hsub
            have herase :
                ((positiveRcAgents C₀).erase u).card =
                  (positiveRcAgents C₀).card - 1 :=
              Finset.card_erase_of_mem hu_mem_old
            rw [herase, hcard] at hle
            omega
          have hgoal₁ :=
            IH (positiveRcAgents C₁).card hcard₁_lt C₁ rfl hAllReset₁
          exact
            ranking_goal_of_runPairs_ranking_goal
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (L := L₁)
              (by simpa [C₁, P] using hgoal₁)
        · push_neg at hSecond
          have hOnlyPos : ∀ w : Fin n, w ≠ u → (C₀ w).1.resetcount = 0 := by
            intro w hw
            have hle : (C₀ w).1.resetcount ≤ 0 := hSecond w hw
            omega
          have hcard_fin : 1 < Fintype.card (Fin n) := by
            rw [Fintype.card_fin]
            omega
          obtain ⟨v, hv_ne_u⟩ := Fintype.exists_ne_of_one_lt_card hcard_fin u
          cases hu_leader : (C₀ u).1.leader with
          | L =>
              simpa [P] using
                ranking_from_all_resetting_single_pos_leader_log
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hn4 hDmax1 hRlog C₀ hv_ne_u.symm hAllReset₀ hu_leader hu_pos
                  hOnlyPos
          | F =>
              by_cases hHasLeader : ∃ ℓ : Fin n, (C₀ ℓ).1.leader = .L
              · obtain ⟨ℓ, hℓ_L⟩ := hHasLeader
                have hℓu : ℓ ≠ u := by
                  intro h
                  subst ℓ
                  rw [hu_leader] at hℓ_L
                  cases hℓ_L
                simpa [P] using
                  ranking_from_all_resetting_single_pos_follower_L_partner_log
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    hn4 hDmax1 hRlog C₀ hℓu hAllReset₀ hu_leader hℓ_L hu_pos
                    hOnlyPos
              · have hAllF : ∀ w : Fin n, (C₀ w).1.leader = .F := by
                  intro w
                  cases hw_leader : (C₀ w).1.leader with
                  | L => exact False.elim (hHasLeader ⟨w, hw_leader⟩)
                  | F => rfl
                simpa [P] using
                  ranking_from_all_resetting_single_pos_follower_F_partner_log
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    hn4 hDmax1 hRlog C₀ hv_ne_u.symm hAllReset₀ hAllF
                    hu_leader (hAllF v) hu_pos hOnlyPos

set_option maxHeartbeats 32000000 in
theorem partial_resetting_to_ranking_goal_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hSomeReset : ∃ r : Fin n, (C r).1.role = .Resetting)
    (hNotAllReset : ¬ ∀ w : Fin n, (C w).1.role = .Resetting) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices h_aux :
      ∀ k : ℕ, ∀ C' : Config (AgentState n) Opinion n,
        resetFuel C' ≤ k →
        (∃ r : Fin n, (C' r).1.role = .Resetting) →
        (¬ ∀ w : Fin n, (C' w).1.role = .Resetting) →
        ∃ (γ : DetScheduler n) (t : ℕ),
          InSrank (execution P C' γ t) ∧
          ((∀ μ : Fin n,
            (execution P C' γ t μ).1.rank.val + 1 = ceilHalf n →
            2 ≤ (execution P C' γ t μ).1.timer) ∨
           IsConsensusConfig (execution P C' γ t)) by
    simpa [P] using h_aux (resetFuel C) C le_rfl hSomeReset hNotAllReset
  intro k
  induction k with
  | zero =>
      intro C' hF hSome _hNot
      obtain ⟨r, hr⟩ := hSome
      have hcontrib_pos : 0 < resetFuelContribution (C' r).1 := by
        unfold resetFuelContribution
        rw [if_pos hr]
        exact Nat.pow_pos (by decide : (0 : ℕ) < 2)
      have hsum_pos :
          0 < ∑ w : Fin n, resetFuelContribution (C' w).1 := by
        refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ?_
        exact ⟨r, Finset.mem_univ r, hcontrib_pos⟩
      have hf_pos : 0 < resetFuel C' := by
        unfold resetFuel
        omega
      omega
  | succ k ih =>
      intro C' hF hSome hNot
      obtain ⟨r, hr_res⟩ := hSome
      push_neg at hNot
      obtain ⟨v, hv_not⟩ := hNot
      have hrv : r ≠ v := fun heq => by
        subst heq
        exact hv_not hr_res
      let C₁ : Config (AgentState n) Opinion n := C'.step P r v
      have dispatch_after_step :
          resetFuel C₁ < resetFuel C' →
          ∃ (γ : DetScheduler n) (t : ℕ),
            InSrank (execution P C₁ γ t) ∧
            ((∀ μ : Fin n,
              (execution P C₁ γ t μ).1.rank.val + 1 = ceilHalf n →
              2 ≤ (execution P C₁ γ t μ).1.timer) ∨
             IsConsensusConfig (execution P C₁ γ t)) := by
        intro h_dec
        have hF1 : resetFuel C₁ ≤ k := by omega
        by_cases hAllRes : ∀ w, (C₁ w).1.role = .Resetting
        · simpa [P] using
            ranking_from_all_resetting_log
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 hDmax1 hRlog C₁ hAllRes
        · by_cases hNoRes : ∀ w, (C₁ w).1.role ≠ .Resetting
          · simpa [P] using
              ranking_of_no_reset_by_parity_log
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                hn4 hDmax1 hRlog C₁ hNoRes
          · have hSomeC1 : ∃ r' : Fin n, (C₁ r').1.role = .Resetting := by
              push_neg at hNoRes
              exact hNoRes
            exact ih C₁ hF1 hSomeC1 hAllRes
      by_cases hr_rc : (C' r).1.resetcount = 0
      · cases hr_leader : (C' r).1.leader with
        | F =>
            have h_dec :=
              dormant_follower_step_resetFuel_lt
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                hrv hr_res hr_rc hr_leader hv_not
            have h_dec' : resetFuel C₁ < resetFuel C' := by
              simpa [C₁, P] using h_dec
            obtain ⟨γ, t, hgoal⟩ := dispatch_after_step h_dec'
            exact
              ranking_goal_of_step_ranking_goal
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C') (u := r) (v := v)
                (by simpa [C₁, P] using ⟨γ, t, hgoal⟩)
        | L =>
            rcases
              dormant_leader_nonresetting_step_resetFuel_lt_or_seed
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                hrv hr_res hr_rc hr_leader hv_not
              with h_dec | ⟨r_seed, hseed_res, hseed_rc, hseed_L⟩
            · have h_dec' : resetFuel C₁ < resetFuel C' := by
                simpa [C₁, P] using h_dec
              obtain ⟨γ, t, hgoal⟩ := dispatch_after_step h_dec'
              exact
                ranking_goal_of_step_ranking_goal
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  (C := C') (u := r) (v := v)
                  (by simpa [C₁, P] using ⟨γ, t, hgoal⟩)
            · have hReset :
                  ∃ q : Fin n, (C₁ q).1.role = .Resetting ∧
                    Rmax ≤ (C₁ q).1.resetcount ∧ (C₁ q).1.leader = .L := by
                refine ⟨r_seed, ?_, ?_, ?_⟩
                · simpa [C₁, P] using hseed_res
                · have hrc : (C₁ r_seed).1.resetcount = Rmax := by
                    simpa [C₁, P] using hseed_rc
                  rw [hrc]
                · simpa [C₁, P] using hseed_L
              obtain ⟨Ltail, hEndpoint⟩ :=
                reset_snapshot_to_RankingEndpoint_log
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hn4 hDmax1 hRlog C₁ hReset
              have hgoal₁ :=
                ranking_goal_of_runPairs_RankingEndpoint
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  (C := C₁) (L := Ltail) hEndpoint
              exact
                ranking_goal_of_step_ranking_goal
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  (C := C') (u := r) (v := v)
                  (by simpa [C₁, P] using hgoal₁)
      · have hr_rc_pos : 0 < (C' r).1.resetcount := Nat.pos_of_ne_zero hr_rc
        have h_dec :=
          propagate_reset_step_resetFuel_lt
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax1 C' hrv hr_res hr_rc_pos hv_not
        have h_dec' : resetFuel C₁ < resetFuel C' := by
          simpa [C₁, P] using h_dec
        obtain ⟨γ, t, hgoal⟩ := dispatch_after_step h_dec'
        exact
          ranking_goal_of_step_ranking_goal
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C') (u := r) (v := v)
            (by simpa [C₁, P] using ⟨γ, t, hgoal⟩)

theorem resetting_exists_to_ranking_goal_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hReset : ∃ r : Fin n, (C r).1.role = .Resetting) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  by_cases hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting
  · exact
      ranking_from_all_resetting_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C hAllReset
  · exact
      partial_resetting_to_ranking_goal_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C hReset hAllReset

theorem ranking_field_proof_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  by_cases hReset : ∃ r : Fin n, (C r).1.role = .Resetting
  · exact
      resetting_exists_to_ranking_goal_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C hReset
  · have hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting := by
      intro w hw
      exact hReset ⟨w, hw⟩
    exact
      ranking_of_no_reset_by_parity_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C hNoReset

set_option maxHeartbeats 8000000 in
-- The log-regime replacement for the old positive-resetcount re-entry:
-- strong seed -> fresh uniform unique endpoint -> ranking -> swap.
theorem correct_reset_seed_strong_to_InSswap_ResAns_phi_zero_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax) (hRmax_pos : 0 < Rmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeedStrong Rmax C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      let E := execution
        (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t
      InSswap E ∧ ResAns (majorityAnswer E) E ∧ phiCount E = 0 := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  rcases hSeed with ⟨⟨r, hr_role, hr_rc, hr_L, _hr_ans⟩, hAllResetAns⟩
  have hAllAns : ∀ w : Fin n, (C w).1.role = .Resetting →
      (C w).1.answer = majorityAnswer C := by
    intro w hw
    exact (hAllResetAns w hw).2
  obtain ⟨L0, hFresh0, hRes0, hNoPhi0, hMaj0⟩ :=
    log_seed_uniform_leader_to_FreshRankingStart_resAns_noPhi_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (m₀ := majorityAnswer C)
      hn4 hDmax1 hRmax_pos C r hr_role
      (by simpa [hr_rc] using hRlog) hr_L rfl hAllAns
  let C1 : Config (AgentState n) Opinion n := runPairs P C L0
  have hFresh1 : FreshRankingStart C1 := by
    simpa [C1, hP] using hFresh0
  have hRes1 : ResAns (majorityAnswer C) C1 := by
    simpa [C1, hP] using hRes0
  have hNoPhi1 : ∀ w : Fin n, (C1 w).1.answer ≠ .phi := by
    simpa [C1, hP] using hNoPhi0
  have hMaj1 : majorityAnswer C1 = majorityAnswer C := by
    simpa [C1, hP] using hMaj0
  have hm1 : majorityAnswer C = majorityAnswer C1 := hMaj1.symm
  obtain ⟨L1, hSrank1, hResRank, hNoPhiRank, hTimerRank, hMajRank⟩ :=
    fresh_start_to_InSrank_ResAns_by_parity_BCF
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C1 (majorityAnswer C) hm1 hFresh1 hRes1 hNoPhi1
  let C2 : Config (AgentState n) Opinion n := runPairs P C1 L1
  have hSrank2 : InSrank C2 := by
    simpa [C2, hP] using hSrank1
  have hRes2 : ResAns (majorityAnswer C) C2 := by
    simpa [C2, hP] using hResRank
  have hNoPhi2 : ∀ w : Fin n, (C2 w).1.answer ≠ .phi := by
    simpa [C2, hP] using hNoPhiRank
  have hTimer2 :
      ∀ μ : Fin n, (C2 μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (C2 μ).1.timer := by
    simpa [C2, hP] using hTimerRank
  have hMaj2 : majorityAnswer C2 = majorityAnswer C1 := by
    simpa [C2, hP] using hMajRank
  have hm2 : majorityAnswer C = majorityAnswer C2 := by
    rw [hMaj2, hMaj1]
  obtain ⟨L2, hSswap2, hResSwap, hNoPhiSwap, hMajSwap⟩ :=
    InSrank_to_InSswap_ResAns_with_inv
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (m₀ := majorityAnswer C) hn4 hSrank2 hRes2 hNoPhi2 hm2 hTimer2
  let E : Config (AgentState n) Opinion n := runPairs P C2 L2
  have hSswapE : InSswap E := by
    simpa [E, hP] using hSswap2
  have hResE0 : ResAns (majorityAnswer C) E := by
    simpa [E, hP] using hResSwap
  have hNoPhiE : ∀ w : Fin n, (E w).1.answer ≠ .phi := by
    simpa [E, hP] using hNoPhiSwap
  have hMajE_to_C2 : majorityAnswer E = majorityAnswer C2 := by
    simpa [E, hP] using hMajSwap
  exact
    exists_schedule_after_runPairs
      (Goal := fun E =>
        InSswap E ∧ ResAns (majorityAnswer E) E ∧ phiCount E = 0)
      P C (L0 ++ L1 ++ L2) ⟨fun _ => default, 0, by
        have hRun : runPairs P C (L0 ++ L1 ++ L2) = E := by
          simp [runPairs_append, C1, C2, E, hP]
        rw [hRun]
        simp only [execution]
        refine ⟨hSswapE, ?_, ?_⟩
        · have hMajE : majorityAnswer E = majorityAnswer C := by
            rw [hMajE_to_C2, hMaj2, hMaj1]
          rw [hMajE]
          exact hResE0
        · exact (phiCount_eq_zero_iff E).mpr hNoPhiE⟩

/-- Log-regime strong version of the entry seed-prefix obligation. -/
def MedCorrectLiveProducesStrongSeedOrProgress
    [Inhabited (Fin n × Fin n)]
    (Rmax Emax Dmax : ℕ) (hn : 0 < n) : Prop :=
  ∀ D : Config (AgentState n) Opinion n,
    InSswap D →
    (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
      1 ≤ (D μ).1.timer) →
    0 < wrongAnswerCount D →
    (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
      (D μ).1.answer = majorityAnswer D) →
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs
        (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) D L
      CorrectResetSeedStrong Rmax C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C')

/-- Log-regime strong version of the reset-leaf seed-prefix obligation. -/
def ReservoirCaseProducesStrongSeedOrProgress
    [Inhabited (Fin n × Fin n)]
    (Rmax Emax Dmax : ℕ) (hn : 0 < n) : Prop :=
  ∀ D : Config (AgentState n) Opinion n,
    InSswap D →
    ResAns (majorityAnswer D) D →
    0 < phiCount D →
    ((∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
        (D μ).1.answer = majorityAnswer D) ∨
     (∃ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n ∧
        (D μ).1.timer = 0)) →
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs
        (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) D L
      CorrectResetSeedStrong Rmax C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C' ∧
          phiCount C' < phiCount D)

theorem correctResetSeedStrong_of_odd_timer_one_max_no_swap_diff
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have hsnap :=
    trigger_reset_from_InSrank_timer_one_max_no_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC.toInSrank hn4 hμv hμ_med hv_max h_timer
      h_no_swap hpar h_post_diff
  have htr :=
    propagation_reset_fires_no_swap_max_timer_one_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC.toInSrank hn4 hμv hμ_med hv_max h_timer
      h_no_swap hpar h_post_diff
  have hmaj_step : majorityAnswer C' = majorityAnswer C := by
    dsimp [C', P]
    exact majorityAnswer_step_eq C μ v
  have hμ_majority : opinionToAnswer (C μ).2 = majorityAnswer C :=
    opinionToAnswer_median_eq_majorityAnswer_odd hC hμ_med hpar
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_ans' : (C' μ).1.answer = majorityAnswer C' := by
    rw [hmaj_step]
    dsimp [C']
    rw [congrArg AgentState.answer hfst]
    change (transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.answer =
      majorityAnswer C
    rw [htr, hμ_majority]
  have hv_ans' : (C' v).1.answer = majorityAnswer C' := by
    rw [hmaj_step]
    dsimp [C']
    rw [congrArg AgentState.answer hsnd]
    change (transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.answer =
      majorityAnswer C
    rw [htr, hμ_majority]
  obtain ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, _hv_leader, _hAll⟩ :=
    hsnap
  refine ⟨[(μ, v)], ?_⟩
  have hRun : runPairs P C [(μ, v)] = C' := by
    simp only [runPairs_cons, runPairs_nil, C']
  rw [hRun]
  exact
    CorrectResetSeedStrong_of_step_pair
      (P := P) hRmax_pos hC.toInSrank hμv
      (by simpa [C'] using hμ_role)
      (by simpa [C'] using hμ_rc)
      (by simpa [C'] using hμ_leader)
      (by simpa [C'] using hμ_ans')
      (by simpa [C'] using hv_role)
      (by simpa [C'] using hv_rc)
      (by simpa [C'] using hv_ans')

theorem correctResetSeedStrong_of_even_lower_timer_one_max_wrong
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hv_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hC.swap_condition_false μ v
  have h_post_diff : (C μ).1.answer ≠ (C v).1.answer := by
    intro hsame
    exact hv_wrong (by rw [← hsame, hμ_correct])
  have hsnap :=
    trigger_reset_from_InSrank_even_lower_timer_one_max_no_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hC.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer
      h_no_swap h_post_diff
  have htr :=
    propagation_reset_fires_even_lower_timer_one_max_no_swap_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer
      h_no_swap h_post_diff
  have hmaj_step : majorityAnswer C' = majorityAnswer C := by
    dsimp [C', P]
    exact majorityAnswer_step_eq C μ v
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_ans' : (C' μ).1.answer = majorityAnswer C' := by
    rw [hmaj_step]
    dsimp [C']
    rw [congrArg AgentState.answer hfst]
    change (transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.answer =
      majorityAnswer C
    rw [htr, hμ_correct]
  have hv_ans' : (C' v).1.answer = majorityAnswer C' := by
    rw [hmaj_step]
    dsimp [C']
    rw [congrArg AgentState.answer hsnd]
    change (transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.answer =
      majorityAnswer C
    rw [htr, hμ_correct]
  obtain ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, _hv_leader, _hAll⟩ :=
    hsnap
  refine ⟨[(μ, v)], ?_⟩
  have hRun : runPairs P C [(μ, v)] = C' := by
    simp only [runPairs_cons, runPairs_nil, C']
  rw [hRun]
  exact
    CorrectResetSeedStrong_of_step_pair
      (P := P) hRmax_pos hC.toInSrank hμv
      (by simpa [C'] using hμ_role)
      (by simpa [C'] using hμ_rc)
      (by simpa [C'] using hμ_leader)
      (by simpa [C'] using hμ_ans')
      (by simpa [C'] using hv_role)
      (by simpa [C'] using hv_rc)
      (by simpa [C'] using hv_ans')

theorem correctResetSeedStrong_of_timer_zero_wrong_nonupper
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (_hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 0)
    (hμ_ans : (C μ).1.answer = majorityAnswer C)
    (h_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have hmaj_step : majorityAnswer C' = majorityAnswer C := by
    dsimp [C', P]
    exact majorityAnswer_step_eq C μ v
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  by_cases hpar : n % 2 = 0
  · have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
    have hμ_lower : (C μ).1.rank.val + 1 = n / 2 := by
      rwa [hceil] at hμ_med
    have hv_not_lower : (C v).1.rank.val + 1 ≠ n / 2 := by
      rwa [← hceil]
    have h_no_swap :
        ¬((C μ).1.rank < (C v).1.rank ∧
          (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
      hC.swap_condition_false μ v
    have h_post_diff : (C μ).1.answer ≠ (C v).1.answer := by
      intro hsame
      exact h_wrong (by rw [← hsame, hμ_ans])
    have hsnap :=
      trigger_reset_from_InSrank_even_lower_timer_zero_no_swap_with_snapshot
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hC.toInSrank hμv hpar hμ_lower hv_not_lower hv_no_upper h_timer
        h_no_swap h_post_diff
    have htr :=
      propagation_reset_fires_even_lower_timer_zero_no_swap_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        (hRank := rankDeltaOSSR_satisfies_fix)
        (C := C) hC.toInSrank hμv hpar hμ_lower hv_not_lower hv_no_upper
        h_timer h_no_swap h_post_diff
    have hμ_ans' : (C' μ).1.answer = majorityAnswer C' := by
      rw [hmaj_step]
      dsimp [C']
      rw [congrArg AgentState.answer hfst]
      change (transitionPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.answer =
        majorityAnswer C
      rw [htr, hμ_ans]
    have hv_ans' : (C' v).1.answer = majorityAnswer C' := by
      rw [hmaj_step]
      dsimp [C']
      rw [congrArg AgentState.answer hsnd]
      change (transitionPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.answer =
        majorityAnswer C
      rw [htr, hμ_ans]
    obtain ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, _hv_leader, _hAll⟩ :=
      hsnap
    refine ⟨[(μ, v)], ?_⟩
    have hRun : runPairs P C [(μ, v)] = C' := by
      simp only [runPairs_cons, runPairs_nil, C']
    rw [hRun]
    exact
      CorrectResetSeedStrong_of_step_pair
        (P := P) hRmax_pos hC.toInSrank hμv
        (by simpa [C'] using hμ_role)
        (by simpa [C'] using hμ_rc)
        (by simpa [C'] using hμ_leader)
        (by simpa [C'] using hμ_ans')
        (by simpa [C'] using hv_role)
        (by simpa [C'] using hv_rc)
        (by simpa [C'] using hv_ans')
  · have h_no_swap :
        ¬((C μ).1.rank < (C v).1.rank ∧
          (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
      hC.swap_condition_false μ v
    have hμ_majority : opinionToAnswer (C μ).2 = majorityAnswer C :=
      opinionToAnswer_median_eq_majorityAnswer_odd hC hμ_med hpar
    have h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer := by
      rw [hμ_majority]
      exact h_wrong.symm
    have hsnap :=
      trigger_reset_from_InSrank_timer_zero_no_swap_with_snapshot
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) hC.toInSrank hμv hμ_med hv_no_med h_timer h_no_swap
        hpar h_post_diff
    have htr :=
      propagation_reset_fires_no_swap_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        (hRank := rankDeltaOSSR_satisfies_fix)
        (C := C) hC.toInSrank hμv hμ_med hv_no_med h_timer
        h_no_swap hpar h_post_diff
    have hμ_ans' : (C' μ).1.answer = majorityAnswer C' := by
      rw [hmaj_step]
      dsimp [C']
      rw [congrArg AgentState.answer hfst]
      change (transitionPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.answer =
        majorityAnswer C
      rw [htr, hμ_majority]
    have hv_ans' : (C' v).1.answer = majorityAnswer C' := by
      rw [hmaj_step]
      dsimp [C']
      rw [congrArg AgentState.answer hsnd]
      change (transitionPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.answer =
        majorityAnswer C
      rw [htr, hμ_majority]
    obtain ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, _hv_leader, _hAll⟩ :=
      hsnap
    refine ⟨[(μ, v)], ?_⟩
    have hRun : runPairs P C [(μ, v)] = C' := by
      simp only [runPairs_cons, runPairs_nil, C']
    rw [hRun]
    exact
      CorrectResetSeedStrong_of_step_pair
        (P := P) hRmax_pos hC.toInSrank hμv
        (by simpa [C'] using hμ_role)
        (by simpa [C'] using hμ_rc)
        (by simpa [C'] using hμ_leader)
        (by simpa [C'] using hμ_ans')
        (by simpa [C'] using hv_role)
        (by simpa [C'] using hv_rc)
        (by simpa [C'] using hv_ans')

theorem correctResetSeedStrong_of_timer_zero_wrong_nonexceptional
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 0)
    (hμ_ans : (C μ).1.answer = majorityAnswer C)
    (h_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' :=
  correctResetSeedStrong_of_timer_zero_wrong_nonupper
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hn4 hRmax_pos hC hμv hμ_med hv_no_med hv_no_upper h_timer
    hμ_ans h_wrong

theorem correctResetSeedStrong_of_odd_timer_zero_wrong_nonmedian
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hC.swap_condition_false μ v
  have hμ_majority : opinionToAnswer (C μ).2 = majorityAnswer C :=
    opinionToAnswer_median_eq_majorityAnswer_odd hC hμ_med hpar
  have h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer := by
    rw [hμ_majority]
    exact h_wrong.symm
  have hsnap :=
    trigger_reset_from_InSrank_timer_zero_no_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC.toInSrank hμv hμ_med hv_no_med h_timer h_no_swap
      hpar h_post_diff
  have htr :=
    propagation_reset_fires_no_swap_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC.toInSrank hμv hμ_med hv_no_med h_timer
      h_no_swap hpar h_post_diff
  have hmaj_step : majorityAnswer C' = majorityAnswer C := by
    dsimp [C', P]
    exact majorityAnswer_step_eq C μ v
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_ans' : (C' μ).1.answer = majorityAnswer C' := by
    rw [hmaj_step]
    dsimp [C']
    rw [congrArg AgentState.answer hfst]
    change (transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.answer =
      majorityAnswer C
    rw [htr, hμ_majority]
  have hv_ans' : (C' v).1.answer = majorityAnswer C' := by
    rw [hmaj_step]
    dsimp [C']
    rw [congrArg AgentState.answer hsnd]
    change (transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.answer =
      majorityAnswer C
    rw [htr, hμ_majority]
  obtain ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, _hv_leader, _hAll⟩ :=
    hsnap
  refine ⟨[(μ, v)], ?_⟩
  have hRun : runPairs P C [(μ, v)] = C' := by
    simp only [runPairs_cons, runPairs_nil, C']
  rw [hRun]
  exact
    CorrectResetSeedStrong_of_step_pair
      (P := P) hRmax_pos hC.toInSrank hμv
      (by simpa [C'] using hμ_role)
      (by simpa [C'] using hμ_rc)
      (by simpa [C'] using hμ_leader)
      (by simpa [C'] using hμ_ans')
      (by simpa [C'] using hv_role)
      (by simpa [C'] using hv_rc)
      (by simpa [C'] using hv_ans')

theorem correctResetSeedStrong_of_odd_timer_one_max_same_then_zero_wrong_nonmedian
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ v w : Fin n} (hμv : μ ≠ v) (hμw : μ ≠ w) (hwv : w ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hw_no_med : (C w).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 1)
    (h_post_same : opinionToAnswer (C μ).2 = (C v).1.answer)
    (hw_wrong : (C w).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P μ v
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hC.swap_condition_false μ v
  obtain ⟨hS₁, htimer₁, _hans₁, hmed₁, _hvmax₁, hothers₁, _hinputs₁⟩ :=
    step_at_median_max_timer_one_no_reset_explicit
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      rankDeltaOSSR_satisfies_fix hC hn4 hμv hμ_med hv_max hpar
      h_no_swap h_timer h_post_same
  have hmaj₁ : majorityAnswer C₁ = majorityAnswer C := by
    simpa [C₁, P] using
      (majorityAnswer_step_eq
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  have hw_no_med₁ : (C₁ w).1.rank.val + 1 ≠ ceilHalf n := by
    rw [show C₁ w = C w from hothers₁ w hμw.symm hwv]
    exact hw_no_med
  have hw_wrong₁ : (C₁ w).1.answer ≠ majorityAnswer C₁ := by
    rw [show C₁ w = C w from hothers₁ w hμw.symm hwv, hmaj₁]
    exact hw_wrong
  obtain ⟨Ltail, hSeedTail⟩ :=
    correctResetSeedStrong_of_odd_timer_zero_wrong_nonmedian
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hRmax_pos hS₁ hμw hpar hmed₁ hw_no_med₁ htimer₁ hw_wrong₁
  refine ⟨(μ, v) :: Ltail, ?_⟩
  change
    let C' := runPairs P (C.step P μ v) Ltail
    CorrectResetSeedStrong Rmax C'
  exact hSeedTail

theorem correctResetSeedStrong_of_even_lower_timer_one_same_then_zero_wrong_nonupper
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (hpar : n % 2 = 0)
    {μ v w : Fin n} (hμv : μ ≠ v) (hμw : μ ≠ w) (hwv : w ≠ v)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hw_not_upper : (C w).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 1)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hv_correct : (C v).1.answer = majorityAnswer C)
    (hw_wrong : (C w).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P μ v
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hC.swap_condition_false μ v
  have h_same : (C μ).1.answer = (C v).1.answer := by
    rw [hμ_correct, hv_correct]
  obtain ⟨_hμ_state, _hv_state, hothers⟩ :=
    no_reset_even_lower_max_timer_one_step_state
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hC.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_same
  have hC₁_pack :=
    insswap_drain_median_timer_one_step
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hC hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_same
  have hC₁_swap : InSswap C₁ := by
    simpa [C₁, P] using hC₁_pack.1
  have hμ_timer₁ : (C₁ μ).1.timer = 0 := by
    simpa [C₁, P] using hC₁_pack.2.1
  have hμ_lower₁ : (C₁ μ).1.rank.val + 1 = n / 2 := by
    simpa [C₁, P] using hC₁_pack.2.2.2
  have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
  have hμ_med₁ : (C₁ μ).1.rank.val + 1 = ceilHalf n := by
    rw [hceil]
    exact hμ_lower₁
  have hμ_correct₁ : (C₁ μ).1.answer = majorityAnswer C₁ := by
    have hmaj₁ : majorityAnswer C₁ = majorityAnswer C := by
      simpa [C₁, P] using
        (majorityAnswer_step_eq
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
    rw [hmaj₁]
    simpa [C₁, P] using hC₁_pack.2.2.1.trans hμ_correct
  have hw_state₁ : C₁ w = C w := by
    simpa [C₁, P] using hothers w hμw.symm hwv
  have hw_no_med₁ : (C₁ w).1.rank.val + 1 ≠ ceilHalf n := by
    rw [hw_state₁, hceil]
    intro hw_lower
    apply hμw
    apply hC.ranks_inj
    apply Fin.eq_of_val_eq
    have hμ_val : (C μ).1.rank.val = n / 2 - 1 := by omega
    have hw_val : (C w).1.rank.val = n / 2 - 1 := by omega
    exact hμ_val.trans hw_val.symm
  have hw_not_upper₁ : (C₁ w).1.rank.val + 1 ≠ n / 2 + 1 := by
    rw [hw_state₁]
    exact hw_not_upper
  have hw_wrong₁ : (C₁ w).1.answer ≠ majorityAnswer C₁ := by
    have hmaj₁ : majorityAnswer C₁ = majorityAnswer C := by
      simpa [C₁, P] using
        (majorityAnswer_step_eq
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
    rw [hw_state₁, hmaj₁]
    exact hw_wrong
  obtain ⟨Ltail, hSeedTail⟩ :=
    correctResetSeedStrong_of_timer_zero_wrong_nonupper
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax_pos hC₁_swap hμw hμ_med₁ hw_no_med₁ hw_not_upper₁
      hμ_timer₁ hμ_correct₁ hw_wrong₁
  refine ⟨(μ, v) :: Ltail, ?_⟩
  change
    let C' := runPairs P (C.step P μ v) Ltail
    CorrectResetSeedStrong Rmax C'
  exact hSeedTail

theorem correctResetSeedStrong_of_median_correct_timer_zero_wrong_nonexceptional
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ v : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 0)
    (hMedCorrect : ∀ η : Fin n, (C η).1.rank.val + 1 = ceilHalf n →
      (C η).1.answer = majorityAnswer C)
    (h_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' := by
  classical
  have hμv : μ ≠ v := by
    intro h
    subst v
    exact hv_no_med hμ_med
  exact
    correctResetSeedStrong_of_timer_zero_wrong_nonexceptional
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax_pos hC hμv hμ_med hv_no_med hv_no_upper h_timer
      (hMedCorrect μ hμ_med) h_wrong

theorem med_correct_timer_zero_strong_seed_or_wrong_exceptional
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (hpos : 0 < wrongAnswerCount C)
    (hMedCorrect : ∀ η : Fin n, (C η).1.rank.val + 1 = ceilHalf n →
      (C η).1.answer = majorityAnswer C) :
    (∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C') ∨
    (∃ v : Fin n,
      (C v).1.rank.val + 1 ≠ ceilHalf n ∧
      (C v).1.answer ≠ majorityAnswer C ∧
      (C v).1.rank.val + 1 = n / 2 + 1) := by
  classical
  obtain ⟨v, hv_no_med, hv_wrong⟩ :=
    exists_wrong_nonmedian_of_med_correct hpos hMedCorrect
  by_cases hv_upper : (C v).1.rank.val + 1 = n / 2 + 1
  · exact Or.inr ⟨v, hv_no_med, hv_wrong, hv_upper⟩
  · exact Or.inl
      (by
        have hμv : μ ≠ v := by
          intro h
          subst v
          exact hv_no_med hμ_med
        exact
          correctResetSeedStrong_of_timer_zero_wrong_nonupper
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hRmax_pos hC hμv hμ_med hv_no_med hv_upper h_timer
            (hMedCorrect μ hμ_med) hv_wrong)

theorem med_correct_live_timer_one_strong_seed_or_progress
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {D : Config (AgentState n) Opinion n}
    (hSswap : InSswap D)
    (hWrongPos : 0 < wrongAnswerCount D)
    (hMedCorrect : ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
      (D μ).1.answer = majorityAnswer D)
    {μ : Fin n}
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (D μ).1.timer = 1) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs
        (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) D L
      CorrectResetSeedStrong Rmax C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C') := by
  classical
  by_cases hpar : n % 2 = 0
  · have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
    have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
      rwa [hceil] at hμ_med
    by_cases hNonupperWrong :
        ∃ w : Fin n,
          (D w).1.answer ≠ majorityAnswer D ∧
          (D w).1.rank.val + 1 ≠ n / 2 + 1
    · obtain ⟨w, hw_wrong, hw_not_upper⟩ := hNonupperWrong
      obtain ⟨v, hμv, hv_max⟩ :=
        hSswap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
      by_cases hv_wrong : (D v).1.answer ≠ majorityAnswer D
      · obtain ⟨L, hSeed⟩ :=
          correctResetSeedStrong_of_even_lower_timer_one_max_wrong
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hRmax_pos hSswap hμv hpar hμ_lower hv_max h_timer
            (hMedCorrect μ hμ_med) hv_wrong
        exact ⟨L, Or.inl hSeed⟩
      · have hv_correct : (D v).1.answer = majorityAnswer D := not_not.mp hv_wrong
        have hμw : μ ≠ w := by
          intro h
          subst w
          exact hw_wrong (hMedCorrect μ hμ_med)
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hw_wrong hv_correct
        obtain ⟨L, hSeed⟩ :=
          correctResetSeedStrong_of_even_lower_timer_one_same_then_zero_wrong_nonupper
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hRmax_pos hSswap hpar hμv hμw hwv hμ_lower hv_max
            hw_not_upper h_timer (hMedCorrect μ hμ_med) hv_correct hw_wrong
        exact ⟨L, Or.inl hSeed⟩
    · push_neg at hNonupperWrong
      obtain ⟨w, hw_no_med, hw_wrong⟩ :=
        exists_wrong_nonmedian_of_med_correct hWrongPos hMedCorrect
      have hw_upper : (D w).1.rank.val + 1 = n / 2 + 1 :=
        hNonupperWrong w hw_wrong
      have hμw : μ ≠ w := by
        intro h
        subst w
        exact hw_no_med hμ_med
      obtain ⟨L, hProg⟩ :=
        even_upper_only_wrong_decision_InSswap_ResAns
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hSswap hμw hpar hμ_lower hw_upper hw_wrong hNonupperWrong
      exact ⟨L, Or.inr hProg⟩
  · obtain ⟨w, hw_no_med, hw_wrong⟩ :=
      exists_wrong_nonmedian_of_med_correct hWrongPos hMedCorrect
    obtain ⟨v, hμv, hv_max⟩ :=
      hSswap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
    have h_no_swap :
        ¬((D μ).1.rank < (D v).1.rank ∧
          (D μ).2 = Opinion.B ∧ (D v).2 = Opinion.A) :=
      hSswap.swap_condition_false μ v
    have hμ_input :
        opinionToAnswer (D μ).2 = majorityAnswer D :=
      opinionToAnswer_median_eq_majorityAnswer_odd hSswap hμ_med hpar
    by_cases hv_wrong : (D v).1.answer ≠ majorityAnswer D
    · have hpost :
          opinionToAnswer (D μ).2 ≠ (D v).1.answer := by
        rw [hμ_input]
        exact hv_wrong.symm
      obtain ⟨L, hSeed⟩ :=
        correctResetSeedStrong_of_odd_timer_one_max_no_swap_diff
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hSswap hμv hμ_med hv_max h_timer h_no_swap hpar hpost
      exact ⟨L, Or.inl hSeed⟩
    · have hv_correct : (D v).1.answer = majorityAnswer D := not_not.mp hv_wrong
      have hμw : μ ≠ w := by
        intro h
        subst w
        exact hw_no_med hμ_med
      have hwv : w ≠ v := by
        intro h
        subst w
        exact hw_wrong hv_correct
      have hpost :
          opinionToAnswer (D μ).2 = (D v).1.answer := by
        rw [hμ_input, hv_correct]
      obtain ⟨L, hSeed⟩ :=
        correctResetSeedStrong_of_odd_timer_one_max_same_then_zero_wrong_nonmedian
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hSswap hμv hμw hwv hpar hμ_med hv_max
          hw_no_med h_timer hpost hw_wrong
      exact ⟨L, Or.inl hSeed⟩

theorem medCorrectLiveProducesStrongSeedOrProgress_holds
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax) :
    MedCorrectLiveProducesStrongSeedOrProgress Rmax Emax Dmax hn := by
  classical
  intro D hSswap hTimer hWrongPos hMedCorrect
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨μ, hμ_rank⟩ :=
    hSswap.toInSrank.exists_at_rank
      (by omega : 0 < n) (⟨ceilHalf n - 1, by
        unfold ceilHalf
        omega⟩ : Fin n)
  have hμ_med : (D μ).1.rank.val + 1 = ceilHalf n := by
    have hv : (D μ).1.rank.val = ceilHalf n - 1 := by
      exact congrArg Fin.val hμ_rank
    have hceil_pos : 0 < ceilHalf n := by
      unfold ceilHalf
      omega
    omega
  by_cases htimer1 : (D μ).1.timer = 1
  · exact
      med_correct_live_timer_one_strong_seed_or_progress
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hRmax_pos hSswap hWrongPos hMedCorrect hμ_med htimer1
  · have htimer2 : 2 ≤ (D μ).1.timer := by
      have hpos := hTimer μ hμ_med
      omega
    obtain ⟨w, hw_no_med, hw_wrong⟩ :=
      exists_wrong_nonmedian_of_med_correct hWrongPos hMedCorrect
    have hμw : μ ≠ w := by
      intro h
      subst w
      exact hw_no_med hμ_med
    by_cases hpar : n % 2 = 0
    · have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
      have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
        rwa [hceil] at hμ_med
      obtain ⟨v, hμv, hv_max⟩ :=
        hSswap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
      have h_no_swap :
          ¬ ((D μ).1.rank < (D v).1.rank ∧
            (D μ).2 = Opinion.B ∧ (D v).2 = Opinion.A) :=
        hSswap.swap_condition_false μ v
      obtain ⟨γ, t, hS, ht, hlower, hvmax, hμans, hvstate, hinput, hothers⟩ :=
        even_lower_timer_descent_to_one_with_states
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
          rankDeltaOSSR_satisfies_fix hSswap hn4 hpar hμv hμ_lower hv_max
          h_no_swap htimer2
      obtain ⟨L0, hpack⟩ :=
        exists_runPairs_of_execution_bcf
          (P := P) (C := D)
          (Goal := fun Ct : Config (AgentState n) Opinion n =>
            InSswap Ct ∧
            (Ct μ).1.timer = 1 ∧
            (Ct μ).1.rank.val + 1 = n / 2 ∧
            (Ct v).1.rank.val + 1 = n ∧
            (Ct μ).1.answer = (D μ).1.answer ∧
            (Ct v).1 = (D v).1 ∧
            (Ct μ).2 = (D μ).2 ∧
            (∀ x : Fin n, x ≠ μ → x ≠ v → Ct x = D x))
          γ t ⟨hS, ht, hlower, hvmax, hμans, hvstate, hinput, hothers⟩
      set Ct : Config (AgentState n) Opinion n := runPairs P D L0 with hCt
      have hpack' :
          InSswap Ct ∧
          (Ct μ).1.timer = 1 ∧
          (Ct μ).1.rank.val + 1 = n / 2 ∧
          (Ct v).1.rank.val + 1 = n ∧
          (Ct μ).1.answer = (D μ).1.answer ∧
          (Ct v).1 = (D v).1 ∧
          (Ct μ).2 = (D μ).2 ∧
          (∀ x : Fin n, x ≠ μ → x ≠ v → Ct x = D x) := by
        simpa [Ct, hP] using hpack
      rcases hpack' with ⟨hCtS, hCtTimer, hCtLower, _hvmaxCt,
        hCtμAns, hCtvState, _hCtInput, hCtOthers⟩
      have hMajCt : majorityAnswer Ct = majorityAnswer D := by
        simpa [Ct, hP] using
          (majorityAnswer_runPairs_eq
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) D L0)
      have hCtMed : (Ct μ).1.rank.val + 1 = ceilHalf n := by
        rw [hceil]
        exact hCtLower
      have hCtMedCorrect :
          ∀ η : Fin n, (Ct η).1.rank.val + 1 = ceilHalf n →
            (Ct η).1.answer = majorityAnswer Ct := by
        intro η hη
        have hημ : η = μ := by
          apply hCtS.ranks_inj
          apply Fin.eq_of_val_eq
          have hηv : (Ct η).1.rank.val = ceilHalf n - 1 := by omega
          have hμv' : (Ct μ).1.rank.val = ceilHalf n - 1 := by omega
          exact hηv.trans hμv'.symm
        subst η
        rw [hCtμAns, hMajCt]
        exact hMedCorrect μ hμ_med
      have hCtWrongPos : 0 < wrongAnswerCount Ct := by
        have hw_wrong_Ct : (Ct w).1.answer ≠ majorityAnswer Ct := by
          rw [hMajCt]
          by_cases hwv : w = v
          · subst w
            rw [hCtvState]
            exact hw_wrong
          · rw [hCtOthers w hμw.symm hwv]
            exact hw_wrong
        unfold wrongAnswerCount
        exact Finset.card_pos.mpr ⟨w, by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ w, hw_wrong_Ct⟩⟩
      obtain ⟨Ltail, hTail⟩ :=
        med_correct_live_timer_one_strong_seed_or_progress
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hCtS hCtWrongPos hCtMedCorrect hCtMed hCtTimer
      refine ⟨L0 ++ Ltail, ?_⟩
      rw [runPairs_append]
      simpa [Ct, hP] using hTail
    · obtain ⟨v, hμv, hv_max⟩ :=
        hSswap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
      have h_no_swap :
          ¬ ((D μ).1.rank < (D v).1.rank ∧
            (D μ).2 = Opinion.B ∧ (D v).2 = Opinion.A) :=
        hSswap.swap_condition_false μ v
      obtain ⟨γ, t, hS, ht, hmedCt, hvmax, hμans, hvstate, hinput, hothers⟩ :=
        odd_timer_descent_to_one_explicit_with_states
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
          rankDeltaOSSR_satisfies_fix hSswap (by omega : 2 ≤ n) hpar hμv
          hμ_med hv_max h_no_swap htimer2
      obtain ⟨L0, hpack⟩ :=
        exists_runPairs_of_execution_bcf
          (P := P) (C := D)
          (Goal := fun Ct : Config (AgentState n) Opinion n =>
            InSswap Ct ∧
            (Ct μ).1.timer = 1 ∧
            (Ct μ).1.rank.val + 1 = ceilHalf n ∧
            (Ct v).1.rank.val + 1 = n ∧
            (Ct μ).1.answer = opinionToAnswer (D μ).2 ∧
            (Ct v).1 = (D v).1 ∧
            (Ct μ).2 = (D μ).2 ∧
            (∀ x : Fin n, x ≠ μ → x ≠ v → Ct x = D x))
          γ t ⟨hS, ht, hmedCt, hvmax, hμans, hvstate, hinput, hothers⟩
      set Ct : Config (AgentState n) Opinion n := runPairs P D L0 with hCt
      have hpack' :
          InSswap Ct ∧
          (Ct μ).1.timer = 1 ∧
          (Ct μ).1.rank.val + 1 = ceilHalf n ∧
          (Ct v).1.rank.val + 1 = n ∧
          (Ct μ).1.answer = opinionToAnswer (D μ).2 ∧
          (Ct v).1 = (D v).1 ∧
          (Ct μ).2 = (D μ).2 ∧
          (∀ x : Fin n, x ≠ μ → x ≠ v → Ct x = D x) := by
        simpa [Ct, hP] using hpack
      rcases hpack' with ⟨hCtS, hCtTimer, hCtMed, _hvmaxCt,
        hCtμAns, hCtvState, _hCtInput, hCtOthers⟩
      have hMajCt : majorityAnswer Ct = majorityAnswer D := by
        simpa [Ct, hP] using
          (majorityAnswer_runPairs_eq
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) D L0)
      have hμ_input :
          opinionToAnswer (D μ).2 = majorityAnswer D :=
        opinionToAnswer_median_eq_majorityAnswer_odd hSswap hμ_med hpar
      have hCtMedCorrect :
          ∀ η : Fin n, (Ct η).1.rank.val + 1 = ceilHalf n →
            (Ct η).1.answer = majorityAnswer Ct := by
        intro η hη
        have hημ : η = μ := by
          apply hCtS.ranks_inj
          apply Fin.eq_of_val_eq
          have hηv : (Ct η).1.rank.val = ceilHalf n - 1 := by omega
          have hμv' : (Ct μ).1.rank.val = ceilHalf n - 1 := by omega
          exact hηv.trans hμv'.symm
        subst η
        rw [hCtμAns, hμ_input, hMajCt]
      have hCtWrongPos : 0 < wrongAnswerCount Ct := by
        have hw_wrong_Ct : (Ct w).1.answer ≠ majorityAnswer Ct := by
          rw [hMajCt]
          by_cases hwv : w = v
          · subst w
            rw [hCtvState]
            exact hw_wrong
          · rw [hCtOthers w hμw.symm hwv]
            exact hw_wrong
        unfold wrongAnswerCount
        exact Finset.card_pos.mpr ⟨w, by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ w, hw_wrong_Ct⟩⟩
      obtain ⟨Ltail, hTail⟩ :=
        med_correct_live_timer_one_strong_seed_or_progress
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hCtS hCtWrongPos hCtMedCorrect hCtMed hCtTimer
      refine ⟨L0 ++ Ltail, ?_⟩
      rw [runPairs_append]
      simpa [Ct, hP] using hTail

theorem med_correct_live_timer_one_strong_seed_or_phi_progress
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {D : Config (AgentState n) Opinion n}
    (hSswap : InSswap D)
    (hRes : ResAns (majorityAnswer D) D)
    (hWrongPos : 0 < wrongAnswerCount D)
    (hMedCorrect : ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
      (D μ).1.answer = majorityAnswer D)
    {μ : Fin n}
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (D μ).1.timer = 1) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs
        (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) D L
      CorrectResetSeedStrong Rmax C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C' ∧
          phiCount C' < phiCount D) := by
  classical
  by_cases hpar : n % 2 = 0
  · have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
    have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
      rwa [hceil] at hμ_med
    by_cases hNonupperWrong :
        ∃ w : Fin n,
          (D w).1.answer ≠ majorityAnswer D ∧
          (D w).1.rank.val + 1 ≠ n / 2 + 1
    · obtain ⟨w, hw_wrong, hw_not_upper⟩ := hNonupperWrong
      obtain ⟨v, hμv, hv_max⟩ :=
        hSswap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
      by_cases hv_wrong : (D v).1.answer ≠ majorityAnswer D
      · obtain ⟨L, hSeed⟩ :=
          correctResetSeedStrong_of_even_lower_timer_one_max_wrong
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hRmax_pos hSswap hμv hpar hμ_lower hv_max h_timer
            (hMedCorrect μ hμ_med) hv_wrong
        exact ⟨L, Or.inl hSeed⟩
      · have hv_correct : (D v).1.answer = majorityAnswer D := not_not.mp hv_wrong
        have hμw : μ ≠ w := by
          intro h
          subst w
          exact hw_wrong (hMedCorrect μ hμ_med)
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hw_wrong hv_correct
        obtain ⟨L, hSeed⟩ :=
          correctResetSeedStrong_of_even_lower_timer_one_same_then_zero_wrong_nonupper
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hRmax_pos hSswap hpar hμv hμw hwv hμ_lower hv_max
            hw_not_upper h_timer (hMedCorrect μ hμ_med) hv_correct hw_wrong
        exact ⟨L, Or.inl hSeed⟩
    · push_neg at hNonupperWrong
      obtain ⟨w, hw_no_med, hw_wrong⟩ :=
        exists_wrong_nonmedian_of_med_correct hWrongPos hMedCorrect
      have hw_upper : (D w).1.rank.val + 1 = n / 2 + 1 :=
        hNonupperWrong w hw_wrong
      have hμw : μ ≠ w := by
        intro h
        subst w
        exact hw_no_med hμ_med
      obtain ⟨L, hProg⟩ :=
        even_upper_wrong_decision_resAns_phi_decrease
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hSswap hRes hμw hpar hμ_lower hw_upper hw_wrong
      exact ⟨L, Or.inr hProg⟩
  · obtain ⟨w, hw_no_med, hw_wrong⟩ :=
      exists_wrong_nonmedian_of_med_correct hWrongPos hMedCorrect
    obtain ⟨v, hμv, hv_max⟩ :=
      hSswap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
    have h_no_swap :
        ¬((D μ).1.rank < (D v).1.rank ∧
          (D μ).2 = Opinion.B ∧ (D v).2 = Opinion.A) :=
      hSswap.swap_condition_false μ v
    have hμ_input :
        opinionToAnswer (D μ).2 = majorityAnswer D :=
      opinionToAnswer_median_eq_majorityAnswer_odd hSswap hμ_med hpar
    by_cases hv_wrong : (D v).1.answer ≠ majorityAnswer D
    · have hpost :
          opinionToAnswer (D μ).2 ≠ (D v).1.answer := by
        rw [hμ_input]
        exact hv_wrong.symm
      obtain ⟨L, hSeed⟩ :=
        correctResetSeedStrong_of_odd_timer_one_max_no_swap_diff
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hSswap hμv hμ_med hv_max h_timer h_no_swap hpar hpost
      exact ⟨L, Or.inl hSeed⟩
    · have hv_correct : (D v).1.answer = majorityAnswer D := not_not.mp hv_wrong
      have hμw : μ ≠ w := by
        intro h
        subst w
        exact hw_no_med hμ_med
      have hwv : w ≠ v := by
        intro h
        subst w
        exact hw_wrong hv_correct
      have hpost :
          opinionToAnswer (D μ).2 = (D v).1.answer := by
        rw [hμ_input, hv_correct]
      obtain ⟨L, hSeed⟩ :=
        correctResetSeedStrong_of_odd_timer_one_max_same_then_zero_wrong_nonmedian
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hSswap hμv hμw hwv hpar hμ_med hv_max
          hw_no_med h_timer hpost hw_wrong
      exact ⟨L, Or.inl hSeed⟩

theorem med_correct_live_strong_seed_or_phi_progress
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {D : Config (AgentState n) Opinion n}
    (hSswap : InSswap D)
    (hRes : ResAns (majorityAnswer D) D)
    (hTimer : ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
      1 ≤ (D μ).1.timer)
    (hWrongPos : 0 < wrongAnswerCount D)
    (hMedCorrect : ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
      (D μ).1.answer = majorityAnswer D) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs
        (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) D L
      CorrectResetSeedStrong Rmax C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C' ∧
          phiCount C' < phiCount D) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨μ, hμ_rank⟩ :=
    hSswap.toInSrank.exists_at_rank
      (by omega : 0 < n) (⟨ceilHalf n - 1, by
        unfold ceilHalf
        omega⟩ : Fin n)
  have hμ_med : (D μ).1.rank.val + 1 = ceilHalf n := by
    have hv : (D μ).1.rank.val = ceilHalf n - 1 := by
      exact congrArg Fin.val hμ_rank
    have hceil_pos : 0 < ceilHalf n := by
      unfold ceilHalf
      omega
    omega
  by_cases htimer1 : (D μ).1.timer = 1
  · exact
      med_correct_live_timer_one_strong_seed_or_phi_progress
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hRmax_pos hSswap hRes hWrongPos hMedCorrect hμ_med htimer1
  · have htimer2 : 2 ≤ (D μ).1.timer := by
      have hpos := hTimer μ hμ_med
      omega
    obtain ⟨w, hw_no_med, hw_wrong⟩ :=
      exists_wrong_nonmedian_of_med_correct hWrongPos hMedCorrect
    have hμw : μ ≠ w := by
      intro h
      subst w
      exact hw_no_med hμ_med
    by_cases hpar : n % 2 = 0
    · have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
      have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
        rwa [hceil] at hμ_med
      obtain ⟨v, hμv, hv_max⟩ :=
        hSswap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
      have h_no_swap :
          ¬ ((D μ).1.rank < (D v).1.rank ∧
            (D μ).2 = Opinion.B ∧ (D v).2 = Opinion.A) :=
        hSswap.swap_condition_false μ v
      obtain ⟨γ, t, hS, ht, hlower, hvmax, hμans, hvstate, hinput, hothers⟩ :=
        even_lower_timer_descent_to_one_with_states
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
          rankDeltaOSSR_satisfies_fix hSswap hn4 hpar hμv hμ_lower hv_max
          h_no_swap htimer2
      obtain ⟨L0, hpack⟩ :=
        exists_runPairs_of_execution_bcf
          (P := P) (C := D)
          (Goal := fun Ct : Config (AgentState n) Opinion n =>
            InSswap Ct ∧
            (Ct μ).1.timer = 1 ∧
            (Ct μ).1.rank.val + 1 = n / 2 ∧
            (Ct v).1.rank.val + 1 = n ∧
            (Ct μ).1.answer = (D μ).1.answer ∧
            (Ct v).1 = (D v).1 ∧
            (Ct μ).2 = (D μ).2 ∧
            (∀ x : Fin n, x ≠ μ → x ≠ v → Ct x = D x))
          γ t ⟨hS, ht, hlower, hvmax, hμans, hvstate, hinput, hothers⟩
      set Ct : Config (AgentState n) Opinion n := runPairs P D L0 with hCt
      have hpack' :
          InSswap Ct ∧
          (Ct μ).1.timer = 1 ∧
          (Ct μ).1.rank.val + 1 = n / 2 ∧
          (Ct v).1.rank.val + 1 = n ∧
          (Ct μ).1.answer = (D μ).1.answer ∧
          (Ct v).1 = (D v).1 ∧
          (Ct μ).2 = (D μ).2 ∧
          (∀ x : Fin n, x ≠ μ → x ≠ v → Ct x = D x) := by
        simpa [Ct, hP] using hpack
      rcases hpack' with ⟨hCtS, hCtTimer, hCtLower, _hvmaxCt,
        hCtμAns, hCtvState, _hCtInput, hCtOthers⟩
      have hMajCt : majorityAnswer Ct = majorityAnswer D := by
        simpa [Ct, hP] using
          (majorityAnswer_runPairs_eq
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) D L0)
      have hAnsEq : ∀ x : Fin n, (Ct x).1.answer = (D x).1.answer := by
        intro x
        by_cases hxμ : x = μ
        · subst x
          exact hCtμAns
        · by_cases hxv : x = v
          · subst x
            exact congrArg AgentState.answer hCtvState
          · rw [hCtOthers x hxμ hxv]
      have hResCt : ResAns (majorityAnswer Ct) Ct := by
        rw [hMajCt]
        intro x
        rw [hAnsEq x]
        exact hRes x
      have hPhiCt : phiCount Ct = phiCount D := by
        unfold phiCount
        congr 1
        apply Finset.filter_congr
        intro x _
        rw [hAnsEq x]
      have hCtMed : (Ct μ).1.rank.val + 1 = ceilHalf n := by
        rw [hceil]
        exact hCtLower
      have hCtMedCorrect :
          ∀ η : Fin n, (Ct η).1.rank.val + 1 = ceilHalf n →
            (Ct η).1.answer = majorityAnswer Ct := by
        intro η hη
        have hημ : η = μ := by
          apply hCtS.ranks_inj
          apply Fin.eq_of_val_eq
          have hηv : (Ct η).1.rank.val = ceilHalf n - 1 := by omega
          have hμv' : (Ct μ).1.rank.val = ceilHalf n - 1 := by omega
          exact hηv.trans hμv'.symm
        subst η
        rw [hAnsEq μ, hMajCt]
        exact hMedCorrect μ hμ_med
      have hCtWrongPos : 0 < wrongAnswerCount Ct := by
        rw [← phiCount_eq_wrongAnswerCount_of_resAns hResCt, hPhiCt,
          phiCount_eq_wrongAnswerCount_of_resAns hRes]
        exact hWrongPos
      obtain ⟨Ltail, hTail⟩ :=
        med_correct_live_timer_one_strong_seed_or_phi_progress
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hCtS hResCt hCtWrongPos hCtMedCorrect
          hCtMed hCtTimer
      refine ⟨L0 ++ Ltail, ?_⟩
      rw [runPairs_append]
      have hTail' :
          CorrectResetSeedStrong Rmax (runPairs P Ct Ltail) ∨
            (InSswap (runPairs P Ct Ltail) ∧
              ResAns (majorityAnswer (runPairs P Ct Ltail)) (runPairs P Ct Ltail) ∧
              phiCount (runPairs P Ct Ltail) < phiCount Ct) := by
        simpa [Ct, hP] using hTail
      rcases hTail' with hSeed | hProg
      · exact Or.inl hSeed
      · rcases hProg with ⟨hI, hR, hlt⟩
        exact Or.inr ⟨hI, hR, by rwa [hPhiCt] at hlt⟩
    · obtain ⟨v, hμv, hv_max⟩ :=
        hSswap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
      have h_no_swap :
          ¬ ((D μ).1.rank < (D v).1.rank ∧
            (D μ).2 = Opinion.B ∧ (D v).2 = Opinion.A) :=
        hSswap.swap_condition_false μ v
      obtain ⟨γ, t, hS, ht, hmedCt, hvmax, hμans, hvstate, hinput, hothers⟩ :=
        odd_timer_descent_to_one_explicit_with_states
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
          rankDeltaOSSR_satisfies_fix hSswap (by omega : 2 ≤ n) hpar hμv
          hμ_med hv_max h_no_swap htimer2
      obtain ⟨L0, hpack⟩ :=
        exists_runPairs_of_execution_bcf
          (P := P) (C := D)
          (Goal := fun Ct : Config (AgentState n) Opinion n =>
            InSswap Ct ∧
            (Ct μ).1.timer = 1 ∧
            (Ct μ).1.rank.val + 1 = ceilHalf n ∧
            (Ct v).1.rank.val + 1 = n ∧
            (Ct μ).1.answer = opinionToAnswer (D μ).2 ∧
            (Ct v).1 = (D v).1 ∧
            (Ct μ).2 = (D μ).2 ∧
            (∀ x : Fin n, x ≠ μ → x ≠ v → Ct x = D x))
          γ t ⟨hS, ht, hmedCt, hvmax, hμans, hvstate, hinput, hothers⟩
      set Ct : Config (AgentState n) Opinion n := runPairs P D L0 with hCt
      have hpack' :
          InSswap Ct ∧
          (Ct μ).1.timer = 1 ∧
          (Ct μ).1.rank.val + 1 = ceilHalf n ∧
          (Ct v).1.rank.val + 1 = n ∧
          (Ct μ).1.answer = opinionToAnswer (D μ).2 ∧
          (Ct v).1 = (D v).1 ∧
          (Ct μ).2 = (D μ).2 ∧
          (∀ x : Fin n, x ≠ μ → x ≠ v → Ct x = D x) := by
        simpa [Ct, hP] using hpack
      rcases hpack' with ⟨hCtS, hCtTimer, hCtMed, _hvmaxCt,
        hCtμAns, hCtvState, _hCtInput, hCtOthers⟩
      have hMajCt : majorityAnswer Ct = majorityAnswer D := by
        simpa [Ct, hP] using
          (majorityAnswer_runPairs_eq
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) D L0)
      have hμ_input :
          opinionToAnswer (D μ).2 = majorityAnswer D :=
        opinionToAnswer_median_eq_majorityAnswer_odd hSswap hμ_med hpar
      have hAnsEq : ∀ x : Fin n, (Ct x).1.answer = (D x).1.answer := by
        intro x
        by_cases hxμ : x = μ
        · subst x
          rw [hCtμAns, hμ_input]
          exact (hMedCorrect μ hμ_med).symm
        · by_cases hxv : x = v
          · subst x
            exact congrArg AgentState.answer hCtvState
          · rw [hCtOthers x hxμ hxv]
      have hResCt : ResAns (majorityAnswer Ct) Ct := by
        rw [hMajCt]
        intro x
        rw [hAnsEq x]
        exact hRes x
      have hPhiCt : phiCount Ct = phiCount D := by
        unfold phiCount
        congr 1
        apply Finset.filter_congr
        intro x _
        rw [hAnsEq x]
      have hCtMedCorrect :
          ∀ η : Fin n, (Ct η).1.rank.val + 1 = ceilHalf n →
            (Ct η).1.answer = majorityAnswer Ct := by
        intro η hη
        have hημ : η = μ := by
          apply hCtS.ranks_inj
          apply Fin.eq_of_val_eq
          have hηv : (Ct η).1.rank.val = ceilHalf n - 1 := by omega
          have hμv' : (Ct μ).1.rank.val = ceilHalf n - 1 := by omega
          exact hηv.trans hμv'.symm
        subst η
        rw [hAnsEq μ, hMajCt]
        exact hMedCorrect μ hμ_med
      have hCtWrongPos : 0 < wrongAnswerCount Ct := by
        rw [← phiCount_eq_wrongAnswerCount_of_resAns hResCt, hPhiCt,
          phiCount_eq_wrongAnswerCount_of_resAns hRes]
        exact hWrongPos
      obtain ⟨Ltail, hTail⟩ :=
        med_correct_live_timer_one_strong_seed_or_phi_progress
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hCtS hResCt hCtWrongPos hCtMedCorrect
          hCtMed hCtTimer
      refine ⟨L0 ++ Ltail, ?_⟩
      rw [runPairs_append]
      have hTail' :
          CorrectResetSeedStrong Rmax (runPairs P Ct Ltail) ∨
            (InSswap (runPairs P Ct Ltail) ∧
              ResAns (majorityAnswer (runPairs P Ct Ltail)) (runPairs P Ct Ltail) ∧
              phiCount (runPairs P Ct Ltail) < phiCount Ct) := by
        simpa [Ct, hP] using hTail
      rcases hTail' with hSeed | hProg
      · exact Or.inl hSeed
      · rcases hProg with ⟨hI, hR, hlt⟩
        exact Or.inr ⟨hI, hR, by rwa [hPhiCt] at hlt⟩

theorem reservoir_med_correct_timer_zero_strong_seed_or_progress
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (hRes : ResAns (majorityAnswer C) C)
    (hPhiPos : 0 < phiCount C)
    {μ : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (hMedCorrect : ∀ η : Fin n, (C η).1.rank.val + 1 = ceilHalf n →
      (C η).1.answer = majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C' ∧
          phiCount C' < phiCount C) := by
  classical
  have hWrongPos : 0 < wrongAnswerCount C := by
    rw [← phiCount_eq_wrongAnswerCount_of_resAns hRes]
    exact hPhiPos
  rcases med_correct_timer_zero_strong_seed_or_wrong_exceptional
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax_pos hC hμ_med h_timer hWrongPos hMedCorrect with
    hSeed | hUpper
  · obtain ⟨L, hL⟩ := hSeed
    exact ⟨L, Or.inl hL⟩
  · obtain ⟨v, hv_no_med, hv_wrong, hv_upper⟩ := hUpper
    have hpar : n % 2 = 0 := by
      by_contra hodd
      have hceil : ceilHalf n = n / 2 + 1 := by
        unfold ceilHalf
        omega
      exact hv_no_med (by rw [hceil]; exact hv_upper)
    have hceil_even : ceilHalf n = n / 2 := by
      exact ceilHalf_eq_half_of_even hpar
    have hμ_lower : (C μ).1.rank.val + 1 = n / 2 := by
      rwa [hceil_even] at hμ_med
    have hμv : μ ≠ v := by
      intro h
      subst v
      exact hv_no_med hμ_med
    obtain ⟨L, hProg⟩ :=
      even_upper_wrong_decision_resAns_phi_decrease
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hC hRes hμv hpar hμ_lower hv_upper hv_wrong
    exact ⟨L, Or.inr hProg⟩

theorem reservoir_timer_zero_strong_seed_or_progress_core
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {D : Config (AgentState n) Opinion n}
    (hSswap : InSswap D)
    (hRes : ResAns (majorityAnswer D) D)
    (hPhi : 0 < phiCount D)
    {μ : Fin n}
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (hμ_timer : (D μ).1.timer = 0) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) D L
      CorrectResetSeedStrong Rmax C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C' ∧
          phiCount C' < phiCount D) := by
  classical
  by_cases hMedCorrect :
      ∀ η : Fin n, (D η).1.rank.val + 1 = ceilHalf n →
        (D η).1.answer = majorityAnswer D
  · exact
      reservoir_med_correct_timer_zero_strong_seed_or_progress
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hRmax_pos hSswap hRes hPhi hμ_med hμ_timer hMedCorrect
  · push_neg at hMedCorrect
    obtain ⟨η, hη_med, hη_wrong⟩ := hMedCorrect
    by_cases hpar : n % 2 = 0
    · have hceil_even : ceilHalf n = n / 2 := by
        exact ceilHalf_eq_half_of_even hpar
      have hη_lower : (D η).1.rank.val + 1 = n / 2 := by
        rwa [hceil_even] at hη_med
      obtain ⟨v, hv_rank⟩ :=
        hSswap.toInSrank.exists_at_rank
          (by omega : 0 < n) (⟨n / 2, by omega⟩ : Fin n)
      have hv_upper : (D v).1.rank.val + 1 = n / 2 + 1 := by
        rw [hv_rank]
      have hηv : η ≠ v := by
        intro h
        subst v
        omega
      obtain ⟨L, hProg⟩ :=
        even_median_pair_wrong_decision_resAns_phi_decrease
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hSswap hRes hηv hpar hη_lower hv_upper (Or.inl hη_wrong)
      exact ⟨L, Or.inr hProg⟩
    · have hη_eq_μ : η = μ := by
        apply hSswap.ranks_inj
        apply Fin.eq_of_val_eq
        have hη_val : (D η).1.rank.val = ceilHalf n - 1 := by omega
        have hμ_val : (D μ).1.rank.val = ceilHalf n - 1 := by omega
        exact hη_val.trans hμ_val.symm
      subst η
      by_cases hNonmedWrong :
          ∃ v : Fin n,
            (D v).1.rank.val + 1 ≠ ceilHalf n ∧
              (D v).1.answer ≠ majorityAnswer D
      · obtain ⟨v, hv_no_med, hv_wrong⟩ := hNonmedWrong
        have hμv : μ ≠ v := by
          intro h
          subst v
          exact hv_no_med hμ_med
        obtain ⟨L, hSeed⟩ :=
          correctResetSeedStrong_of_odd_timer_zero_wrong_nonmedian
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hRmax_pos hSswap hμv hpar hμ_med hv_no_med hμ_timer hv_wrong
        exact ⟨L, Or.inl hSeed⟩
      · push_neg at hNonmedWrong
        have hOnly : ∀ w : Fin n, w ≠ μ →
            (D w).1.answer = majorityAnswer D := by
          intro w hwμ
          exact hNonmedWrong w (by
            intro hw_med
            apply hwμ
            apply hSswap.ranks_inj
            apply Fin.eq_of_val_eq
            have hw_val : (D w).1.rank.val = ceilHalf n - 1 := by omega
            have hμ_val : (D μ).1.rank.val = ceilHalf n - 1 := by omega
            exact hw_val.trans hμ_val.symm)
        obtain ⟨L, hProg⟩ :=
          odd_timer_zero_only_median_wrong_resAns_phi_decrease
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hSswap hRes hPhi hpar hμ_med hμ_timer hOnly
        exact ⟨L, Or.inr hProg⟩

theorem reservoirCaseProducesStrongSeedOrProgress_holds
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax) :
    ReservoirCaseProducesStrongSeedOrProgress Rmax Emax Dmax hn := by
  classical
  intro D hSswap hRes hPhi hCase
  rcases hCase with hMedCorrect | hTimerZero
  · have hWrongPos : 0 < wrongAnswerCount D := by
      rw [← phiCount_eq_wrongAnswerCount_of_resAns hRes]
      exact hPhi
    by_cases hTimer :
        ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
          1 ≤ (D μ).1.timer
    · exact
        med_correct_live_strong_seed_or_phi_progress
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hSswap hRes hTimer hWrongPos hMedCorrect
    · push_neg at hTimer
      obtain ⟨μ, hμ_med, hμ_timer_lt⟩ := hTimer
      have hμ_timer : (D μ).1.timer = 0 := by omega
      exact
        reservoir_timer_zero_strong_seed_or_progress_core
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hSswap hRes hPhi hμ_med hμ_timer
  · obtain ⟨μ, hμ_med, hμ_timer⟩ := hTimerZero
    exact
      reservoir_timer_zero_strong_seed_or_progress_core
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hRmax_pos hSswap hRes hPhi hμ_med hμ_timer

set_option maxHeartbeats 8000000 in
-- Re-entry consumer with the strong seed disjunct routed through the log
-- fresh bridge instead of the old positive-resetcount path.
theorem med_correct_live_InSswap_to_reservoir_entry_from_strong_seed_and_reentry_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax) (hRmax_pos : 0 < Rmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (hSeedPrefix :
      MedCorrectLiveProducesStrongSeedOrProgress Rmax Emax Dmax hn) :
    MedCorrectLiveInSswapToReservoirEntry Rmax Emax Dmax hn := by
  classical
  intro D hSswap hTimer hWrongPos hMedCorrect
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨L0, hCase⟩ :=
    hSeedPrefix D hSswap hTimer hWrongPos hMedCorrect
  set C0 : Config (AgentState n) Opinion n := runPairs P D L0 with hC0def
  have hCase' :
      CorrectResetSeedStrong Rmax C0 ∨
      (InSswap C0 ∧ ResAns (majorityAnswer C0) C0) := by
    simpa [C0, hP] using hCase
  rcases hCase' with hSeed0 | hProg
  · obtain ⟨γ1, t1, hFinal⟩ :=
      correct_reset_seed_strong_to_InSswap_ResAns_phi_zero_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRmax_pos hRlog hSeed0
    exact
      exists_schedule_after_runPairs
        (Goal := fun E => InSswap E ∧ ResAns (majorityAnswer E) E)
        P D L0 ⟨γ1, t1, by
          rcases hFinal with ⟨hInSswap, hResFinal, _hPhiZero⟩
          exact ⟨hInSswap, hResFinal⟩⟩
  · exact
      exists_schedule_after_runPairs
        (Goal := fun E => InSswap E ∧ ResAns (majorityAnswer E) E)
        P D L0 ⟨fun _ => default, 0, hProg⟩

set_option maxHeartbeats 8000000 in
-- Reset-leaf consumer with the strong seed disjunct routed through the log
-- fresh bridge instead of the old positive-resetcount path.
theorem reservoir_reset_leaf_from_strong_seed_and_reentry_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax) (hRmax_pos : 0 < Rmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (hSeedPrefix :
      ReservoirCaseProducesStrongSeedOrProgress Rmax Emax Dmax hn) :
    ReservoirResetLeaf Rmax Emax Dmax hn := by
  classical
  intro D hSswap hRes hPhiPos hCase
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨L0, hCaseL⟩ :=
    hSeedPrefix D hSswap hRes hPhiPos hCase
  set C0 : Config (AgentState n) Opinion n := runPairs P D L0 with hC0def
  have hCaseL' :
      CorrectResetSeedStrong Rmax C0 ∨
      (InSswap C0 ∧ ResAns (majorityAnswer C0) C0 ∧
        phiCount C0 < phiCount D) := by
    simpa [C0, hP] using hCaseL
  rcases hCaseL' with hSeed0 | hProg
  · obtain ⟨γ1, t1, hFinal⟩ :=
      correct_reset_seed_strong_to_InSswap_ResAns_phi_zero_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRmax_pos hRlog hSeed0
    refine
      exists_schedule_after_runPairs
        (Goal := fun E =>
          (InSswap E ∧ ResAns (majorityAnswer E) E) ∧
          phiCount E < phiCount D)
        P D L0 ?_
    refine ⟨γ1, t1, ?_⟩
    rcases hFinal with ⟨hInSswap, hResFinal, hPhiZero⟩
    refine ⟨⟨hInSswap, hResFinal⟩, ?_⟩
    rw [hPhiZero]
    exact hPhiPos
  · exact
      exists_schedule_after_runPairs
        (Goal := fun E =>
          (InSswap E ∧ ResAns (majorityAnswer E) E) ∧
          phiCount E < phiCount D)
        P D L0 ⟨fun _ => default, 0, by
          rcases hProg with ⟨hI, hR, hPhi⟩
          exact ⟨⟨hI, hR⟩, hPhi⟩⟩

set_option maxHeartbeats 8000000 in
-- Wrapper composition is elaboration-heavy because both re-entry branches
-- retain the full scheduler/execution goal shape.
theorem hMedCorrectExit_from_log_reentry_and_strong_seed_prefixes
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hDmax1 : 1 < Dmax) (hRmax_pos : 0 < Rmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (hEntrySeed :
      MedCorrectLiveProducesStrongSeedOrProgress Rmax Emax Dmax hn)
    (hLeafSeed :
      ReservoirCaseProducesStrongSeedOrProgress Rmax Emax Dmax hn) :
    ∀ k : ℕ, ∀ D : Config (AgentState n) Opinion n,
      InSswap D →
      (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (D μ).1.timer) →
      0 < wrongAnswerCount D →
      (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
        (D μ).1.answer = majorityAnswer D) →
      wrongAnswerCount D ≤ k →
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig (execution (protocolPEM n Rmax Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) D γ t) := by
  exact
    hMedCorrectExit_from_reservoir_entry_and_reset_leaf
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4
      (med_correct_live_InSswap_to_reservoir_entry_from_strong_seed_and_reentry_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRmax_pos hRlog hEntrySeed)
      (reservoir_reset_leaf_from_strong_seed_and_reentry_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRmax_pos hRlog hLeafSeed)

set_option maxHeartbeats 16000000 in
theorem burmanConvergence_concrete_log_with_strong_seed_prefixes
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (hEntrySeed :
      MedCorrectLiveProducesStrongSeedOrProgress Rmax Emax Dmax hn)
    (hLeafSeed :
      ReservoirCaseProducesStrongSeedOrProgress Rmax Emax Dmax hn) :
    BurmanConvergence Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) where
  ranking := fun C₀ =>
    ranking_field_proof_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) hn4 hDmax1 hRlog C₀
  epidemic := fun C₀ _h_correct => by
    classical
    obtain ⟨γ₁, t₁, hInSrank, hdisj⟩ :=
      ranking_field_proof_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) hn4 hDmax1 hRlog C₀
    set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
    have hclose :
        ∀ E : Config (AgentState n) Opinion n,
          (∃ (γ : DetScheduler n) (t : ℕ),
            E = execution P C₀ γ t ∧ IsConsensusConfig E) →
          ∃ (γ : DetScheduler n) (t : ℕ),
            InSswap (execution P C₀ γ t) ∧
            (∀ w : Fin n,
              (execution P C₀ γ t w).1.answer = majorityAnswer C₀) ∧
            ((∀ μ : Fin n,
              (execution P C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
              1 ≤ (execution P C₀ γ t μ).1.timer) ∨
             IsConsensusConfig (execution P C₀ γ t)) := by
      rintro E ⟨γ, t, hEeq, hconsE⟩
      have hStim : InStim (execution P C₀ γ t) := by
        rw [← hEeq]; exact (InStim_iff_IsConsensusConfig _).mpr hconsE
      have hconsE' : IsConsensusConfig (execution P C₀ γ t) := by
        rw [← hEeq]; exact hconsE
      refine ⟨γ, t, hStim.toInSswap, ?_, Or.inr hconsE'⟩
      intro w
      have hmajγ : majorityAnswer (execution P C₀ γ t) = majorityAnswer C₀ :=
        majorityAnswer_execution_eq C₀ γ t
      have hw : (execution P C₀ γ t w).1.answer
          = majorityAnswer (execution P C₀ γ t) :=
        hconsE'.allAnswerCorrect w
      rw [hw, hmajγ]
    rcases hdisj with htimer | hcons
    · set E₁ : Config (AgentState n) Opinion n := execution P C₀ γ₁ t₁
        with hE₁def
      have hMedCorrectExit :
          ∀ k : ℕ, ∀ D : Config (AgentState n) Opinion n,
            InSswap D →
            (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
              1 ≤ (D μ).1.timer) →
            0 < wrongAnswerCount D →
            (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
              (D μ).1.answer = majorityAnswer D) →
            wrongAnswerCount D ≤ k →
            ∃ (γ : DetScheduler n) (t : ℕ),
              IsConsensusConfig (execution (protocolPEM n Rmax Rmax
                (rankDeltaOSSR Rmax Emax Dmax hn)) D γ t) := by
        exact
          hMedCorrectExit_from_log_reentry_and_strong_seed_prefixes
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hDmax1 (by omega : 0 < Rmax) hRlog hEntrySeed hLeafSeed
      have hbridge :
          ∃ (γ : DetScheduler n) (t : ℕ),
            IsConsensusConfig (execution P E₁ γ t) :=
        epidemic_timer_branch_to_consensus
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 (C₁ := E₁)
          (by simpa [E₁, hP] using hInSrank)
          (by
            intro μ hμ
            have h2 := htimer μ (by simpa [E₁, hP] using hμ)
            omega)
          (by simpa [hP] using hMedCorrectExit)
      obtain ⟨γ₂, t₂, hcons₂⟩ := hbridge
      refine hclose (execution P E₁ γ₂ t₂) ⟨concatScheduler γ₁ t₁ γ₂,
        t₁ + t₂, ?_, hcons₂⟩
      rw [hE₁def, execution_concat]
    · exact hclose (execution P C₀ γ₁ t₁) ⟨γ₁, t₁, rfl, hcons⟩

theorem P_EM_solves_SSEM_log_with_strong_seed_prefixes
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (hEntrySeed :
      MedCorrectLiveProducesStrongSeedOrProgress Rmax Emax Dmax hn)
    (hLeafSeed :
      ReservoirCaseProducesStrongSeedOrProgress Rmax Emax Dmax hn) :
    SolvesSSEM (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) n :=
  P_EM_solves_SSEM_from_BurmanConvergence_only
    rankDeltaOSSR_satisfies_fix
    hn4
    (burmanConvergence_concrete_log_with_strong_seed_prefixes
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog hEntrySeed hLeafSeed)

theorem burmanConvergence_concrete_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax) :
    BurmanConvergence Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) :=
  burmanConvergence_concrete_log_with_strong_seed_prefixes
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hn4 hDmax1 hRlog
    (medCorrectLiveProducesStrongSeedOrProgress_holds
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 (by omega : 0 < Rmax))
    (reservoirCaseProducesStrongSeedOrProgress_holds
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 (by omega : 0 < Rmax))

theorem P_EM_solves_SSEM_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax) :
    SolvesSSEM (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) n :=
  P_EM_solves_SSEM_log_with_strong_seed_prefixes
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hn4 hDmax1 hRlog
    (medCorrectLiveProducesStrongSeedOrProgress_holds
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 (by omega : 0 < Rmax))
    (reservoirCaseProducesStrongSeedOrProgress_holds
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 (by omega : 0 < Rmax))

end SSEM
