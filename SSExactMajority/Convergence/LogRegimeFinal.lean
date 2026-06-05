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

end SSEM
