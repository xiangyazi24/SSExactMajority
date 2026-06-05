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
