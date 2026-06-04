import SSExactMajority.UpperBound.Time.GenericTrank
import SSExactMajority.UpperBound.Time.OptimalWindows

set_option linter.style.header false

/-!
# Generic-trank faithful reset keystone

This file assembles the faithful reset-completion contract with the generic
`trank` phase windows.  The reset contract is stated directly for
`PEMProtocol n trank Rmax`; no coupled median-timer scale is used in the
keystone.
-/

namespace SSEM

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

section

variable {n trank Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]

/-- Generic faithful reset-completion contract.

The reset entry is the [12]-cited probabilistic window from `CorrectResetSeed`
to the all-resetting epidemic region.  The local epidemic fields are exactly
the abstract obligations consumed by `epidemic_phiCount_to_zero_window_ge_half`,
stated for the generic protocol. -/
structure CRSResetCompletion12Generic {n trank Rmax Emax Dmax : ℕ} (hn : 0 < n)
    (p_reset : ENNReal) (C_reset K_reset : ℕ) : Prop where
  resetProb_pos : 0 < p_reset
  resetProb_le_one : p_reset ≤ 1
  resetConstant_pos : 0 < C_reset
  resetWindow_quadratic : K_reset ≤ C_reset * n * n
  resetReach :
    ∀ (hn2 : 2 ≤ n) (C : Config (AgentState n) Opinion n),
      IsTimerBoundedConfig (7 * (trank + 4)) C →
      CorrectResetSeed C →
        p_reset ≤
          Probability.ProbHitWithin
            (PEMProtocol n trank Rmax Emax Dmax hn) hn2 C
            (ResetCompletionTarget12 (majorityAnswer C)) K_reset
  epidemicStep :
    ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
      EpidemicRegion m D → ¬ EpidemicPhiGoal m D →
        ∀ i j : Fin n,
          EpidemicRegion m
              (D.step (PEMProtocol n trank Rmax Emax Dmax hn) i j) ∨
            EpidemicPhiGoal m
              (D.step (PEMProtocol n trank Rmax Emax Dmax hn) i j)
  epidemicNonincrease :
    ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
      EpidemicRegion m D → ¬ EpidemicPhiGoal m D →
        ∀ i j : Fin n,
          phiCount (D.step (PEMProtocol n trank Rmax Emax Dmax hn) i j) ≤
            phiCount D
  epidemicPairDescent :
    ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
      EpidemicRegion m D → ¬ EpidemicPhiGoal m D → 0 < phiCount D →
        ∀ p : Fin n × Fin n, p ∈ phiNonPhiPairs D →
          EpidemicPhiGoal m
              (D.step (PEMProtocol n trank Rmax Emax Dmax hn) p.1 p.2) ∨
            (EpidemicRegion m
                (D.step (PEMProtocol n trank Rmax Emax Dmax hn) p.1 p.2) ∧
              phiCount
                  (D.step (PEMProtocol n trank Rmax Emax Dmax hn) p.1 p.2) <
                phiCount D)

omit [Inhabited (Fin n × Fin n)] in
/-- Generic answer-epidemic window after reset completion. -/
theorem resetCompletion_to_phiGoal_window_generic (hn4 : 4 ≤ n)
    (p_reset : ENNReal) (C_reset K_reset : ℕ)
    (h12resetCompletion :
      CRSResetCompletion12Generic (n := n) (trank := trank) (Rmax := Rmax)
        (Emax := Emax) (Dmax := Dmax) (by omega : 0 < n)
        p_reset C_reset K_reset) :
    ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
      EpidemicRegion m D →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin
            (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) D (EpidemicPhiGoal m)
            (OW_answerEpidemicWindow n) := by
  classical
  intro m D hD
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocol n trank Rmax Emax Dmax hn0 with hP
  refine epidemic_phiCount_to_zero_window_ge_half
    P hn2 (m := m) D (fun E => EpidemicRegion m E)
    (n * n) (OW_answerEpidemicWindow n) hD
    (fun E hE => epidemicRegion_answerInv hE)
    (fun E hE hNot i j => ?_)
    (fun E hE hNot i j => ?_)
    (fun E hE hNot hPhi p hp => ?_)
    (epidemic_coupon_sum_le_nsq hD)
    (by
      dsimp [OW_answerEpidemicWindow]
      calc
        2 * (n * n) = 2 * n * n := by ring
        _ ≤ 2 * n * n + 1 := Nat.le_succ _)
  · simpa [P] using h12resetCompletion.epidemicStep m E hE hNot i j
  · simpa [P] using h12resetCompletion.epidemicNonincrease m E hE hNot i j
  · simpa [P] using h12resetCompletion.epidemicPairDescent m E hE hNot hPhi p hp

omit [Inhabited (Fin n × Fin n)] in
/-- Generic faithful CRS-to-silence wrapper retaining the product probability. -/
theorem CRS_to_silence_faithful_product_generic (hn4 : 4 ≤ n)
    (K_reset T_rank : ℕ)
    (p_reset rankProb : ENNReal) (C_reset : ℕ)
    (h12resetCompletion :
      CRSResetCompletion12Generic (n := n) (trank := trank) (Rmax := Rmax)
        (Emax := Emax) (Dmax := Dmax) (by omega : 0 < n)
        p_reset C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
          rankProb ≤
            Probability.ProbHitWithin
              (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (trank + 4)) C →
      CorrectResetSeed C →
        p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤
          Probability.ProbHitWithin
            (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C OW_silenceEndpoint
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
  classical
  intro C hTimer hSeed
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocol n trank Rmax Emax Dmax hn0 with hP
  have hReset :
      p_reset ≤
        Probability.ProbHitWithin P hn2 C
          (ResetCompletionTarget12 (majorityAnswer C)) K_reset := by
    simpa [P] using h12resetCompletion.resetReach hn2 C hTimer hSeed
  have hEpidemic :
      ∀ D : Config (AgentState n) Opinion n,
        ResetCompletionTarget12 (majorityAnswer C) D →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 D
              (EpidemicPhiGoal (majorityAnswer C)) (OW_answerEpidemicWindow n) := by
    intro D hD
    simpa [P, ResetCompletionTarget12] using
      (resetCompletion_to_phiGoal_window_generic
        (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 p_reset C_reset K_reset h12resetCompletion
        (majorityAnswer C) D hD)
  have hResetToPhi :
      p_reset * ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C
          (EpidemicPhiGoal (majorityAnswer C))
          (K_reset + OW_answerEpidemicWindow n) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C
      (ResetCompletionTarget12 (majorityAnswer C))
      (EpidemicPhiGoal (majorityAnswer C))
      K_reset (OW_answerEpidemicWindow n)
      p_reset ((2 : ENNReal)⁻¹) hReset hEpidemic
  have hRankToSilence :
      ∀ D : Config (AgentState n) Opinion n,
        EpidemicPhiGoal (majorityAnswer C) D →
          rankProb ≤
            Probability.ProbHitWithin P hn2 D OW_silenceEndpoint T_rank := by
    intro D hD
    have hRankRaw :
        rankProb ≤
          Probability.ProbHitWithin P hn2 D
            (OW_rankedEpidemicEndpoint (majorityAnswer C)) T_rank := by
      simpa [P] using h12rank (majorityAnswer C) D hD
    exact hRankRaw.trans
      (Probability.ProbHitWithin_mono_goal P hn2 D
        (OW_rankedEpidemicEndpoint (majorityAnswer C)) OW_silenceEndpoint
        (fun E hE => OW_silenceEndpoint_of_rankedEpidemicEndpoint hE)
        T_rank)
  simpa [Nat.add_assoc, add_assoc] using
    (Probability.ProbHitWithin_add_ge_mul P hn2 C
      (EpidemicPhiGoal (majorityAnswer C)) OW_silenceEndpoint
      (K_reset + OW_answerEpidemicWindow n) T_rank
      (p_reset * ((2 : ENNReal)⁻¹)) rankProb
      hResetToPhi hRankToSilence)

omit [Inhabited (Fin n × Fin n)] in
/-- Generic faithful CRS-to-consensus wrapper retaining the product probability. -/
theorem CRS_to_consensus_faithful_product_generic (hn4 : 4 ≤ n)
    (K_reset T_rank : ℕ)
    (p_reset rankProb : ENNReal) (C_reset : ℕ)
    (h12resetCompletion :
      CRSResetCompletion12Generic (n := n) (trank := trank) (Rmax := Rmax)
        (Emax := Emax) (Dmax := Dmax) (by omega : 0 < n)
        p_reset C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
          rankProb ≤
            Probability.ProbHitWithin
              (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (trank + 4)) C →
      CorrectResetSeed C →
        p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤
          Probability.ProbHitWithin
            (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C IsConsensusConfig
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
  classical
  intro C hTimer hSeed
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocol n trank Rmax Emax Dmax hn0 with hP
  have hSilence :
      p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤
        Probability.ProbHitWithin P hn2 C OW_silenceEndpoint
          (K_reset + OW_answerEpidemicWindow n + T_rank) := by
    simpa [P] using
      (CRS_to_silence_faithful_product_generic
        (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 K_reset T_rank p_reset rankProb C_reset h12resetCompletion h12rank
        C hTimer hSeed)
  exact hSilence.trans
    (Probability.ProbHitWithin_mono_goal P hn2 C
      OW_silenceEndpoint IsConsensusConfig
      (fun D hD => isConsensusConfig_of_InSswap_phiCount_zero hD.1 hD.2.1 hD.2.2)
      (K_reset + OW_answerEpidemicWindow n + T_rank))

/-- Generic-trank end-to-end keystone.  This is the coupled keystone with every
phase window taken from `GenericTrank`. -/
theorem PEM_expectedParallelTime_optimal_generic (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C_rank T_timer K_reset T_rank T_rerank : ℕ)
    (p_reset : ENNReal) (C_reset : ℕ)
    (hTimerStep : ∀ D : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig T_timer D → ∀ i j : Fin n,
        IsTimerBoundedConfig T_timer
          (D.step (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n)) i j))
    (h12ranking :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (trank + 4)) C →
          IsTimerBoundedConfig T_timer C →
          Probability.expectedHittingTime
            (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C
            (fun D => InSrank D ∧ MedianTimerAtLeast 35 D ∧
              IsTimerBoundedConfig (7 * (trank + 4)) D ∧
              IsTimerBoundedConfig T_timer D) ≤
            ((C_rank * n * n : ℕ) : ENNReal))
    (h12resetCompletion :
      CRSResetCompletion12Generic (n := n) (trank := trank) (Rmax := Rmax)
        (Emax := Emax) (Dmax := Dmax) (by omega : 0 < n)
        p_reset C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank)
    (h12reRank :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (trank + 4)) C →
        IsTimerBoundedConfig T_timer C →
        ¬ (InSswap C ∧ MedianTimerAtLeast 35 C) →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (fun D => InSswap D ∧ MedianTimerAtLeast 35 D) T_rerank) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (trank + 4)) C₀ →
      IsTimerBoundedConfig T_timer C₀ →
      Probability.expectedParallelTimeToConsensus
        (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀ ≤
        (((OW_globalWindow n C_rank T_timer K_reset T_rank T_rerank : ℕ) : ENNReal) *
          (p_reset * ((128 : ENNReal)⁻¹))⁻¹ / n) := by
  classical
  intro C₀ hTimer₀ hTimerT₀
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocol n trank Rmax Emax Dmax hn0 with hP
  let Inv : Config (AgentState n) Opinion n → Prop :=
    fun C => IsTimerBoundedConfig (7 * (trank + 4)) C ∧
      IsTimerBoundedConfig T_timer C
  let RankTarget : Config (AgentState n) Opinion n → Prop :=
    fun C =>
      InSrank C ∧ MedianTimerAtLeast 35 C ∧
        IsTimerBoundedConfig (7 * (trank + 4)) C ∧
        IsTimerBoundedConfig T_timer C
  let Live35 : Config (AgentState n) Opinion n → Prop :=
    fun C => InSswap C ∧ MedianTimerAtLeast 35 C
  let Live35Target : Config (AgentState n) Opinion n → Prop :=
    fun C => Live35 C ∧ Inv C
  let DecisionTarget : Config (AgentState n) Opinion n → Prop :=
    (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
  let DecisionMid : Config (AgentState n) Opinion n → Prop :=
    fun C => DecisionTarget C ∧ Inv C
  let ConsOrCRS : Config (AgentState n) Opinion n → Prop :=
    fun C => IsConsensusConfig C ∨ CorrectResetSeed C
  let ConsOrCRSMid : Config (AgentState n) Opinion n → Prop :=
    fun C => ConsOrCRS C ∧ Inv C
  let KLive : ℕ := OW_liveConsensusWindow n T_timer K_reset T_rank
  let K : ℕ := OW_globalWindow n C_rank T_timer K_reset T_rank T_rerank
  have hKpos : 0 < K := by
    have hDecisionPos : 0 < decisionWindow n := by
      dsimp [decisionWindow]
      exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
    have hLivePos : 0 < OW_liveConsensusWindow n T_timer K_reset T_rank := by
      dsimp [OW_liveConsensusWindow]
      omega
    dsimp [K, OW_globalWindow]
    omega
  haveI : NeZero K := ⟨Nat.pos_iff_ne_zero.mp hKpos⟩
  have hp_le_one : p_reset * ((128 : ENNReal)⁻¹) ≤ 1 := by
    exact (mul_le_mul' h12resetCompletion.resetProb_le_one
      (by norm_num : ((128 : ENNReal)⁻¹) ≤ 1)).trans (by simp)
  have hInvStep : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j) := by
    intro C hC i j
    constructor
    · simpa [P, Inv] using
        generic_timer_preservation
          (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn0 (by omega : 7 * (trank + 4) ≤ 7 * (trank + 4))
          C hC.1 i j
    · simpa [P, Inv] using hTimerStep C hC.2 i j
  have hConsOrCRSToConsensus :
      ∀ C : Config (AgentState n) Opinion n, ConsOrCRSMid C →
        p_reset * ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
    intro C hC
    rcases hC with ⟨hEvent, hInvC⟩
    rcases hEvent with hCons | hSeed
    · have hOne : (1 : ENNReal) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
        calc
          (1 : ENNReal) = Probability.probReached P hn2 C IsConsensusConfig 0 := by
              exact (Probability.probReached_zero_of_goal P hn2 C IsConsensusConfig hCons).symm
          _ ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig 0 :=
              Probability.probReached_le_ProbHitWithin P hn2 C IsConsensusConfig 0
          _ ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig
                (K_reset + OW_answerEpidemicWindow n + T_rank) :=
              Probability.ProbHitWithin_mono_time P hn2 C IsConsensusConfig (Nat.zero_le _)
      have hp4_le_one : p_reset * ((4 : ENNReal)⁻¹) ≤ 1 := by
        exact (mul_le_mul' h12resetCompletion.resetProb_le_one
          (by norm_num : ((4 : ENNReal)⁻¹) ≤ 1)).trans (by simp)
      exact hp4_le_one.trans hOne
    · have hCRS :
          p_reset * ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 C IsConsensusConfig
              (K_reset + OW_answerEpidemicWindow n + T_rank) := by
        simpa [P] using
          (CRS_to_consensus_faithful_product_generic
            (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 K_reset T_rank p_reset ((2 : ENNReal)⁻¹) C_reset
            h12resetCompletion h12rank C hInvC.1 hSeed)
      have hprod :
          p_reset * ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) =
            p_reset * ((4 : ENNReal)⁻¹) := by
        have hhalf :
            ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((4 : ENNReal)⁻¹) := by
          rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          norm_num
        rw [mul_assoc, hhalf]
      simpa [hprod] using hCRS
  have hDecisionToConsOrCRS :
      ∀ C : Config (AgentState n) Opinion n, DecisionMid C →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C ConsOrCRSMid
            (OW_macLiveWindow n T_timer) := by
    intro C hC
    rcases hC with ⟨hDecision, hInvC⟩
    rcases hDecision with hMAC | hRest
    · have hBase :
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 C ConsOrCRS
              (OW_macLiveWindow n T_timer) := by
        simpa [P, ConsOrCRS, OW_macLiveWindow] using
          (generic_MAClive_to_consensus_or_crs_window
            (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 hn0 hRmax hEmax hDmax T_timer C
            hMAC.1 hMAC.2.1 hMAC.2.2 hInvC.2)
      rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
        P hn2 C ConsOrCRS Inv hInvC hInvStep (OW_macLiveWindow n T_timer)]
      exact hBase
    · rcases hRest with hCons | hSeed
      · have hGoalC : ConsOrCRSMid C := ⟨Or.inl hCons, hInvC⟩
        have hOne : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 C ConsOrCRSMid
              (OW_macLiveWindow n T_timer) := by
          calc
            (1 : ENNReal) =
                Probability.probReached P hn2 C ConsOrCRSMid 0 := by
                  exact (Probability.probReached_zero_of_goal P hn2 C
                    ConsOrCRSMid hGoalC).symm
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 C ConsOrCRSMid 0
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid
                  (OW_macLiveWindow n T_timer) :=
                Probability.ProbHitWithin_mono_time P hn2 C ConsOrCRSMid
                  (Nat.zero_le _)
        exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) hOne
      · have hGoalC : ConsOrCRSMid C := ⟨Or.inr hSeed, hInvC⟩
        have hOne : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 C ConsOrCRSMid
              (OW_macLiveWindow n T_timer) := by
          calc
            (1 : ENNReal) =
                Probability.probReached P hn2 C ConsOrCRSMid 0 := by
                  exact (Probability.probReached_zero_of_goal P hn2 C
                    ConsOrCRSMid hGoalC).symm
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 C ConsOrCRSMid 0
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid
                  (OW_macLiveWindow n T_timer) :=
                Probability.ProbHitWithin_mono_time P hn2 C ConsOrCRSMid
                  (Nat.zero_le _)
        exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) hOne
  have hLiveToConsensus :
      ∀ C : Config (AgentState n) Opinion n, Live35Target C →
        p_reset * ((32 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig KLive := by
    intro C hLiveTarget
    rcases hLiveTarget with ⟨hLive, hInvC⟩
    have hDecisionBase :
        ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C DecisionTarget (decisionWindow n) := by
      simpa [P, DecisionTarget] using
        (generic_decision_before_timer_zero
          (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn4 hn0 hRmax hEmax hDmax C hLive.1 hLive.2)
    have hDecision :
        ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C DecisionMid (decisionWindow n) := by
      rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
        P hn2 C DecisionTarget Inv hInvC hInvStep (decisionWindow n)]
      exact hDecisionBase
    have hAB :
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C ConsOrCRSMid
            (decisionWindow n + OW_macLiveWindow n T_timer) :=
      Probability.ProbHitWithin_add_ge_mul P hn2 C DecisionMid ConsOrCRSMid
        (decisionWindow n) (OW_macLiveWindow n T_timer)
        ((4 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹)
        hDecision hDecisionToConsOrCRS
    have hChain :
        (((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹)) *
            (p_reset * ((4 : ENNReal)⁻¹)) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            ((decisionWindow n + OW_macLiveWindow n T_timer) +
              (K_reset + OW_answerEpidemicWindow n + T_rank)) :=
      Probability.ProbHitWithin_add_ge_mul P hn2 C ConsOrCRSMid IsConsensusConfig
        (decisionWindow n + OW_macLiveWindow n T_timer)
        (K_reset + OW_answerEpidemicWindow n + T_rank)
        (((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹))
        (p_reset * ((4 : ENNReal)⁻¹))
        hAB hConsOrCRSToConsensus
    have h42 :
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((8 : ENNReal)⁻¹) := by
      rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    have h84 :
        ((8 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) = ((32 : ENNReal)⁻¹) := by
      rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    have hprod :
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
            (p_reset * ((4 : ENNReal)⁻¹)) =
          p_reset * ((32 : ENNReal)⁻¹) := by
      calc
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
            (p_reset * ((4 : ENNReal)⁻¹))
            = p_reset * (((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
                ((4 : ENNReal)⁻¹)) := by ac_rfl
        _ = p_reset * (((8 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹)) := by rw [h42]
        _ = p_reset * ((32 : ENNReal)⁻¹) := by rw [h84]
    simpa [KLive, OW_liveConsensusWindow, hprod] using hChain
  have hwin : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ¬ IsConsensusConfig C →
      p_reset * ((128 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig K := by
    intro C hInvC _hNot
    have hRankE : Probability.expectedHittingTime P hn2 C RankTarget ≤
        ((C_rank * n * n : ℕ) : ENNReal) := by
      simpa [P, RankTarget, Inv] using h12ranking C hInvC.1 hInvC.2
    have hRankW : 2 * (C_rank * n * n) ≤ (2 * C_rank * n * n) + 1 := by nlinarith
    have hRankPH : ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C RankTarget (2 * C_rank * n * n) :=
      Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
        P hn2 C RankTarget hRankE hRankW
    have hLivePH : ∀ D : Config (AgentState n) Opinion n, RankTarget D →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 D Live35Target T_rerank := by
      intro D hD
      by_cases hLive : Live35 D
      · have hGoalD : Live35Target D := ⟨hLive, hD.2.2⟩
        have hOne : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 D Live35Target T_rerank := by
          calc
            (1 : ENNReal) =
                Probability.probReached P hn2 D Live35Target 0 := by
                  exact (Probability.probReached_zero_of_goal P hn2 D
                    Live35Target hGoalD).symm
            _ ≤ Probability.ProbHitWithin P hn2 D Live35Target 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 D Live35Target 0
            _ ≤ Probability.ProbHitWithin P hn2 D Live35Target T_rerank :=
                Probability.ProbHitWithin_mono_time P hn2 D Live35Target
                  (Nat.zero_le _)
        exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) hOne
      · have hBase :
            ((2 : ENNReal)⁻¹) ≤
              Probability.ProbHitWithin P hn2 D Live35 T_rerank := by
          simpa [P, Live35] using h12reRank D hD.2.2.1 hD.2.2.2 hLive
        rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
          P hn2 D Live35 Inv hD.2.2 hInvStep T_rerank]
        exact hBase
    have hAB : ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C Live35Target
          (2 * C_rank * n * n + T_rerank) := by
      have hAB' : ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C Live35Target
            (2 * C_rank * n * n + T_rerank) :=
        Probability.ProbHitWithin_add_ge_mul P hn2 C RankTarget Live35Target
          (2 * C_rank * n * n) T_rerank
          ((2 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹)
          hRankPH hLivePH
      have hprod :
          ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((4 : ENNReal)⁻¹) := by
        rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        norm_num
      simpa [hprod] using hAB'
    have hChain : ((4 : ENNReal)⁻¹) * (p_reset * ((32 : ENNReal)⁻¹)) ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig
          ((2 * C_rank * n * n + T_rerank) + KLive) :=
      Probability.ProbHitWithin_add_ge_mul P hn2 C Live35Target IsConsensusConfig
        (2 * C_rank * n * n + T_rerank) KLive
        ((4 : ENNReal)⁻¹) (p_reset * ((32 : ENNReal)⁻¹))
        hAB hLiveToConsensus
    have hprod :
        ((4 : ENNReal)⁻¹) * (p_reset * ((32 : ENNReal)⁻¹)) =
          p_reset * ((128 : ENNReal)⁻¹) := by
      have h432 :
          ((4 : ENNReal)⁻¹) * ((32 : ENNReal)⁻¹) = ((128 : ENNReal)⁻¹) := by
        rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        norm_num
      calc
        ((4 : ENNReal)⁻¹) * (p_reset * ((32 : ENNReal)⁻¹))
            = p_reset * (((4 : ENNReal)⁻¹) * ((32 : ENNReal)⁻¹)) := by ac_rfl
        _ = p_reset * ((128 : ENNReal)⁻¹) := by rw [h432]
    simpa [K, OW_globalWindow, hprod] using hChain
  simpa [Probability.expectedParallelTimeToConsensus, P, Inv, K] using
    (Probability.expectedParallelTime_le_window_mul_inv_of_invariant
      P hn2 C₀ IsConsensusConfig Inv K (p_reset * ((128 : ENNReal)⁻¹))
      hp_le_one ⟨hTimer₀, hTimerT₀⟩ hInvStep hwin)

/-- Concrete constant timer cap for `trank = 1`. -/
def PEM_trank1_timer : ℕ := 35

/-- Instantiated generic keystone at `trank = 1`, hence `T_timer = 35`. -/
theorem PEM_expectedParallelTime_On (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C_rank K_reset T_rank T_rerank : ℕ)
    (p_reset : ENNReal) (C_reset : ℕ)
    (h12ranking :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig PEM_trank1_timer C →
          Probability.expectedHittingTime
            (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C
            (fun D => InSrank D ∧ MedianTimerAtLeast 35 D ∧
              IsTimerBoundedConfig PEM_trank1_timer D) ≤
            ((C_rank * n * n : ℕ) : ENNReal))
    (h12resetCompletion :
      CRSResetCompletion12Generic (n := n) (trank := 1) (Rmax := Rmax)
        (Emax := Emax) (Dmax := Dmax) (by omega : 0 < n)
        p_reset C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank)
    (h12reRank :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig PEM_trank1_timer C →
        ¬ (InSswap C ∧ MedianTimerAtLeast 35 C) →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (fun D => InSswap D ∧ MedianTimerAtLeast 35 D) T_rerank) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig PEM_trank1_timer C₀ →
      Probability.expectedParallelTimeToConsensus
        (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀ ≤
        (((OW_globalWindow n C_rank PEM_trank1_timer K_reset T_rank T_rerank : ℕ) :
            ENNReal) *
          (p_reset * ((128 : ENNReal)⁻¹))⁻¹ / n) := by
  intro C₀ hTimer₀
  have hTimerStep : ∀ D : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig PEM_trank1_timer D → ∀ i j : Fin n,
        IsTimerBoundedConfig PEM_trank1_timer
          (D.step (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n)) i j) := by
    intro D hD i j
    simpa [PEM_trank1_timer] using
      (generic_timer_preservation
        (n := n) (trank := 1) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (by omega : 0 < n) (by norm_num : 7 * (1 + 4) ≤ 35) D hD i j)
  exact
    (PEM_expectedParallelTime_optimal_generic
      (n := n) (trank := 1) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hRmax hEmax hDmax C_rank PEM_trank1_timer K_reset T_rank T_rerank
      p_reset C_reset hTimerStep
      (fun C hT35 _hT =>
        by
          simpa [PEM_trank1_timer] using h12ranking C hT35)
      h12resetCompletion
      h12rank
      (fun C hT35 _hT hNot =>
        by
          simpa [PEM_trank1_timer] using h12reRank C hT35 hNot)
      C₀
      (by simpa [PEM_trank1_timer] using hTimer₀)
      (by simpa [PEM_trank1_timer] using hTimer₀))

omit [Inhabited (Fin n × Fin n)] in
/-- Explicit quadratic sequential window for the `trank = 1` instantiation. -/
theorem OW_globalWindow_trank1_quadratic
    {K_reset C_reset T_rank C_T_rank T_rerank C_T_rerank C_rank : ℕ}
    (hK : K_reset ≤ C_reset * n * n)
    (hRank : T_rank ≤ C_T_rank * n * n)
    (hRerank : T_rerank ≤ C_T_rerank * n * n) :
    OW_globalWindow n C_rank PEM_trank1_timer K_reset T_rank T_rerank ≤
      (2 * C_rank + C_reset + C_T_rank + C_T_rerank + 76) * n * n := by
  have hnn : n * (n - 1) ≤ n * n :=
    Nat.mul_le_mul_left n (Nat.sub_le n 1)
  dsimp [OW_globalWindow, OW_liveConsensusWindow, decisionWindow,
    OW_macLiveWindow, OW_answerEpidemicWindow, PEM_trank1_timer]
  nlinarith

end

end SSEM
