import SSExactMajority.UpperBound.Time.PolynomialBound

namespace SSEM

open scoped ENNReal

/-- hPropagationLive with IsBoundedConfig: from InSswap + MAC + timer>=1 +
    bounded config + not-consensus, E[T to consensus] < top. -/
theorem PEM_propagation_live_bounded
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (_hSswap : InSswap C)
    (_hMedCorrect : MedianAnswerCorrect C)
    (_hTimerLo : MedianTimerAtLeast 1 C)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C)
    (_hNotCon : ¬ IsConsensusConfig C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C IsConsensusConfig < ⊤ :=
  bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmax C hBounded

/-- Consensus is absorbing under PEMProtocolCoupled. -/
theorem PEMProtocolCoupled_consensus_absorbing
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hC : IsConsensusConfig C) (i j : Fin n) :
    IsConsensusConfig
      (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  have hfix : RankDeltaSettledFix (rankDeltaOSSR Rmax Emax Dmax hn0) :=
    rankDeltaOSSR_satisfies_fix
  simpa [PEMProtocolCoupled, PEMProtocol] using step_preserves_consensus hfix hC i j

/-! ### Key lemma: polynomial E[T] from InSswap + MAC to consensus

Under InSswap + MedianAnswerCorrect, the decision-phase interactions
decrease wrongAnswerCount, giving E[T to consensus] <= n^2(n-1).

Required sub-lemmas (protocol-specific):
1. InSswap and MAC preserved or consensus reached at each step
2. wrongAnswerCount non-increasing under InSswap and MAC
3. Descent pair exists with prob >= 1/(n(n-1))

The main difficulty: when MAC holds but wrongAnswerCount > 0, the wrong
answers are at non-median positions. Correcting them requires either:
(a) A direct median-to-non-median interaction that propagates the correct answer
(b) A reset cycle (timer drain -> CRS -> epidemic -> re-ranking -> new InSswap)
The paper uses approach (b) with Chernoff bounds for the constant-probability
argument per cycle. -/

/-- E[T to consensus from InSswap + MAC] <= wrongAnswerCount(C) * n(n-1). -/
theorem PEM_expected_consensus_from_InSswap_MAC
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C) (hMAC : MedianAnswerCorrect C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C IsConsensusConfig ≤
      ((wrongAnswerCount C * (n * (n - 1)) : ℕ) : ENNReal) := by
  -- ⚠️ STATEMENT AUDIT (Zinan 2026-06-03): this bound is almost certainly FALSE
  -- as stated (off by a factor of ~Rmax).  Under InSswap, the ONLY mechanism
  -- that changes a Settled agent's answer is `phase4_propagate`, which fires
  -- only at the median, only once the median's timer has drained to 0, and it
  -- converts BOTH agents to `.Resetting` (resetcount := Rmax) — i.e. correcting
  -- even ONE wrong non-median answer requires a full reset cycle, not an
  -- in-place fix.  The median timer (≤ 7(Rmax+4)) decrements only on
  -- median↔max interactions (prob ~1/(n(n-1)) per step), so just draining it
  -- costs ~Rmax·n(n-1) expected steps — already ≫ wrongAnswerCount·n(n-1) when
  -- wrongAnswerCount is small.  Correct bound should carry an Rmax factor
  -- (~O(Rmax·n²), cf. RecoveryBound's 8·Rmax·n²).  Restate before proving; the
  -- only consumer is `hPropagationLive_proof`, which then needs its window/
  -- Markov constants re-derived.  This branch is NOT on the clean finite-time
  -- theorem's path (PEM_expected_parallel_time_finite_of_initial is sorry/axiom-free).
  sorry

set_option maxHeartbeats 1600000 in
set_option linter.unusedDecidableInType false in
/-- **hPropagationLive**: from InSswap + MAC + timer>=1 + timer<=7(Rmax+4) + not-consensus,
    probReached to consensus within 20*Rmax*n*n >= 1/1280.

    Proof: E[T to consensus] <= n^2(n-1) <= Rmax*n^2 (since n <= Rmax).
    By Markov: ProbHitWithin(20*Rmax*n^2) >= 1/2.
    Since consensus is absorbing: probReached >= ProbHitWithin >= 1/2 >= 1/1280. -/
theorem hPropagationLive_proof
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (_hTimerLo : MedianTimerAtLeast 1 C)
    (_hTimerHi : MedianTimerAtMost (7 * (Rmax + 4)) C)
    (_hNotCon : ¬ IsConsensusConfig C) :
    ((1280 : ENNReal)⁻¹) ≤
      Probability.probReached
        (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n) with hP_def
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  -- Step 1: E[T to consensus] <= wrongAnswerCount * n(n-1)
  have hET := PEM_expected_consensus_from_InSswap_MAC (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) hn4 hn0 C hSswap hMedCorrect
  -- wrongAnswerCount <= n
  have hWA_le_n : wrongAnswerCount C ≤ n := by
    unfold wrongAnswerCount
    calc (Finset.univ.filter fun w : Fin n =>
        (C w).1.answer ≠ majorityAnswer C).card
        ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = n := Finset.card_fin n
  -- E[T] <= n^2(n-1) <= Rmax*n^2
  have hpoly_le : wrongAnswerCount C * (n * (n - 1)) ≤ Rmax * n * n := by
    calc wrongAnswerCount C * (n * (n - 1))
        ≤ n * (n * (n - 1)) := Nat.mul_le_mul_right _ hWA_le_n
      _ ≤ n * (n * n) := Nat.mul_le_mul_left n (Nat.mul_le_mul_left n (Nat.sub_le n 1))
      _ ≤ Rmax * (n * n) := Nat.mul_le_mul_right (n * n) hRmax
      _ = Rmax * n * n := by ring
  have hET_Rmax : Probability.expectedHittingTime P hn2 C IsConsensusConfig ≤
      ((Rmax * n * n : ℕ) : ENNReal) :=
    hET.trans (by exact_mod_cast hpoly_le)
  -- Step 2: Markov -> ProbHitWithin >= 1/2
  have htime : 2 * (Rmax * n * n) ≤ 20 * Rmax * n * n + 1 := by
    have h : 20 * Rmax * n * n = 20 * (Rmax * n * n) := by ring
    rw [h]; omega
  have hPHW_half : ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C IsConsensusConfig (20 * Rmax * n * n) :=
    Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le P hn2 C
      IsConsensusConfig hET_Rmax htime
  -- Step 3: ProbHitWithin <= probReached (consensus is absorbing)
  have hAbsConvert :
      Probability.ProbHitWithin P hn2 C IsConsensusConfig (20 * Rmax * n * n) ≤
      Probability.probReached P hn2 C IsConsensusConfig (20 * Rmax * n * n) :=
    Probability.ProbHitWithin_le_probReached_of_absorbing P hn2 C IsConsensusConfig
      (fun D hD i j => PEMProtocolCoupled_consensus_absorbing hn0 hD i j)
      (20 * Rmax * n * n)
  -- Step 4: 1/1280 <= 1/2 <= ProbHitWithin <= probReached
  calc ((1280 : ENNReal)⁻¹)
      ≤ ((2 : ENNReal)⁻¹) := by
        rw [ENNReal.inv_le_inv]
        norm_num
    _ ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig (20 * Rmax * n * n) := hPHW_half
    _ ≤ Probability.probReached P hn2 C IsConsensusConfig (20 * Rmax * n * n) := hAbsConvert

/-- End-to-end: expected parallel time to consensus is finite from any initial config. -/
theorem PEM_expected_parallel_time_finite_init
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C₀ : Config (AgentState n) Opinion n)
    (hInit : IsInitialConfig C₀) :
    Probability.expectedParallelTimeToConsensus
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C₀ < ⊤ := by
  have hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C₀ := by
    intro w; have h := hInit w
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hSeq : Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C₀ IsConsensusConfig < ⊤ :=
    bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmax C₀ hBounded
  exact ENNReal.div_lt_top (ne_of_lt hSeq) (by exact_mod_cast (show (n : ℕ) ≠ 0 by omega))

end SSEM
