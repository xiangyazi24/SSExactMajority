import SSExactMajority.UpperBound.Time.Defs
import SSExactMajority.UpperBound.Time.SwapPhase
import SSExactMajority.UpperBound.Time.DecisionPhase
import SSExactMajority.UpperBound.Time.TimerDrain

namespace SSEM

open scoped ENNReal

/-! ### Kanaya Table-2 phase composition -/

/-- The product of the five success probabilities in Kanaya Table 2:
`1/10 * 1/20 * 1/8 * 1/1280 * 1/2`.

The decimal denominator is `4096000`; keeping the product form avoids
unnecessary arithmetic coercion work in phase-composition proofs. -/
noncomputable def pemTable2SuccessProb : ENNReal :=
  ((10 : ENNReal)⁻¹) *
    ((20 : ENNReal)⁻¹) *
      ((8 : ENNReal)⁻¹) *
        ((1280 : ENNReal)⁻¹) *
          ((2 : ENNReal)⁻¹)

theorem pemTable2SuccessProb_le_one : pemTable2SuccessProb ≤ 1 := by
  unfold pemTable2SuccessProb
  have h10 : ((10 : ENNReal)⁻¹) ≤ 1 :=
    (ENNReal.inv_le_one).2 (by norm_num)
  have h20 : ((20 : ENNReal)⁻¹) ≤ 1 :=
    (ENNReal.inv_le_one).2 (by norm_num)
  have h8 : ((8 : ENNReal)⁻¹) ≤ 1 :=
    (ENNReal.inv_le_one).2 (by norm_num)
  have h1280 : ((1280 : ENNReal)⁻¹) ≤ 1 :=
    (ENNReal.inv_le_one).2 (by norm_num)
  have h2 : ((2 : ENNReal)⁻¹) ≤ 1 :=
    (ENNReal.inv_le_one).2 (by norm_num)
  calc
    ((10 : ENNReal)⁻¹) * ((20 : ENNReal)⁻¹) *
          ((8 : ENNReal)⁻¹) * ((1280 : ENNReal)⁻¹) *
          ((2 : ENNReal)⁻¹)
        ≤ 1 * 1 * 1 * 1 * 1 := by
          gcongr
    _ = 1 := by norm_num

/-- Direct five-phase window composition for the Table-2 route.  The
hypotheses are conditional endpoint probabilities for each phase; no
independence between phase endpoints is assumed. -/
theorem pem_table2_phase_window_to_ProbHitWithin
    {n : ℕ} [DecidableEq (Config (AgentState n) Opinion n)]
    (P : Protocol (AgentState n) Opinion Output) (hn2 : 2 ≤ n)
    (C₀ : Config (AgentState n) Opinion n)
    (SrankPhase SswapPhase SdecPhase StimPhase SemPhase :
      Config (AgentState n) Opinion n → Prop)
    [DecidablePred SrankPhase] [DecidablePred SswapPhase]
    [DecidablePred SdecPhase] [DecidablePred StimPhase]
    [DecidablePred SemPhase]
    (tRank tSwap tDec tTim tSem : ℕ)
    (hRank :
      ((10 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C₀ SrankPhase tRank)
    (hSwap : ∀ C, SrankPhase C →
      ((20 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C SswapPhase tSwap)
    (hDec : ∀ C, SswapPhase C →
      ((8 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C SdecPhase tDec)
    (hTim : ∀ C, SdecPhase C →
      ((1280 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C StimPhase tTim)
    (hSem : ∀ C, StimPhase C →
      ((2 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C SemPhase tSem) :
    pemTable2SuccessProb ≤
      Probability.ProbHitWithin P hn2 C₀ SemPhase
        ((((tRank + tSwap) + tDec) + tTim) + tSem) := by
  classical
  have hRankHit :
      ((10 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C₀ SrankPhase tRank :=
    hRank.trans (Probability.probReached_le_ProbHitWithin P hn2 C₀ SrankPhase tRank)
  have hSwapHit : ∀ C, SrankPhase C →
      ((20 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C SswapPhase tSwap := by
    intro C hC
    exact (hSwap C hC).trans
      (Probability.probReached_le_ProbHitWithin P hn2 C SswapPhase tSwap)
  have hDecHit : ∀ C, SswapPhase C →
      ((8 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C SdecPhase tDec := by
    intro C hC
    exact (hDec C hC).trans
      (Probability.probReached_le_ProbHitWithin P hn2 C SdecPhase tDec)
  have hTimHit : ∀ C, SdecPhase C →
      ((1280 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C StimPhase tTim := by
    intro C hC
    exact (hTim C hC).trans
      (Probability.probReached_le_ProbHitWithin P hn2 C StimPhase tTim)
  have hSemHit : ∀ C, StimPhase C →
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C SemPhase tSem := by
    intro C hC
    exact (hSem C hC).trans
      (Probability.probReached_le_ProbHitWithin P hn2 C SemPhase tSem)
  have h12 :
      ((10 : ENNReal)⁻¹) * ((20 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C₀ SswapPhase (tRank + tSwap) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀
      SrankPhase SswapPhase tRank tSwap
      ((10 : ENNReal)⁻¹) ((20 : ENNReal)⁻¹) hRankHit hSwapHit
  have h123 :
      (((10 : ENNReal)⁻¹) * ((20 : ENNReal)⁻¹)) * ((8 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C₀ SdecPhase
          ((tRank + tSwap) + tDec) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀
      SswapPhase SdecPhase (tRank + tSwap) tDec
      (((10 : ENNReal)⁻¹) * ((20 : ENNReal)⁻¹)) ((8 : ENNReal)⁻¹)
      h12 hDecHit
  have h1234 :
      ((((10 : ENNReal)⁻¹) * ((20 : ENNReal)⁻¹)) * ((8 : ENNReal)⁻¹)) *
          ((1280 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C₀ StimPhase
          (((tRank + tSwap) + tDec) + tTim) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀
      SdecPhase StimPhase ((tRank + tSwap) + tDec) tTim
      ((((10 : ENNReal)⁻¹) * ((20 : ENNReal)⁻¹)) * ((8 : ENNReal)⁻¹))
      ((1280 : ENNReal)⁻¹) h123 hTimHit
  have h12345 :
      (((((10 : ENNReal)⁻¹) * ((20 : ENNReal)⁻¹)) * ((8 : ENNReal)⁻¹)) *
          ((1280 : ENNReal)⁻¹)) * ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C₀ SemPhase
          ((((tRank + tSwap) + tDec) + tTim) + tSem) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀
      StimPhase SemPhase (((tRank + tSwap) + tDec) + tTim) tSem
      (((((10 : ENNReal)⁻¹) * ((20 : ENNReal)⁻¹)) * ((8 : ENNReal)⁻¹)) *
        ((1280 : ENNReal)⁻¹)) ((2 : ENNReal)⁻¹) h1234 hSemHit
  simpa [pemTable2SuccessProb, mul_assoc] using h12345

/-- Three-phase consensus composition using only hitting-window probabilities.

This is the lightweight PEM route: hit `InSrank`, then hit `InSswap` from any
ranking endpoint, then hit consensus from any swap endpoint.  The middle target
does not need to be absorbing, because the composition is entirely in
`ProbHitWithin`. -/
theorem PEM_consensus_ProbHitWithin_from_phase_bounds
    {n : ℕ} [DecidableEq (Config (AgentState n) Opinion n)]
    (P : Protocol (AgentState n) Opinion Output) (hn2 : 2 ≤ n)
    (C₀ : Config (AgentState n) Opinion n)
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred
      (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (tRank tSwap tConsensus : ℕ)
    (pRank pSwap pConsensus : ENNReal)
    (hRank :
      pRank ≤ Probability.ProbHitWithin P hn2 C₀ InSrank tRank)
    (hSwap : ∀ C : Config (AgentState n) Opinion n, InSrank C →
      pSwap ≤ Probability.ProbHitWithin P hn2 C InSswap tSwap)
    (hConsensus : ∀ C : Config (AgentState n) Opinion n, InSswap C →
      pConsensus ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig tConsensus) :
    (pRank * pSwap) * pConsensus ≤
      Probability.ProbHitWithin P hn2 C₀ IsConsensusConfig
        ((tRank + tSwap) + tConsensus) := by
  classical
  have hRankSwap :
      pRank * pSwap ≤
        Probability.ProbHitWithin P hn2 C₀ InSswap (tRank + tSwap) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀
      InSrank InSswap tRank tSwap pRank pSwap hRank hSwap
  exact
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀
      InSswap IsConsensusConfig (tRank + tSwap) tConsensus
      (pRank * pSwap) pConsensus hRankSwap hConsensus

/-- Markov-generated `1/2 × 1/2 × 1/2` version of
`PEM_consensus_ProbHitWithin_from_phase_bounds`.  Each phase only supplies an
expected hitting-time bound; Markov converts it to a half-probability
`ProbHitWithin` window, and the three windows compose by strong Markov. -/
theorem PEM_consensus_ProbHitWithin_from_expected_phases
    {n : ℕ} [DecidableEq (Config (AgentState n) Opinion n)]
    (P : Protocol (AgentState n) Opinion Output) (hn2 : 2 ≤ n)
    (C₀ : Config (AgentState n) Opinion n)
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred
      (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (MRank MSwap MConsensus tRank tSwap tConsensus : ℕ)
    (hRankExpected :
      Probability.expectedHittingTime P hn2 C₀ InSrank ≤ MRank)
    (hRankWindow : 2 * MRank ≤ tRank + 1)
    (hSwapExpected : ∀ C : Config (AgentState n) Opinion n, InSrank C →
      Probability.expectedHittingTime P hn2 C InSswap ≤ MSwap)
    (hSwapWindow : 2 * MSwap ≤ tSwap + 1)
    (hConsensusExpected :
      ∀ C : Config (AgentState n) Opinion n, InSswap C →
        Probability.expectedHittingTime P hn2 C IsConsensusConfig ≤
          MConsensus)
    (hConsensusWindow : 2 * MConsensus ≤ tConsensus + 1) :
    (((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹)) * ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C₀ IsConsensusConfig
        ((tRank + tSwap) + tConsensus) := by
  classical
  apply PEM_consensus_ProbHitWithin_from_phase_bounds P hn2 C₀
    tRank tSwap tConsensus
    ((2 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹)
  · exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
      P hn2 C₀ InSrank hRankExpected hRankWindow
  · intro C hC
    exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
      P hn2 C InSswap (hSwapExpected C hC) hSwapWindow
  · intro C hC
    exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
      P hn2 C IsConsensusConfig (hConsensusExpected C hC)
        hConsensusWindow

/-- Expected-parallel-time consequence of a uniform Table-2 success window.
This is the abstract geometric amplification step after the concrete phase
probability window has been proved. -/
theorem pem_table2_window_to_expectedParallelTime
    {n : ℕ} [DecidableEq (Config (AgentState n) Opinion n)]
    (P : Protocol (AgentState n) Opinion Output) (hn2 : 2 ≤ n)
    (K : ℕ) [NeZero K]
    (hwin : ∀ C : Config (AgentState n) Opinion n,
      ¬ IsConsensusConfig C →
        pemTable2SuccessProb ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig K) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      Probability.expectedParallelTimeToConsensus P hn2 C₀ ≤
        ((K : ENNReal) * pemTable2SuccessProb⁻¹) / n := by
  intro C₀
  exact
    (Probability.expectedParallelTime_le_window_mul_inv
      (P := P) (hn := hn2) (C₀ := C₀)
      (Goal := IsConsensusConfig) (K := K) (p := pemTable2SuccessProb)
      pemTable2SuccessProb_le_one hwin)

/-- Uniform five-phase Table-2 hypotheses imply the expected-parallel-time
window bound.  The remaining protocol-specific work is exactly to prove these
five hypotheses from scheduler-good-pair counts. -/
theorem pem_table2_phase_windows_to_expectedParallelTime
    {n : ℕ} [DecidableEq (Config (AgentState n) Opinion n)]
    (P : Protocol (AgentState n) Opinion Output) (hn2 : 2 ≤ n)
    (SrankPhase SswapPhase SdecPhase StimPhase :
      Config (AgentState n) Opinion n → Prop)
    [DecidablePred SrankPhase] [DecidablePred SswapPhase]
    [DecidablePred SdecPhase] [DecidablePred StimPhase]
    [DecidablePred
      (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (tRank tSwap tDec tTim tSem : ℕ)
    [NeZero ((((tRank + tSwap) + tDec) + tTim) + tSem)]
    (hRank : ∀ C₀,
      ((10 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C₀ SrankPhase tRank)
    (hSwap : ∀ C, SrankPhase C →
      ((20 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C SswapPhase tSwap)
    (hDec : ∀ C, SswapPhase C →
      ((8 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C SdecPhase tDec)
    (hTim : ∀ C, SdecPhase C →
      ((1280 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C StimPhase tTim)
    (hSem : ∀ C, StimPhase C →
      ((2 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C
          (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)
          tSem) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      Probability.expectedParallelTimeToConsensus P hn2 C₀ ≤
        (((((tRank + tSwap) + tDec) + tTim) + tSem : ℕ) : ENNReal) *
          pemTable2SuccessProb⁻¹ / n := by
  classical
  let K := (((tRank + tSwap) + tDec) + tTim) + tSem
  have hwin : ∀ C : Config (AgentState n) Opinion n,
      ¬ IsConsensusConfig C →
        pemTable2SuccessProb ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig K := by
    intro C _hNot
    simpa [K] using
      (pem_table2_phase_window_to_ProbHitWithin
        (P := P) (hn2 := hn2) (C₀ := C)
        (SrankPhase := SrankPhase) (SswapPhase := SswapPhase)
        (SdecPhase := SdecPhase) (StimPhase := StimPhase)
        (SemPhase := IsConsensusConfig)
        tRank tSwap tDec tTim tSem
        (hRank C) hSwap hDec hTim hSem)
  intro C₀
  simpa [K] using
    (pem_table2_window_to_expectedParallelTime
      (P := P) (hn2 := hn2) (K := K) hwin C₀)

theorem not_exists_global_InSswap_median_timer_bound
    {n : ℕ} (hn0 : 0 < n) :
    ¬ ∃ K₀ : ℕ, ∀ (C : Config (AgentState n) Opinion n) (μ : Fin n),
        InSswap C →
        (C μ).1.rank.val + 1 = ceilHalf n →
        (C μ).1.timer ≤ K₀ := by
  classical
  rintro ⟨K₀, hK₀⟩
  let Cbad : Config (AgentState n) Opinion n := fun μ =>
    (({ role := .Settled
        rank := μ
        leader := .F
        resetcount := 0
        answer := .outA
        timer := K₀ + 1 } : AgentState n), Opinion.A)
  have hnA : nAOf Cbad = n := by
    unfold nAOf Config.agentsWithInput Config.inputOf
    simp [Cbad]
  have hSwap : InSswap Cbad := by
    refine
      { allSettled := ?_
        ranks_inj := ?_
        input_rank := ?_ }
    · intro v
      rfl
    · intro u v huv
      exact huv
    · intro v
      rw [hnA]
      simp [Cbad]
  have hceil_pos : 0 < ceilHalf n := ceilHalf_pos hn0
  have hceil_le : ceilHalf n ≤ n := ceilHalf_le n
  let μ : Fin n := ⟨ceilHalf n - 1, by omega⟩
  have hμ : (Cbad μ).1.rank.val + 1 = ceilHalf n := by
    dsimp [Cbad, μ]
    omega
  have hle : (Cbad μ).1.timer ≤ K₀ := hK₀ Cbad μ hSwap hμ
  dsimp [Cbad] at hle
  omega

/-- `InSswap` by itself carries neither a consensus guarantee nor a median
timer bound.  This is the concrete obstruction to any phase-C statement that
starts from an arbitrary `InSswap` configuration and tries to bound the time
to `IsConsensusConfig` only in terms of protocol parameters. -/
theorem exists_InSswap_not_consensus_with_large_median_timer
    {n : ℕ} (hn0 : 0 < n) (K : ℕ) :
    ∃ (C : Config (AgentState n) Opinion n) (μ : Fin n),
      InSswap C ∧ ¬ IsConsensusConfig C ∧
      (C μ).1.rank.val + 1 = ceilHalf n ∧ K < (C μ).1.timer := by
  classical
  let bad : Fin n := ⟨0, hn0⟩
  have hceil_pos : 0 < ceilHalf n := ceilHalf_pos hn0
  have hceil_le : ceilHalf n ≤ n := ceilHalf_le n
  let μ : Fin n := ⟨ceilHalf n - 1, by omega⟩
  let Cbad : Config (AgentState n) Opinion n := fun v =>
    (({ role := .Settled
        rank := v
        leader := .F
        resetcount := 0
        answer := if v = bad then .outB else .outA
        timer := if v = μ then K + 1 else 0 } : AgentState n), Opinion.A)
  have hnA : nAOf Cbad = n := by
    unfold nAOf Config.agentsWithInput Config.inputOf
    simp [Cbad]
  have hnB : nBOf Cbad = 0 := by
    unfold nBOf Config.agentsWithInput Config.inputOf
    simp [Cbad]
  have hSwap : InSswap Cbad := by
    refine
      { allSettled := ?_
        ranks_inj := ?_
        input_rank := ?_ }
    · intro v
      rfl
    · intro u v huv
      exact huv
    · intro v
      rw [hnA]
      simp [Cbad]
  have hMaj : majorityAnswer Cbad = .outA := by
    unfold majorityAnswer
    simp [hnA, hnB, hn0]
  have hNotConsensus : ¬ IsConsensusConfig Cbad := by
    intro hCons
    have hbad := hCons.allAnswerCorrect bad
    rw [hMaj] at hbad
    simp [Cbad, bad] at hbad
  have hμ_rank : (Cbad μ).1.rank.val + 1 = ceilHalf n := by
    dsimp [Cbad, μ]
    omega
  have hμ_timer : K < (Cbad μ).1.timer := by
    dsimp [Cbad]
    simp [μ]
  exact ⟨Cbad, μ, hSwap, hNotConsensus, hμ_rank, hμ_timer⟩

/-! ### Consolidated window hypothesis

The final theorem reduces to a single window-success claim: from any
non-consensus configuration, within a quadratic sequential window
(`c · n²` interactions), the protocol reaches `IsConsensusConfig` with
probability at least `pemTable2SuccessProb = 1/4096000`.

Once this claim is established, the abstract geometric-restart inequality
(`pem_table2_window_to_expectedParallelTime`) converts it directly into an
O(n) expected parallel time upper bound. -/

/-- **Kanaya Table-2 consolidated window hypothesis.**  From any non-consensus
configuration, the coupled PEM wrapper reaches `IsConsensusConfig` within
`c · n²` sequential interactions with probability at least
`pemTable2SuccessProb`.

The constant `c` absorbs the per-phase window constants from Table 2:
ranking (`O(n²)` seq), swap (`O(n²)` seq), decision/propagation
(`O(n²)` seq each), plus a trivial identity phase. -/
theorem PEM_consensus_window_success_prob_vacuous_timer_const
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n)
    (_hRmax : n ≤ Rmax) (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (hTimerConst :
      ∃ K₀ : ℕ, ∀ (C : Config (AgentState n) Opinion n) (μ : Fin n),
        InSswap C →
        (C μ).1.rank.val + 1 = ceilHalf n →
        (C μ).1.timer ≤ K₀) :
    ∃ c : ℕ, 0 < c ∧
      ∀ C : Config (AgentState n) Opinion n,
        ¬ IsConsensusConfig C →
          pemTable2SuccessProb ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (c * n * n) := by
  classical
  exact (not_exists_global_InSswap_median_timer_bound (by omega : 0 < n)
    hTimerConst).elim

/-- `pemTable2SuccessProb` is positive: product of positive inverses. -/
private theorem pemTable2SuccessProb_pos : 0 < pemTable2SuccessProb := by
  unfold pemTable2SuccessProb
  have hinv : ∀ (k : ℕ), ((k : ENNReal)⁻¹) ≠ 0 := by
    intro k; rw [ne_eq, ENNReal.inv_eq_zero]; exact ENNReal.natCast_ne_top k
  exact pos_iff_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hinv 10) (hinv 20))
      (hinv 8)) (hinv 1280)) (hinv 2))

/-- `pemTable2SuccessProb` is not `⊤`. -/
private theorem pemTable2SuccessProb_ne_top : pemTable2SuccessProb ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt pemTable2SuccessProb_le_one ENNReal.one_lt_top)

/-- `pemTable2SuccessProb⁻¹` is not `⊤` (since `pemTable2SuccessProb > 0`). -/
private theorem pemTable2SuccessProb_inv_ne_top : pemTable2SuccessProb⁻¹ ≠ ⊤ := by
  rw [ENNReal.inv_ne_top]
  exact ne_of_gt pemTable2SuccessProb_pos

/-- Arithmetic helper: `c · n² · p⁻¹ / n = c · p⁻¹ · n` in ENNReal
after cancelling one factor of `n`. -/
private theorem ennreal_quadratic_window_div_cancel
    {c n : ℕ} (p : ENNReal) (hn : 0 < n)
    (_hp_pos : 0 < p) (_hp_ne_top : p ≠ ⊤) :
    ((c * n * n : ℕ) : ENNReal) * p⁻¹ / ↑n =
      ↑c * p⁻¹ * ↑n := by
  have hn_ne : (↑n : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn_ne_top : (↑n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
  rw [show (c * n * n : ℕ) = c * (n * n) from by ring]
  push_cast [Nat.cast_mul]
  rw [div_eq_mul_inv]
  calc ↑c * (↑n * ↑n) * p⁻¹ * (↑n : ENNReal)⁻¹
      = ↑c * p⁻¹ * (↑n * ↑n * (↑n : ENNReal)⁻¹) := by
        simp only [mul_comm, mul_assoc]
    _ = ↑c * p⁻¹ * (↑n * (↑n * (↑n : ENNReal)⁻¹)) := by
        rw [mul_assoc (↑n : ENNReal)]
    _ = ↑c * p⁻¹ * (↑n * 1) := by
        rw [ENNReal.mul_inv_cancel hn_ne hn_ne_top]
    _ = ↑c * p⁻¹ * ↑n := by rw [mul_one]

/-- Roundtrip: `↑c * p⁻¹ * ↑n` in ENNReal equals
`ENNReal.ofReal ((c : ℝ) * p⁻¹.toReal * (n : ℝ))` for finite `p⁻¹`. -/
private theorem ennreal_nat_mul_inv_mul_nat_eq_ofReal
    {c n : ℕ} (p : ENNReal)
    (hp_pos : 0 < p) (_hp_ne_top : p ≠ ⊤) :
    ↑c * p⁻¹ * (↑n : ENNReal) =
      ENNReal.ofReal ((c : ℝ) * p⁻¹.toReal * (n : ℝ)) := by
  have hp_inv_ne_top : p⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (ne_of_gt hp_pos)
  symm
  calc ENNReal.ofReal ((c : ℝ) * p⁻¹.toReal * (n : ℝ))
      = ENNReal.ofReal ((c : ℝ) * p⁻¹.toReal) * ENNReal.ofReal (n : ℝ) := by
          rw [ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (c : ℝ) * ENNReal.ofReal (p⁻¹.toReal) * ENNReal.ofReal (n : ℝ) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg c)]
    _ = ↑c * p⁻¹ * ↑n := by
          rw [ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hp_inv_ne_top, ENNReal.ofReal_natCast]

/-- **§5.2 quantitative — O(n) expected parallel time upper bound for P_EM,
parameterized by a constant/externally bounded timer regime.**

The literal `ConcretePEM n Emax Dmax` has timer range `7 * (n + 4)`, so the
direct Kanaya timer-drain argument only gives a weaker bound unless a sharper
timer lemma is added. -/
theorem PEM_expected_parallel_time_linear_param
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hTimerConst :
      ∃ K₀ : ℕ, ∀ (C : Config (AgentState n) Opinion n) (μ : Fin n),
        InSswap C →
        (C μ).1.rank.val + 1 = ceilHalf n →
        (C μ).1.timer ≤ K₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C₀ : Config (AgentState n) Opinion n,
        Probability.expectedParallelTimeToConsensus
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C₀ ≤
          ENNReal.ofReal (C * n) := by
  classical
  obtain ⟨c, hc_pos, hwin⟩ :=
    PEM_consensus_window_success_prob_vacuous_timer_const hn4 hRmax hEmax hDmax hTimerConst
  set P := PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n) with hP_def
  have hn2 : 2 ≤ n := by omega
  have hK_ne : NeZero (c * n * n) := ⟨by positivity⟩
  have hle := pem_table2_window_to_expectedParallelTime P hn2 (K := c * n * n) hwin
  refine ⟨c * pemTable2SuccessProb⁻¹.toReal, ?_, fun C₀ => ?_⟩
  · apply mul_pos
    · exact Nat.cast_pos.mpr hc_pos
    · exact ENNReal.toReal_pos
        (ne_of_gt (ENNReal.inv_pos.mpr pemTable2SuccessProb_ne_top))
        pemTable2SuccessProb_inv_ne_top
  · calc Probability.expectedParallelTimeToConsensus P hn2 C₀
        ≤ ((c * n * n : ℕ) : ENNReal) * pemTable2SuccessProb⁻¹ / ↑n := hle C₀
      _ = ↑c * pemTable2SuccessProb⁻¹ * ↑n :=
          ennreal_quadratic_window_div_cancel pemTable2SuccessProb
            (by omega) pemTable2SuccessProb_pos pemTable2SuccessProb_ne_top
      _ = ENNReal.ofReal (↑c * pemTable2SuccessProb⁻¹.toReal * ↑n) :=
          ennreal_nat_mul_inv_mul_nat_eq_ofReal pemTable2SuccessProb
            pemTable2SuccessProb_pos pemTable2SuccessProb_ne_top

/-! ### Non-vacuous window hypothesis and time bound -/

private def AgentCountersBounded (M : ℕ) (s : AgentState n) : Prop :=
  s.timer ≤ M ∧
  s.resetcount ≤ M ∧
  s.errorcount ≤ M ∧
  s.delaytimer ≤ M ∧
  s.children ≤ M

private def PairCountersBounded (M : ℕ) (p : AgentState n × AgentState n) : Prop :=
  AgentCountersBounded M p.1 ∧ AgentCountersBounded M p.2

private theorem resetOSSR_preserves_counter_bound
    {n Emax M : ℕ} {hn : 0 < n} {s : AgentState n}
    (hEmax : Emax ≤ M) (hs : AgentCountersBounded M s) :
    AgentCountersBounded M (resetOSSR Emax hn s) := by
  rcases s with ⟨role, rank, leader, resetcount, answer, timer, children,
    errorcount, delaytimer⟩
  cases leader <;> simp [AgentCountersBounded, resetOSSR] at * <;> omega

set_option maxHeartbeats 800000 in
private theorem processAgent_preserves_counter_bound
    {n Emax Dmax M : ℕ} {hn : 0 < n} {s : AgentState n}
    {oldRc : ℕ} {partnerResetting : Bool}
    (hEmax : Emax ≤ M) (hDmax : Dmax ≤ M)
    (hs : AgentCountersBounded M s) :
    AgentCountersBounded M
      (processAgent Emax Dmax hn s oldRc partnerResetting) := by
  unfold processAgent
  by_cases hmain : s.role = .Resetting ∧ s.resetcount = 0
  · rw [if_pos hmain]
    let t : AgentState n :=
      if 0 < oldRc then
        { s with delaytimer := Dmax }
      else
        { s with delaytimer := s.delaytimer - 1 }
    have ht : AgentCountersBounded M t := by
      by_cases hold : 0 < oldRc
      · simp [t, hold, AgentCountersBounded] at * <;> omega
      · simp [t, hold, AgentCountersBounded] at * <;> omega
    change AgentCountersBounded M
      (if t.delaytimer = 0 ∨ !partnerResetting then resetOSSR Emax hn t else t)
    cases partnerResetting <;>
      by_cases hfire : t.delaytimer = 0 <;>
      simp [hfire, resetOSSR_preserves_counter_bound hEmax ht, ht]
  · rw [if_neg hmain]
    exact hs

private theorem propagateReset_recruit_preserves_counter_bound
    {n Emax Dmax M : ℕ} {a b : AgentState n}
    (hDmax : Dmax ≤ M)
    (ha : AgentCountersBounded M a) (hb : AgentCountersBounded M b) :
    PairCountersBounded M
      (if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
        (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
      else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
        ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
      else (a, b)) := by
  unfold PairCountersBounded
  split_ifs <;> simp_all [AgentCountersBounded] <;> omega

private theorem propagateReset_sync_preserves_counter_bound
    {n M : ℕ} {a b : AgentState n}
    (ha : AgentCountersBounded M a) (hb : AgentCountersBounded M b) :
    PairCountersBounded M
      (if a.role = .Resetting ∧ b.role = .Resetting then
        let newRc := max (a.resetcount - 1) (b.resetcount - 1)
        ({ a with resetcount := newRc }, { b with resetcount := newRc })
      else (a, b)) := by
  unfold PairCountersBounded
  split_ifs <;> simp_all [AgentCountersBounded, max_le_iff] <;> omega

private theorem propagateReset_preserves_counter_bound
    {n Emax Dmax M : ℕ} {hn : 0 < n} {a b : AgentState n}
    (hEmax : Emax ≤ M) (hDmax : Dmax ≤ M)
    (ha : AgentCountersBounded M a) (hb : AgentCountersBounded M b) :
    AgentCountersBounded M (propagateReset Emax Dmax hn a b).1 ∧
    AgentCountersBounded M (propagateReset Emax Dmax hn a b).2 := by
  unfold propagateReset
  let p₁ :=
    if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
      (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
    else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
      ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
    else (a, b)
  have hp₁ : PairCountersBounded M p₁ := by
    simpa [p₁] using
      propagateReset_recruit_preserves_counter_bound
        (Emax := Emax) (Dmax := Dmax) hDmax ha hb
  let oldRcA := p₁.1.resetcount
  let oldRcB := p₁.2.resetcount
  let p₂ :=
    if p₁.1.role = .Resetting ∧ p₁.2.role = .Resetting then
      let newRc := max (p₁.1.resetcount - 1) (p₁.2.resetcount - 1)
      ({ p₁.1 with resetcount := newRc }, { p₁.2 with resetcount := newRc })
    else p₁
  have hp₂ : PairCountersBounded M p₂ := by
    exact propagateReset_sync_preserves_counter_bound hp₁.1 hp₁.2
  simpa [p₁, oldRcA, oldRcB, p₂, PairCountersBounded] using
    And.intro
      (processAgent_preserves_counter_bound hEmax hDmax hp₂.1)
      (processAgent_preserves_counter_bound hEmax hDmax hp₂.2)

set_option maxHeartbeats 800000 in
private theorem rankDeltaOSSR_preserves_counter_bound
    {n Rmax Emax Dmax M : ℕ} {hn : 0 < n} {a b : AgentState n}
    (hRmax : Rmax ≤ M) (hEmax : Emax ≤ M) (hDmax : Dmax ≤ M)
    (hTwo : 2 ≤ M)
    (ha : AgentCountersBounded M a) (hb : AgentCountersBounded M b) :
    AgentCountersBounded M (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1 ∧
    AgentCountersBounded M (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2 := by
  by_cases hReset : a.role = .Resetting ∨ b.role = .Resetting
  · simp [rankDeltaOSSR, hReset]
    have hpr := propagateReset_preserves_counter_bound (hn := hn) hEmax hDmax ha hb
    split_ifs <;> simp_all [AgentCountersBounded]
  · simp [rankDeltaOSSR, hReset]
    repeat' split_ifs <;> simp_all [AgentCountersBounded] <;> omega

set_option maxHeartbeats 800000 in
private theorem phase4_propagate_preserves_counter_bound
    {n Rmax M : ℕ} {a b : AgentState n}
    (hRmax : Rmax ≤ M)
    (ha : AgentCountersBounded M a) (hb : AgentCountersBounded M b) :
    AgentCountersBounded M (phase4_propagate n Rmax a b).1 ∧
    AgentCountersBounded M (phase4_propagate n Rmax a b).2 := by
  unfold phase4_propagate
  by_cases haMed : a.rank.val + 1 = ceilHalf n
  · by_cases hbLast : b.rank.val + 1 = n
    · by_cases hReset :
        ({ a with timer := a.timer - 1 } : AgentState n).timer = 0 ∧
          ({ a with timer := a.timer - 1 } : AgentState n).answer ≠ b.answer
      · simp [haMed, hbLast, hReset, AgentCountersBounded] at * <;> omega
      · simp [haMed, hbLast, hReset, AgentCountersBounded] at * <;> omega
    · by_cases hReset : a.timer = 0 ∧ a.answer ≠ b.answer
      · simp [haMed, hbLast, hReset, AgentCountersBounded] at * <;> omega
      · simp [haMed, hbLast, hReset, AgentCountersBounded] at * <;> omega
  · by_cases hbMed : b.rank.val + 1 = ceilHalf n
    · by_cases haLast : a.rank.val + 1 = n
      · by_cases hReset :
          ({ b with timer := b.timer - 1 } : AgentState n).timer = 0 ∧
            ({ b with timer := b.timer - 1 } : AgentState n).answer ≠ a.answer
        · have hn_ne_ceil : n ≠ ceilHalf n := by
            intro h
            exact haMed (by omega)
          simp [hn_ne_ceil, hbMed, haLast, hReset, AgentCountersBounded] at * <;>
            omega
        · have hn_ne_ceil : n ≠ ceilHalf n := by
            intro h
            exact haMed (by omega)
          simp [hn_ne_ceil, hbMed, haLast, hReset, AgentCountersBounded] at * <;>
            omega
      · by_cases hReset : b.timer = 0 ∧ b.answer ≠ a.answer
        · simp [haMed, hbMed, haLast, hReset, AgentCountersBounded] at * <;> omega
        · simp [haMed, hbMed, haLast, hReset, AgentCountersBounded] at * <;> omega
    · simp [haMed, hbMed, AgentCountersBounded] at * <;> omega

private theorem phase4_swap_preserves_counter_bound
    {n M : ℕ} {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : AgentCountersBounded M a) (hb : AgentCountersBounded M b) :
    AgentCountersBounded M (phase4_swap a b x₀ x₁).1 ∧
    AgentCountersBounded M (phase4_swap a b x₀ x₁).2 := by
  unfold phase4_swap
  split_ifs <;> simp_all [AgentCountersBounded]

private theorem phase4_decide_preserves_counter_bound
    {n M : ℕ} {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : AgentCountersBounded M a) (hb : AgentCountersBounded M b) :
    AgentCountersBounded M (phase4_decide n a b x₀ x₁).1 ∧
    AgentCountersBounded M (phase4_decide n a b x₀ x₁).2 := by
  unfold phase4_decide
  repeat' split_ifs <;> simp_all [AgentCountersBounded]

private theorem transitionPEM_phase4_preserves_counter_bound
    {n Rmax M : ℕ} {a : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (hRmax : Rmax ≤ M)
    (ha : AgentCountersBounded M a.1) (hb : AgentCountersBounded M a.2) :
    AgentCountersBounded M (transitionPEM_phase4 n Rmax a x₀ x₁).1 ∧
    AgentCountersBounded M (transitionPEM_phase4 n Rmax a x₀ x₁).2 := by
  by_cases hSettled : a.1.role = .Settled ∧ a.2.role = .Settled
  · let sw := phase4_swap a.1 a.2 x₀ x₁
    have hsw : AgentCountersBounded M sw.1 ∧ AgentCountersBounded M sw.2 :=
      phase4_swap_preserves_counter_bound (x₀ := x₀) (x₁ := x₁) ha hb
    let dec := phase4_decide n sw.1 sw.2 x₀ x₁
    have hdec : AgentCountersBounded M dec.1 ∧ AgentCountersBounded M dec.2 :=
      phase4_decide_preserves_counter_bound (x₀ := x₀) (x₁ := x₁) hsw.1 hsw.2
    have hprop :
        AgentCountersBounded M (phase4_propagate n Rmax dec.1 dec.2).1 ∧
        AgentCountersBounded M (phase4_propagate n Rmax dec.1 dec.2).2 :=
      phase4_propagate_preserves_counter_bound hRmax hdec.1 hdec.2
    simpa [transitionPEM_phase4, hSettled, sw, dec] using hprop
  · simpa [transitionPEM_phase4, hSettled] using And.intro ha hb

set_option maxHeartbeats 800000 in
private theorem transitionPEM_prePhase4_preserves_counter_bound
    {n trank M : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hTimer : 7 * (trank + 4) ≤ M)
    (hRankDelta :
      AgentCountersBounded M (rankDelta (s₀, s₁)).1 ∧
      AgentCountersBounded M (rankDelta (s₀, s₁)).2) :
    AgentCountersBounded M
        (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).1 ∧
      AgentCountersBounded M
        (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).2 := by
  unfold transitionPEM_prePhase4
  rcases hrd : rankDelta (s₀, s₁) with ⟨r₀, r₁⟩
  simp [hrd] at hRankDelta ⊢
  repeat' split_ifs <;> simp_all [AgentCountersBounded] <;> omega

set_option maxHeartbeats 800000 in
private theorem transitionPEM_preserves_counter_bound
    {n Rmax Emax Dmax M : ℕ} {hn : 0 < n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hTimer : 7 * (Rmax + 4) ≤ M)
    (hRmax : Rmax ≤ M) (hEmax : Emax ≤ M) (hDmax : Dmax ≤ M)
    (hTwo : 2 ≤ M)
    (hs₀ : AgentCountersBounded M s₀) (hs₁ : AgentCountersBounded M s₁) :
    AgentCountersBounded M
        ((PEMProtocolCoupled n Rmax Emax Dmax hn).δ ((s₀, x₀), (s₁, x₁))).1 ∧
      AgentCountersBounded M
        ((PEMProtocolCoupled n Rmax Emax Dmax hn).δ ((s₀, x₀), (s₁, x₁))).2 := by
  have hrd :=
    rankDeltaOSSR_preserves_counter_bound (hn := hn)
      hRmax hEmax hDmax hTwo hs₀ hs₁
  have hpre :=
    transitionPEM_prePhase4_preserves_counter_bound
      (x₀ := x₀) (x₁ := x₁) hTimer hrd
  simpa [PEMProtocolCoupled, protocolPEM, transitionPEM] using
    transitionPEM_phase4_preserves_counter_bound
      (x₀ := x₀) (x₁ := x₁) hRmax hpre.1 hpre.2

/-- Protocol execution preserves bounded counters: if all counters are
initially bounded by `7 * (Rmax + 4) + Emax + Dmax`, they stay bounded
after any interaction.  This is a protocol-specific invariant. -/
theorem PEMProtocolCoupled_preserves_bounded
    {n Rmax Emax Dmax : ℕ} (hn : 0 < n) :
    let M := 7 * (Rmax + 4) + Emax + Dmax
    ∀ C : Config (AgentState n) Opinion n,
      IsBoundedConfig M C →
      ∀ i j : Fin n,
        IsBoundedConfig M (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn) i j) := by
  classical
  change ∀ C : Config (AgentState n) Opinion n,
      IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C →
      ∀ i j : Fin n,
        IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax)
          (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn) i j)
  intro C hC i j μ
  let M := 7 * (Rmax + 4) + Emax + Dmax
  have hTimer : 7 * (Rmax + 4) ≤ M := by omega
  have hRmaxM : Rmax ≤ M := by omega
  have hEmaxM : Emax ≤ M := by omega
  have hDmaxM : Dmax ≤ M := by omega
  have hTwo : 2 ≤ M := by omega
  have hi : AgentCountersBounded M (C i).1 := hC i
  have hj : AgentCountersBounded M (C j).1 := hC j
  by_cases hij : i = j
  · subst j
    simpa [Config.step, AgentCountersBounded, IsBoundedConfig] using hC μ
  · by_cases hμi : μ = i
    · subst μ
      have hpair :=
        transitionPEM_preserves_counter_bound
          (hn := hn) (x₀ := (C i).2) (x₁ := (C j).2)
          hTimer hRmaxM hEmaxM hDmaxM hTwo hi hj
      simpa [Config.step, hij, AgentCountersBounded, IsBoundedConfig]
        using hpair.1
    · by_cases hμj : μ = j
      · subst μ
        have hpair :=
          transitionPEM_preserves_counter_bound
            (hn := hn) (x₀ := (C i).2) (x₁ := (C j).2)
            hTimer hRmaxM hEmaxM hDmaxM hTwo hi hj
        simpa [Config.step, hij, hμi, AgentCountersBounded, IsBoundedConfig]
          using hpair.2
      · simpa [Config.step, hij, hμi, hμj, AgentCountersBounded, IsBoundedConfig]
          using hC μ

private def AgentTimerBounded (K : ℕ) (s : AgentState n) : Prop :=
  s.timer ≤ K

private def PairTimerBounded (K : ℕ) (p : AgentState n × AgentState n) : Prop :=
  AgentTimerBounded K p.1 ∧ AgentTimerBounded K p.2

private theorem resetOSSR_preserves_timer_bound
    {n Emax K : ℕ} {hn : 0 < n} {s : AgentState n}
    (hs : AgentTimerBounded K s) :
    AgentTimerBounded K (resetOSSR Emax hn s) := by
  rcases s with ⟨role, rank, leader, resetcount, answer, timer, children,
    errorcount, delaytimer⟩
  cases leader <;> simpa [AgentTimerBounded, resetOSSR] using hs

private theorem processAgent_preserves_timer_bound
    {n Emax Dmax K : ℕ} {hn : 0 < n} {s : AgentState n}
    {oldRc : ℕ} {partnerResetting : Bool}
    (hs : AgentTimerBounded K s) :
    AgentTimerBounded K
      (processAgent Emax Dmax hn s oldRc partnerResetting) := by
  unfold processAgent
  by_cases hmain : s.role = .Resetting ∧ s.resetcount = 0
  · rw [if_pos hmain]
    by_cases hold : 0 < oldRc
    · rw [if_pos hold]
      by_cases hfire :
          ({s with delaytimer := Dmax} : AgentState n).delaytimer = 0 ∨
            !partnerResetting
      · rw [if_pos hfire]
        exact resetOSSR_preserves_timer_bound (s := {s with delaytimer := Dmax}) hs
      · rw [if_neg hfire]
        exact hs
    · rw [if_neg hold]
      by_cases hfire :
          ({s with delaytimer := s.delaytimer - 1} : AgentState n).delaytimer = 0 ∨
            !partnerResetting
      · rw [if_pos hfire]
        exact resetOSSR_preserves_timer_bound
          (s := {s with delaytimer := s.delaytimer - 1}) hs
      · rw [if_neg hfire]
        exact hs
  · rw [if_neg hmain]
    exact hs

private theorem propagateReset_recruit_preserves_timer_bound
    {n Emax Dmax K : ℕ} {a b : AgentState n}
    (ha : AgentTimerBounded K a) (hb : AgentTimerBounded K b) :
    PairTimerBounded K
      (if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
        (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
      else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
        ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
      else (a, b)) := by
  unfold PairTimerBounded
  split_ifs <;> simp_all [AgentTimerBounded]

private theorem propagateReset_sync_preserves_timer_bound
    {n K : ℕ} {a b : AgentState n}
    (ha : AgentTimerBounded K a) (hb : AgentTimerBounded K b) :
    PairTimerBounded K
      (if a.role = .Resetting ∧ b.role = .Resetting then
        let newRc := max (a.resetcount - 1) (b.resetcount - 1)
        ({ a with resetcount := newRc }, { b with resetcount := newRc })
      else (a, b)) := by
  unfold PairTimerBounded
  split_ifs <;> simp_all [AgentTimerBounded]

private theorem propagateReset_preserves_timer_bound
    {n Emax Dmax K : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : AgentTimerBounded K a) (hb : AgentTimerBounded K b) :
    AgentTimerBounded K (propagateReset Emax Dmax hn a b).1 ∧
    AgentTimerBounded K (propagateReset Emax Dmax hn a b).2 := by
  unfold propagateReset
  let p₁ :=
    if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
      (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
    else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
      ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
    else (a, b)
  have hp₁ : PairTimerBounded K p₁ := by
    simpa [p₁] using
      propagateReset_recruit_preserves_timer_bound
        (Emax := Emax) (Dmax := Dmax) ha hb
  let oldRcA := p₁.1.resetcount
  let oldRcB := p₁.2.resetcount
  let p₂ :=
    if p₁.1.role = .Resetting ∧ p₁.2.role = .Resetting then
      let newRc := max (p₁.1.resetcount - 1) (p₁.2.resetcount - 1)
      ({ p₁.1 with resetcount := newRc }, { p₁.2 with resetcount := newRc })
    else p₁
  have hp₂ : PairTimerBounded K p₂ := by
    exact propagateReset_sync_preserves_timer_bound hp₁.1 hp₁.2
  simpa [p₁, oldRcA, oldRcB, p₂, PairTimerBounded] using
    And.intro
      (processAgent_preserves_timer_bound (Emax := Emax) (Dmax := Dmax) (hn := hn) hp₂.1)
      (processAgent_preserves_timer_bound (Emax := Emax) (Dmax := Dmax) (hn := hn) hp₂.2)

set_option maxHeartbeats 800000 in
private theorem rankDeltaOSSR_preserves_timer_bound
    {n Rmax Emax Dmax K : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : AgentTimerBounded K a) (hb : AgentTimerBounded K b) :
    AgentTimerBounded K (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1 ∧
    AgentTimerBounded K (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2 := by
  unfold rankDeltaOSSR
  by_cases hReset : a.role = .Resetting ∨ b.role = .Resetting
  · simp [hReset]
    have hpr :=
      propagateReset_preserves_timer_bound
        (Emax := Emax) (Dmax := Dmax) (hn := hn) ha hb
    split_ifs <;> simp_all [AgentTimerBounded]
  · simp [hReset]
    repeat' split_ifs <;> simp_all [AgentTimerBounded]

set_option maxHeartbeats 800000 in
private theorem transitionPEM_prePhase4_preserves_protocol_timer_bound
    {n trank K : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hK : 7 * (trank + 4) ≤ K)
    (hRankDelta :
      AgentTimerBounded K (rankDelta (s₀, s₁)).1 ∧
      AgentTimerBounded K (rankDelta (s₀, s₁)).2) :
    AgentTimerBounded K
        (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).1 ∧
      AgentTimerBounded K
        (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).2 := by
  unfold transitionPEM_prePhase4
  rcases hrd : rankDelta (s₀, s₁) with ⟨r₀, r₁⟩
  simp [hrd] at hRankDelta ⊢
  repeat' split_ifs <;> simp_all [AgentTimerBounded] <;> omega

private theorem phase4_swap_preserves_timer_bound
    {n K : ℕ} {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : AgentTimerBounded K a) (hb : AgentTimerBounded K b) :
    AgentTimerBounded K (phase4_swap a b x₀ x₁).1 ∧
    AgentTimerBounded K (phase4_swap a b x₀ x₁).2 := by
  unfold phase4_swap
  split_ifs <;> simp_all [AgentTimerBounded]

private theorem phase4_decide_preserves_timer_bound
    {n K : ℕ} {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : AgentTimerBounded K a) (hb : AgentTimerBounded K b) :
    AgentTimerBounded K (phase4_decide n a b x₀ x₁).1 ∧
    AgentTimerBounded K (phase4_decide n a b x₀ x₁).2 := by
  unfold phase4_decide
  repeat' split_ifs <;> simp_all [AgentTimerBounded]

set_option maxHeartbeats 800000 in
private theorem phase4_propagate_preserves_timer_bound
    {n Rmax K : ℕ} {a b : AgentState n}
    (ha : AgentTimerBounded K a) (hb : AgentTimerBounded K b) :
    AgentTimerBounded K (phase4_propagate n Rmax a b).1 ∧
    AgentTimerBounded K (phase4_propagate n Rmax a b).2 := by
  unfold phase4_propagate
  by_cases haMed : a.rank.val + 1 = ceilHalf n
  · by_cases hbLast : b.rank.val + 1 = n
    · by_cases hReset :
        ({ a with timer := a.timer - 1 } : AgentState n).timer = 0 ∧
          ({ a with timer := a.timer - 1 } : AgentState n).answer ≠ b.answer
      · simp [haMed, hbLast, hReset, AgentTimerBounded] at * <;> omega
      · simp [haMed, hbLast, hReset, AgentTimerBounded] at * <;> omega
    · by_cases hReset : a.timer = 0 ∧ a.answer ≠ b.answer
      · simp [haMed, hbLast, hReset, AgentTimerBounded] at * <;> omega
      · simp [haMed, hbLast, hReset, AgentTimerBounded] at * <;> omega
  · by_cases hbMed : b.rank.val + 1 = ceilHalf n
    · by_cases haLast : a.rank.val + 1 = n
      · by_cases hReset :
          ({ b with timer := b.timer - 1 } : AgentState n).timer = 0 ∧
            ({ b with timer := b.timer - 1 } : AgentState n).answer ≠ a.answer
        · have hn_ne_ceil : n ≠ ceilHalf n := by
            intro h
            exact haMed (by omega)
          simp [hn_ne_ceil, hbMed, haLast, hReset, AgentTimerBounded] at * <;>
            omega
        · have hn_ne_ceil : n ≠ ceilHalf n := by
            intro h
            exact haMed (by omega)
          simp [hn_ne_ceil, hbMed, haLast, hReset, AgentTimerBounded] at * <;>
            omega
      · by_cases hReset : b.timer = 0 ∧ b.answer ≠ a.answer
        · simp [haMed, hbMed, haLast, hReset, AgentTimerBounded] at * <;> omega
        · simp [haMed, hbMed, haLast, hReset, AgentTimerBounded] at * <;> omega
    · simp [haMed, hbMed, AgentTimerBounded] at * <;> omega

private theorem transitionPEM_phase4_preserves_timer_bound
    {n Rmax K : ℕ} {a : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (ha : AgentTimerBounded K a.1) (hb : AgentTimerBounded K a.2) :
    AgentTimerBounded K (transitionPEM_phase4 n Rmax a x₀ x₁).1 ∧
    AgentTimerBounded K (transitionPEM_phase4 n Rmax a x₀ x₁).2 := by
  by_cases hSettled : a.1.role = .Settled ∧ a.2.role = .Settled
  · let sw := phase4_swap a.1 a.2 x₀ x₁
    have hsw : AgentTimerBounded K sw.1 ∧ AgentTimerBounded K sw.2 :=
      phase4_swap_preserves_timer_bound (x₀ := x₀) (x₁ := x₁) ha hb
    let dec := phase4_decide n sw.1 sw.2 x₀ x₁
    have hdec : AgentTimerBounded K dec.1 ∧ AgentTimerBounded K dec.2 :=
      phase4_decide_preserves_timer_bound (x₀ := x₀) (x₁ := x₁) hsw.1 hsw.2
    have hprop :
        AgentTimerBounded K (phase4_propagate n Rmax dec.1 dec.2).1 ∧
        AgentTimerBounded K (phase4_propagate n Rmax dec.1 dec.2).2 :=
      phase4_propagate_preserves_timer_bound hdec.1 hdec.2
    simpa [transitionPEM_phase4, hSettled, sw, dec] using hprop
  · simpa [transitionPEM_phase4, hSettled] using And.intro ha hb

private theorem transitionPEM_preserves_protocol_timer_bound
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hs₀ : AgentTimerBounded (7 * (Rmax + 4)) s₀)
    (hs₁ : AgentTimerBounded (7 * (Rmax + 4)) s₁) :
      AgentTimerBounded (7 * (Rmax + 4))
          ((PEMProtocolCoupled n Rmax Emax Dmax hn).δ ((s₀, x₀), (s₁, x₁))).1 ∧
        AgentTimerBounded (7 * (Rmax + 4))
          ((PEMProtocolCoupled n Rmax Emax Dmax hn).δ ((s₀, x₀), (s₁, x₁))).2 := by
  have hrd :=
    rankDeltaOSSR_preserves_timer_bound (hn := hn)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hs₀ hs₁
  have hpre :=
    transitionPEM_prePhase4_preserves_protocol_timer_bound
      (trank := Rmax) (K := 7 * (Rmax + 4))
      (x₀ := x₀) (x₁ := x₁) (by omega) hrd
  simpa [PEMProtocolCoupled, protocolPEM, transitionPEM] using
    transitionPEM_phase4_preserves_timer_bound
      (x₀ := x₀) (x₁ := x₁) hpre.1 hpre.2

theorem PEMProtocolCoupled_preserves_timer_bounded
    {n Rmax Emax Dmax : ℕ} (hn : 0 < n) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
      ∀ i j : Fin n,
        IsTimerBoundedConfig (7 * (Rmax + 4))
          (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn) i j) := by
  intro C hC i j μ
  have hi : AgentTimerBounded (7 * (Rmax + 4)) (C i).1 := hC i
  have hj : AgentTimerBounded (7 * (Rmax + 4)) (C j).1 := hC j
  by_cases hij : i = j
  · subst j
    simpa [Config.step, AgentTimerBounded, IsTimerBoundedConfig] using hC μ
  · by_cases hμi : μ = i
    · subst μ
      have hpair :=
        transitionPEM_preserves_protocol_timer_bound
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          (hn := hn) (x₀ := (C i).2) (x₁ := (C j).2) hi hj
      simpa [Config.step, hij, AgentTimerBounded, IsTimerBoundedConfig]
        using hpair.1
    · by_cases hμj : μ = j
      · subst μ
        have hpair :=
          transitionPEM_preserves_protocol_timer_bound
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (hn := hn) (x₀ := (C i).2) (x₁ := (C j).2) hi hj
        simpa [Config.step, hij, hμi, AgentTimerBounded, IsTimerBoundedConfig]
          using hpair.2
      · simpa [Config.step, hij, hμi, hμj, AgentTimerBounded, IsTimerBoundedConfig]
          using hC μ

theorem PEMProtocolCoupled_consensus_probReached_eq_one
    {n Rmax Emax Dmax : ℕ} [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hC : IsConsensusConfig C) (t : ℕ) :
    Probability.probReached (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
      IsConsensusConfig t = 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hfix : RankDeltaSettledFix (rankDeltaOSSR Rmax Emax Dmax hn0) :=
    rankDeltaOSSR_satisfies_fix
  have hstep : ∀ C' : Config (AgentState n) Opinion n,
      IsConsensusConfig C' → ∀ i j : Fin n,
        IsConsensusConfig (C'.step P i j) := by
    intro C' hC' i j
    simpa [P, PEMProtocolCoupled, PEMProtocol] using step_preserves_consensus hfix hC' i j
  simp only [Probability.probReached]
  have hsupport :=
    Probability.nthStepDist_support_inv P hn2 C IsConsensusConfig hC hstep t
  conv_lhs => arg 1; ext D; rw [show (if IsConsensusConfig D then
      (Probability.nthStepDist P hn2 C t) D else 0) =
      (Probability.nthStepDist P hn2 C t) D from by
        by_cases hD : IsConsensusConfig D
        · rw [if_pos hD]
        · have hDzero : (Probability.nthStepDist P hn2 C t) D = 0 :=
            (PMF.apply_eq_zero_iff _ _).mpr (fun h => hD (hsupport D h))
          rw [if_neg hD, hDzero]]
  exact PMF.tsum_coe _

theorem PEM_decision_phase_hypothesis_of_live_branch
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSdecTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n)
    (hLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianTimerAtLeast 28 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((8 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n)) :
      ∀ C : Config (AgentState n) Opinion n,
        InTswap28SswapTimerBounded (7 * (Rmax + 4)) C →
          ((8 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n) := by
  classical
  intro C hC
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  rcases hC with ⟨hSwap, hTimer, hTimerUpper⟩ | hCon
  · by_cases hCon' : IsConsensusConfig C
    · calc ((8 : ENNReal)⁻¹) ≤ 1 := by norm_num
        _ = Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
              IsConsensusConfig (4 * n * n) :=
            (PEMProtocolCoupled_consensus_probReached_eq_one
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn2 hn0 hCon' (4 * n * n)).symm
        _ ≤ Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n) :=
            Probability.probReached_mono_goal
              (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C IsConsensusConfig
              (InSdecTimerBounded (7 * (Rmax + 4))) (fun D hD => Or.inr hD) _
    · exact hLive C hSwap hTimer hTimerUpper hCon'
  · calc ((8 : ENNReal)⁻¹) ≤ 1 := by norm_num
      _ = Probability.probReached
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
            IsConsensusConfig (4 * n * n) :=
          (PEMProtocolCoupled_consensus_probReached_eq_one
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn2 hn0 hCon (4 * n * n)).symm
      _ ≤ Probability.probReached
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
            (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n) :=
          Probability.probReached_mono_goal
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C IsConsensusConfig
            (InSdecTimerBounded (7 * (Rmax + 4))) (fun D hD => Or.inr hD) _

theorem PEM_propagation_phase_hypothesis_of_live_branch
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n)
    (hLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianAnswerCorrect C →
        MedianTimerAtLeast 1 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n)) :
      ∀ C : Config (AgentState n) Opinion n,
        InSdecTimerBounded (7 * (Rmax + 4)) C →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n) := by
  classical
  intro C hC
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  rcases hC with ⟨hSwap, hAns, hTimer, hTimerUpper⟩ | hCon
  · by_cases hCon' : IsConsensusConfig C
    · calc ((1280 : ENNReal)⁻¹) ≤ 1 := by norm_num
        _ = Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
              IsConsensusConfig (20 * Rmax * n * n) :=
            (PEMProtocolCoupled_consensus_probReached_eq_one
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn2 hn0 hCon' (20 * Rmax * n * n)).symm
    · exact hLive C hSwap hAns hTimer hTimerUpper hCon'
  · calc ((1280 : ENNReal)⁻¹) ≤ 1 := by norm_num
      _ = Probability.probReached
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
            IsConsensusConfig (20 * Rmax * n * n) :=
          (PEMProtocolCoupled_consensus_probReached_eq_one
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn2 hn0 hCon (20 * Rmax * n * n)).symm

/-- Phase-B variable-descent expectation up to either completing the swap phase
or leaving `Srank`.  The exit branch is necessary because the coupled PEM
transition may trigger a reset from an arbitrary `InSrank` state; the pure
`InSswap` hitting statement needs a separate timer/no-reset hypothesis or a
restart through Phase A. -/
theorem PEM_swap_phase_expected_until_swap_or_exit_le_sum
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    Probability.expectedHittingTime
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∨ ¬ InSrank D) ≤
      ∑ k ∈ Finset.range (wrongLowBCount C),
        ((((k + 1) * (k + 1) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∨ ¬ InSrank D
  let pRate : ℕ → ENNReal := fun k =>
    (((k * k : ℕ) : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
  have hRankFix : RankDeltaSettledFix (rankDeltaOSSR Rmax Emax Dmax hn0) :=
    rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn0)
  have hZeroGoal : ∀ D : Config (AgentState n) Opinion n,
      InSrank D → wrongLowBCount D = 0 → Goal D := by
    intro D hD hzero
    exact Or.inl (InSswap_of_InSrank_of_wrongLowBCount_zero hD hzero)
  have hInvStep : ∀ D : Config (AgentState n) Opinion n, InSrank D → ¬ Goal D →
      ∀ i j : Fin n, InSrank (D.step P i j) ∨ Goal (D.step P i j) := by
    intro D _hD _hGoalD i j
    by_cases h' : InSrank (D.step P i j)
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')
  have hNonincrease : ∀ D : Config (AgentState n) Opinion n, InSrank D → ¬ Goal D →
      ∀ i j : Fin n, wrongLowBCount (D.step P i j) ≤ wrongLowBCount D := by
    intro D hD _hGoalD i j
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      (wrongLowBCount_step_le_of_InSrank
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        hRankFix hD i j)
  have hp : ∀ k : ℕ, 0 < k →
      ∀ D : Config (AgentState n) Opinion n, InSrank D → wrongLowBCount D = k →
        pRate k ≤
          Probability.ProbHitWithin P hn2 D
            (fun E => Goal E ∨ (InSrank E ∧ wrongLowBCount E < k)) 1 := by
    intro k hk D hD hφ
    have hrate_le :
        pRate k ≤
          (((wrongLowBCount D * wrongLowBCount D : ℕ) : ENNReal) *
            ((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
      dsimp [pRate]
      rw [← hφ]
    have hdescent :
        (((wrongLowBCount D * wrongLowBCount D : ℕ) : ENNReal) *
            ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 D
            (fun E => wrongLowBCount E < wrongLowBCount D) 1 := by
      simpa [P] using
        (PEM_swap_phase_wrongLowB_square_descent_prob_lower_bound
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hD)
    refine hrate_le.trans (hdescent.trans ?_)
    apply Probability.ProbHitWithin_mono_goal P hn2 D
    intro E hlt
    by_cases hE : InSrank E
    · exact Or.inr ⟨hE, by simpa [hφ] using hlt⟩
    · exact Or.inl (Or.inr hE)
  simpa [P, Goal, pRate] using
    (Probability.expectedHittingTime_le_of_variable_descent_until_goal
      P hn2 C Goal InSrank wrongLowBCount pRate hSrank
      hZeroGoal hInvStep hNonincrease hp)

/-! ### Ranking-phase stochastic bridge -/

/-- One binary-tree recruit step has at least the scheduler mass of one
ordered pair.

This is the stochastic wrapper around the deterministic
`heapPrefix_recruit_step_with_child_BCF`: while the ranking heap prefix is at
level `k < n`, an unsettled child and its heap parent form a concrete ordered
pair whose interaction advances the prefix to `k + 1`, preserving the median
timer side conditions needed by the later swap phase. -/
theorem PEM_heapPrefix_recruit_step_ProbHitWithin
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {k : ℕ} (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (C : Config (AgentState n) Opinion n)
    (hHeap : HeapPrefix C k) (hTimer : SettledMedianTimerStrong C) :
    (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D =>
          HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
            (k + 1 < n → SettledMedianTimerStrong D)) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
        (k + 1 < n → SettledMedianTimerStrong D)
  by_cases hGoalC : Goal C
  · have hp_le_one :
        (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤ 1 := by
      exact ENNReal.inv_le_one.mpr (by
        have hn_one : 1 ≤ n := by omega
        have hpred_one : 1 ≤ n - 1 := by omega
        exact_mod_cast (Nat.mul_le_mul hn_one hpred_one))
    calc
      (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤ 1 := hp_le_one
      _ = Probability.ProbHitWithin P hn2 C Goal 0 := by
        rw [Probability.ProbHitWithin, Probability.probHitBy_zero_of_goal P hn2 C Goal hGoalC]
      _ ≤ Probability.ProbHitWithin P hn2 C Goal 1 :=
        Probability.ProbHitWithin_mono_time P hn2 C Goal (by omega)
  · have hExistsUnsettled : ∃ u : Fin n, (C u).1.role = .Unsettled := by
      by_contra hnone
      push_neg at hnone
      have hall : ∀ w : Fin n, (C w).1.role = .Settled := by
        intro w
        rcases hHeap.2.2.2.1 w with hwS | hwU
        · exact hwS
        · exact False.elim (hnone w hwU)
      exact heapPrefix_no_unsettled_contradiction hk_lt hHeap hall
    obtain ⟨u, hu_unsettled⟩ := hExistsUnsettled
    obtain ⟨parent, hparent_settled, _hparent_children, _hvalid, _hrank,
        hstep⟩ :=
      heapPrefix_recruit_step_with_child_BCF
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hk_pos hk_lt C hHeap hTimer u hu_unsettled
    have hup : u ≠ parent := by
      intro h
      subst u
      rw [hparent_settled] at hu_unsettled
      cases hu_unsettled
    have hstepGoal : Goal (C.step P u parent) := by
      simpa [P, PEMProtocolCoupled, PEMProtocol, Goal, runPairs] using hstep
    simpa [P, Goal] using
      (Probability.ProbHitWithin_one_lower_bound_of_step
        (P := P) hn2 C Goal hGoalC hup hstepGoal)

/-- All unsettled agents in a heap-prefix configuration contribute distinct
successful recruit ordered pairs.

This is the rate form needed for the ranking expected-time bound: at heap
level `k`, every unsettled agent can be recruited by the unique heap parent of
rank `heapParent k`, so the one-step success probability is at least
`unsettledCount / (n(n-1))`. -/
theorem PEM_heapPrefix_recruit_step_mass_ProbHitWithin
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {k : ℕ} (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (C : Config (AgentState n) Opinion n)
    (hHeap : HeapPrefix C k) (hTimer : SettledMedianTimerStrong C) :
    ((unsettledCount C : ℕ) : ENNReal) *
        (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D =>
          HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
            (k + 1 < n → SettledMedianTimerStrong D)) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
        (k + 1 < n → SettledMedianTimerStrong D)
  by_cases hGoalC : Goal C
  · have hU_le_n : unsettledCount C ≤ n := by
      unfold unsettledCount
      calc
        (Finset.univ.filter fun w : Fin n => (C w).1.role == .Unsettled).card
            ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
        _ = n := by simp
    have hden_le : n ≤ n * (n - 1) := by
      have hpred_one : 1 ≤ n - 1 := by omega
      calc
        n = n * 1 := by omega
        _ ≤ n * (n - 1) := Nat.mul_le_mul_left n hpred_one
    have hmass_le_one :
        ((unsettledCount C : ℕ) : ENNReal) *
            (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤ 1 := by
      calc
        ((unsettledCount C : ℕ) : ENNReal) *
            (((n * (n - 1) : ℕ) : ENNReal)⁻¹)
            ≤ ((n : ℕ) : ENNReal) *
                (((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
              gcongr
        _ ≤ ((n * (n - 1) : ℕ) : ENNReal) *
                (((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
              gcongr
        _ ≤ 1 := by
              exact ENNReal.mul_inv_le_one ((n * (n - 1) : ℕ) : ENNReal)
    calc
      ((unsettledCount C : ℕ) : ENNReal) *
          (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤ 1 := hmass_le_one
      _ = Probability.ProbHitWithin P hn2 C Goal 0 := by
        rw [Probability.ProbHitWithin, Probability.probHitBy_zero_of_goal P hn2 C Goal hGoalC]
      _ ≤ Probability.ProbHitWithin P hn2 C Goal 1 :=
        Probability.ProbHitWithin_mono_time P hn2 C Goal (by omega)
  · let parentOf : Fin n → Fin n := fun u =>
      if hu : (C u).1.role = .Unsettled then
        Classical.choose
          (heapPrefix_recruit_step_with_child_BCF
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
            hk_pos hk_lt C hHeap hTimer u hu)
      else u
    have parentOf_spec : ∀ u : Fin n, (C u).1.role = .Unsettled →
        (C (parentOf u)).1.role = .Settled ∧
        (C (parentOf u)).1.children < 2 ∧
        2 * (C (parentOf u)).1.rank.val +
            (C (parentOf u)).1.children + 1 < n ∧
        2 * (C (parentOf u)).1.rank.val +
            (C (parentOf u)).1.children + 1 = k ∧
        (let C' := runPairs (protocolPEM n Rmax Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn0)) C [(u, parentOf u)]
         HeapPrefix C' (k + 1) ∧ SettledMedianTimerGood C' ∧
          (k + 1 < n → SettledMedianTimerStrong C')) := by
      intro u hu
      dsimp [parentOf]
      rw [dif_pos hu]
      exact Classical.choose_spec
        (heapPrefix_recruit_step_with_child_BCF
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
          hk_pos hk_lt C hHeap hTimer u hu)
    let U : Finset (Fin n) :=
      Finset.univ.filter fun u : Fin n => (C u).1.role == .Unsettled
    let S : Finset (Fin n × Fin n) := U.image fun u => (u, parentOf u)
    have hU_card : U.card = unsettledCount C := by
      rfl
    have hS_card : S.card = unsettledCount C := by
      dsimp [S]
      rw [Finset.card_image_of_injective]
      · exact hU_card
      · intro a b h
        exact congrArg Prod.fst h
    have hS_sub : S ⊆ Probability.OffDiagonalPairs n := by
      intro p hp
      dsimp [S] at hp
      obtain ⟨u, huU, rfl⟩ := Finset.mem_image.mp hp
      have hu_role : (C u).1.role = .Unsettled := by
        have hbool := (Finset.mem_filter.mp huU).2
        simpa using hbool
      have hspec := parentOf_spec u hu_role
      have hup : u ≠ parentOf u := by
        intro h
        rw [h] at hu_role
        rw [hspec.1] at hu_role
        cases hu_role
      exact (Probability.mem_offDiagonalPairs n (u, parentOf u)).mpr hup
    have hS_step : ∀ p ∈ S, Goal (C.step P p.1 p.2) := by
      intro p hp
      dsimp [S] at hp
      obtain ⟨u, huU, rfl⟩ := Finset.mem_image.mp hp
      have hu_role : (C u).1.role = .Unsettled := by
        have hbool := (Finset.mem_filter.mp huU).2
        simpa using hbool
      have hspec := parentOf_spec u hu_role
      have hstep := hspec.2.2.2.2
      simpa [P, PEMProtocolCoupled, PEMProtocol, Goal, runPairs] using hstep
    calc
      ((unsettledCount C : ℕ) : ENNReal) *
          (((n * (n - 1) : ℕ) : ENNReal)⁻¹)
          = Probability.pairSetMass n hn2 S := by
            rw [Probability.pairSetMass_eq_card_mul_inv_of_subset n hn2 S hS_sub]
            rw [hS_card]
      _ ≤ Probability.ProbHitWithin P hn2 C Goal 1 :=
        Probability.ProbHitWithin_one_lower_bound_of_pairSet
          P hn2 C Goal hGoalC S hS_sub hS_step

/-- In a `HeapPrefix C k` state, exactly the first `k` ranks are occupied by
settled agents and all remaining agents are unsettled.  This is the counting
bridge that turns the mass recruit bound into a level-dependent rate. -/
theorem HeapPrefix.unsettledCount_add_eq_n
    {n : ℕ} {C : Config (AgentState n) Opinion n} {k : ℕ}
    (hHeap : HeapPrefix C k) :
    k + unsettledCount C = n := by
  classical
  rcases hHeap with ⟨hk_le, hRankLt, hRankUnique, hRoles, _hChildren⟩
  let S : Finset (Fin n) :=
    Finset.univ.filter fun w : Fin n => (C w).1.role = .Settled
  let U : Finset (Fin n) :=
    Finset.univ.filter fun w : Fin n => (C w).1.role == .Unsettled
  have hSettledCard : S.card = k := by
    let rankOnSettled : {w : Fin n // w ∈ S} → Fin k := fun w =>
      ⟨(C w.1).1.rank.val, by
        have hw_settled : (C w.1).1.role = .Settled := by
          exact (Finset.mem_filter.mp w.2).2
        exact hRankLt w.1 hw_settled⟩
    have hBij : Function.Bijective rankOnSettled := by
      constructor
      · intro x y hxy
        apply Subtype.ext
        obtain ⟨z, _hz, hz_unique⟩ :=
          hRankUnique (rankOnSettled x).val (rankOnSettled x).isLt
        have hxz : x.1 = z := by
          apply hz_unique
          constructor
          · exact (Finset.mem_filter.mp x.2).2
          · rfl
        have hyz : y.1 = z := by
          apply hz_unique
          constructor
          · exact (Finset.mem_filter.mp y.2).2
          · exact congrArg Fin.val hxy |>.symm
        exact hxz.trans hyz.symm
      · intro r
        obtain ⟨w, hw, _hw_unique⟩ := hRankUnique r.val r.isLt
        have hwS : w ∈ S := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw.1⟩
        exact ⟨⟨w, hwS⟩, Fin.ext hw.2⟩
    have hCardSubtype :
        Fintype.card {w : Fin n // w ∈ S} = Fintype.card (Fin k) :=
      Fintype.card_congr (Equiv.ofBijective rankOnSettled hBij)
    have hSubtypeCard : Fintype.card {w : Fin n // w ∈ S} = S.card :=
      Fintype.card_of_subtype S (fun _ => Iff.rfl)
    rw [← hSubtypeCard, hCardSubtype]
    simp
  have hUCard : U.card = unsettledCount C := by
    rfl
  have hDisjoint : Disjoint S U := by
    rw [Finset.disjoint_left]
    intro w hwS hwU
    have hSrole : (C w).1.role = .Settled := (Finset.mem_filter.mp hwS).2
    have hUrole : (C w).1.role = .Unsettled := by
      simpa using (Finset.mem_filter.mp hwU).2
    rw [hSrole] at hUrole
    cases hUrole
  have hUnion : S ∪ U = (Finset.univ : Finset (Fin n)) := by
    ext w
    constructor
    · intro _hw
      exact Finset.mem_univ w
    · intro _hw
      rcases hRoles w with hSettled | hUnsettled
      · exact Finset.mem_union_left U
          (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hSettled⟩)
      · exact Finset.mem_union_right S
          (Finset.mem_filter.mpr ⟨Finset.mem_univ w, by simpa [hUnsettled]⟩)
  have htotal : n = S.card + U.card := by
    calc
      n = (Finset.univ : Finset (Fin n)).card := by simp
      _ = (S ∪ U).card := by rw [hUnion]
      _ = S.card + U.card := Finset.card_union_of_disjoint hDisjoint
  omega

/-- Level-rate form of the heap-prefix recruit bound.  At prefix level `k`,
there are exactly `n-k` unsettled agents, hence that many successful recruit
edges. -/
theorem PEM_heapPrefix_recruit_step_level_ProbHitWithin
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {k : ℕ} (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (C : Config (AgentState n) Opinion n)
    (hHeap : HeapPrefix C k) (hTimer : SettledMedianTimerStrong C) :
    (((n - k : ℕ) : ENNReal) *
        (((n * (n - 1) : ℕ) : ENNReal)⁻¹)) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D =>
          HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
            (k + 1 < n → SettledMedianTimerStrong D)) 1 := by
  classical
  have hcount : unsettledCount C = n - k := by
    have hsum := HeapPrefix.unsettledCount_add_eq_n (C := C) (k := k) hHeap
    omega
  simpa [hcount] using
    (PEM_heapPrefix_recruit_step_mass_ProbHitWithin
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hk_pos hk_lt C hHeap hTimer)

/-- Expected time to advance one heap-prefix level or leave the level,
using the full mass of all unsettled recruitable agents. -/
theorem PEM_heapPrefix_recruit_step_or_exit_expected_le_level
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {k : ℕ} (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (C : Config (AgentState n) Opinion n)
    (hHeap : HeapPrefix C k) (hTimer : SettledMedianTimerStrong C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
      (fun D =>
        (HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
            (k + 1 < n → SettledMedianTimerStrong D)) ∨
          ¬ (HeapPrefix D k ∧ SettledMedianTimerStrong D)) ≤
      ((((n - k : ℕ) : ENNReal) *
          (((n * (n - 1) : ℕ) : ENNReal)⁻¹))⁻¹) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Region : Config (AgentState n) Opinion n → Prop :=
    fun D => HeapPrefix D k ∧ SettledMedianTimerStrong D
  let Next : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
        (k + 1 < n → SettledMedianTimerStrong D)
  have hRegion : Region C := ⟨hHeap, hTimer⟩
  by_cases hNextC : Next C
  · rw [Probability.expectedHittingTime_eq_zero_of_goal
        P hn2 C (fun D => Next D ∨ ¬ Region D) (Or.inl hNextC)]
    exact zero_le _
  · apply Probability.expectedHittingTime_le_inv_of_local_one_lower_bound
      (P := P) (hn := hn2) (C₀ := C)
      (Region := Region) (Goal := Next)
      (p := (((n - k : ℕ) : ENNReal) *
        (((n * (n - 1) : ℕ) : ENNReal)⁻¹)))
    · exact hRegion
    · exact hNextC
    · intro D hRegionD _hNextD
      have hbase :
          (((n - k : ℕ) : ENNReal) *
              (((n * (n - 1) : ℕ) : ENNReal)⁻¹)) ≤
            Probability.ProbHitWithin P hn2 D Next 1 := by
        simpa [P, Next] using
          (PEM_heapPrefix_recruit_step_level_ProbHitWithin
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn2 hn0 hk_pos hk_lt D hRegionD.1 hRegionD.2)
      exact hbase.trans
        (Probability.ProbHitWithin_mono_goal P hn2 D Next
          (fun E => Next E ∨ ¬ Region E) (fun E hE => Or.inl hE) 1)

/-- Expected time to either advance one heap-prefix level or leave the current
heap-prefix region.

The exit disjunct is deliberate: arbitrary scheduler interactions can touch
unsettled agents and error counters, so the honest local statement does not
pretend the heap-prefix invariant is globally preserved.  The theorem says
that while the current heap-prefix state is live, one concrete recruit pair
gives a geometric `n(n-1)` sequential-time bound for either making the intended
advance or detecting that the region has been left. -/
theorem PEM_heapPrefix_recruit_step_or_exit_expected_le
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {k : ℕ} (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (C : Config (AgentState n) Opinion n)
    (hHeap : HeapPrefix C k) (hTimer : SettledMedianTimerStrong C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
      (fun D =>
        (HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
            (k + 1 < n → SettledMedianTimerStrong D)) ∨
          ¬ (HeapPrefix D k ∧ SettledMedianTimerStrong D)) ≤
      ((n * (n - 1) : ℕ) : ENNReal) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Region : Config (AgentState n) Opinion n → Prop :=
    fun D => HeapPrefix D k ∧ SettledMedianTimerStrong D
  let Next : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
        (k + 1 < n → SettledMedianTimerStrong D)
  have hRegion : Region C := ⟨hHeap, hTimer⟩
  by_cases hNextC : Next C
  · rw [Probability.expectedHittingTime_eq_zero_of_goal
        P hn2 C (fun D => Next D ∨ ¬ Region D) (Or.inl hNextC)]
    exact zero_le _
  · have hraw :
        Probability.expectedHittingTime P hn2 C
          (fun D => Next D ∨ ¬ Region D) ≤
        ((((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹) := by
      apply Probability.expectedHittingTime_le_inv_of_local_one_lower_bound
        (P := P) (hn := hn2) (C₀ := C)
        (Region := Region) (Goal := Next)
        (p := (((n * (n - 1) : ℕ) : ENNReal)⁻¹))
      · exact hRegion
      · exact hNextC
      · intro D hRegionD hNextD
        have hbase :
            (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
              Probability.ProbHitWithin P hn2 D Next 1 := by
          simpa [P, Next] using
            (PEM_heapPrefix_recruit_step_ProbHitWithin
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn2 hn0 hk_pos hk_lt D hRegionD.1 hRegionD.2)
        exact hbase.trans
          (Probability.ProbHitWithin_mono_goal P hn2 D Next
            (fun E => Next E ∨ ¬ Region E) (fun E hE => Or.inl hE) 1)
    change
      Probability.expectedHittingTime P hn2 C
        (fun D => Next D ∨ ¬ Region D) ≤
        ((n * (n - 1) : ℕ) : ENNReal)
    calc
      Probability.expectedHittingTime P hn2 C
          (fun D => Next D ∨ ¬ Region D)
          ≤ ((((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹) := hraw
      _ = ((n * (n - 1) : ℕ) : ENNReal) := by
        rw [inv_inv]

/-- Multi-level heap-prefix ranking estimate, with an explicit exit target.

Starting at prefix level `j`, the process reaches `RankingEndpoint` or leaves one of
the heap-prefix/strong-timer regions at levels `k₀, …, n-1` in at most
`(n-j) * n(n-1)` expected sequential steps.  This is the honest stochastic
version of the deterministic binary-tree recruit loop: the exit disjunct
records arbitrary scheduler interactions that break the recruit-loop invariant
and must be handled by the outer restart/rerank analysis. -/
theorem PEM_heapPrefix_expected_until_rankingEndpoint_or_exit_from_level_le
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {k₀ j : ℕ} (hk₀j : k₀ ≤ j) (hj_pos : 1 ≤ j) (hj_le : j ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hHeap : HeapPrefix C j) (hTimer : SettledMedianTimerStrong C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
      (fun D =>
        RankingEndpoint D ∨
          ∃ ℓ : ℕ, k₀ ≤ ℓ ∧ ℓ < n ∧
            ¬ (HeapPrefix D ℓ ∧ SettledMedianTimerStrong D)) ≤
      (((n - j) * (n * (n - 1)) : ℕ) : ENNReal) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let G : Config (AgentState n) Opinion n → Prop := fun D =>
    RankingEndpoint D ∨
      ∃ ℓ : ℕ, k₀ ≤ ℓ ∧ ℓ < n ∧
        ¬ (HeapPrefix D ℓ ∧ SettledMedianTimerStrong D)
  let den : ℕ := n * (n - 1)
  have hAll :
      ∀ fuel : ℕ, ∀ j : ℕ, ∀ C : Config (AgentState n) Opinion n,
        n - j ≤ fuel → k₀ ≤ j → 1 ≤ j → j ≤ n →
        HeapPrefix C j → SettledMedianTimerStrong C →
        Probability.expectedHittingTime P hn2 C G ≤
          (((n - j) * den : ℕ) : ENNReal) := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
        intro j C hfuel hk₀j hj_pos hj_le hHeap hTimer
        by_cases hG_C : G C
        · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 C G hG_C]
          exact zero_le _
        · by_cases hj_eq : j = n
          · subst j
            have hEndpoint : RankingEndpoint C :=
              HeapPrefix.to_RankingEndpoint hHeap
                (SettledMedianTimerStrong.toGood hTimer)
            exact False.elim (hG_C (Or.inl hEndpoint))
          · have hj_lt : j < n := by omega
            let Next : Config (AgentState n) Opinion n → Prop := fun D =>
              HeapPrefix D (j + 1) ∧ SettledMedianTimerGood D ∧
                (j + 1 < n → SettledMedianTimerStrong D)
            let GoalLocal : Config (AgentState n) Opinion n → Prop := fun D =>
              Next D ∨ G D
            let Region : Config (AgentState n) Opinion n → Prop := fun D =>
              HeapPrefix D j ∧ SettledMedianTimerStrong D
            let Mid : Config (AgentState n) Opinion n → Prop := fun D =>
              GoalLocal D ∨ ¬ Region D
            have hRegionC : Region C := ⟨hHeap, hTimer⟩
            by_cases hNextC : Next C
            · have hBelow : Probability.expectedHittingTime P hn2 C G ≤
                  (((n - (j + 1)) * den : ℕ) : ENNReal) := by
                by_cases hlast : j + 1 = n
                · have hSrank : InSrank C := by
                    exact HeapPrefix.to_InSrank
                      (by simpa [Next, hlast] using hNextC.1)
                  have hEndpoint : RankingEndpoint C :=
                    HeapPrefix.to_RankingEndpoint
                      (by simpa [Next, hlast] using hNextC.1)
                      (by simpa [Next] using hNextC.2.1)
                  rw [Probability.expectedHittingTime_eq_zero_of_goal
                    P hn2 C G (Or.inl hEndpoint)]
                  exact zero_le _
                · have hj_next_lt : j + 1 < n := by omega
                  exact ih (n - (j + 1)) (by omega) (j + 1) C
                    (by omega) (by omega) (by omega) (by omega)
                    hNextC.1 (hNextC.2.2 hj_next_lt)
              exact hBelow.trans (by
                have hle : n - (j + 1) ≤ n - j := by omega
                exact_mod_cast Nat.mul_le_mul_right den hle)
            · have hToMid : Probability.expectedHittingTime P hn2 C Mid ≤
                  ((den : ENNReal)) := by
                have hraw :
                    Probability.expectedHittingTime P hn2 C Mid ≤
                      ((((den : ℕ) : ENNReal)⁻¹)⁻¹) := by
                  apply Probability.expectedHittingTime_le_inv_of_local_one_lower_bound
                    (P := P) (hn := hn2) (C₀ := C)
                    (Region := Region) (Goal := GoalLocal)
                    (p := (((den : ℕ) : ENNReal)⁻¹))
                  · exact hRegionC
                  · intro hGoalLocal
                    rcases hGoalLocal with hNext | hG
                    · exact hNextC hNext
                    · exact hG_C hG
                  · intro D hRegionD _hGoalLocalD
                    have hbase :
                        (((den : ℕ) : ENNReal)⁻¹) ≤
                          Probability.ProbHitWithin P hn2 D Next 1 := by
                      simpa [P, Next, den] using
                        (PEM_heapPrefix_recruit_step_ProbHitWithin
                          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                          hn2 hn0 hj_pos hj_lt D hRegionD.1 hRegionD.2)
                    have hmono₁ :
                        Probability.ProbHitWithin P hn2 D Next 1 ≤
                          Probability.ProbHitWithin P hn2 D GoalLocal 1 :=
                      Probability.ProbHitWithin_mono_goal P hn2 D Next GoalLocal
                        (fun E hE => Or.inl hE) 1
                    have hmono₂ :
                        Probability.ProbHitWithin P hn2 D GoalLocal 1 ≤
                          Probability.ProbHitWithin P hn2 D Mid 1 :=
                      Probability.ProbHitWithin_mono_goal P hn2 D GoalLocal Mid
                        (fun E hE => Or.inl hE) 1
                    exact hbase.trans (hmono₁.trans hmono₂)
                calc
                  Probability.expectedHittingTime P hn2 C Mid
                      ≤ ((((den : ℕ) : ENNReal)⁻¹)⁻¹) := hraw
                  _ = (den : ENNReal) := by rw [inv_inv]
              have hFromMid : ∀ D : Config (AgentState n) Opinion n, Mid D →
                  Probability.expectedHittingTime P hn2 D G ≤
                    (((n - (j + 1)) * den : ℕ) : ENNReal) := by
                intro D hD
                rcases hD with hGoalLocal | hExit
                · rcases hGoalLocal with hNext | hG
                  · by_cases hlast : j + 1 = n
                    · have hEndpoint : RankingEndpoint D :=
                        HeapPrefix.to_RankingEndpoint
                          (by simpa [Next, hlast] using hNext.1)
                          (by simpa [Next] using hNext.2.1)
                      rw [Probability.expectedHittingTime_eq_zero_of_goal
                        P hn2 D G (Or.inl hEndpoint)]
                      exact zero_le _
                    · have hj_next_lt : j + 1 < n := by omega
                      exact ih (n - (j + 1)) (by omega) (j + 1) D
                        (by omega) (by omega) (by omega) (by omega)
                        hNext.1 (hNext.2.2 hj_next_lt)
                  · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D G hG]
                    exact zero_le _
                · have hG : G D := Or.inr ⟨j, hk₀j, hj_lt, hExit⟩
                  rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D G hG]
                  exact zero_le _
              have hComp :
                  Probability.expectedHittingTime P hn2 C G ≤
                    (den : ENNReal) + (((n - (j + 1)) * den : ℕ) : ENNReal) :=
                Probability.expectedHittingTime_add_le P hn2 C Mid G
                  (den : ENNReal)
                  (((n - (j + 1)) * den : ℕ) : ENNReal)
                  hToMid hFromMid
                  (by intro D hD; exact Or.inl (Or.inr hD))
              calc
                Probability.expectedHittingTime P hn2 C G
                    ≤ (den : ENNReal) +
                      (((n - (j + 1)) * den : ℕ) : ENNReal) := hComp
                _ = (((n - j) * den : ℕ) : ENNReal) := by
                  have hnj : n - j = (n - (j + 1)) + 1 := by omega
                  rw [hnj]
                  have hnat :
                      den + (n - (j + 1)) * den =
                        ((n - (j + 1)) + 1) * den := by
                    rw [Nat.add_mul, Nat.one_mul, add_comm]
                  rw [← Nat.cast_add, hnat]
  simpa [P, G, den] using
    hAll (n - j) j C (by omega) hk₀j hj_pos hj_le hHeap hTimer

/-- Fresh-ranking-start corollary of the heap-prefix stochastic recruit loop.

This is the ranking subphase that starts once the deterministic reset/dormant
normalizer has produced a `FreshRankingStart`.  It reaches `RankingEndpoint`, or else
explicitly records that some heap-prefix/strong-timer level was left. -/
theorem PEM_FreshRankingStart_expected_until_rankingEndpoint_or_heap_exit_le
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hFresh : FreshRankingStart C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C
      (fun D =>
        RankingEndpoint D ∨
          ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ < n ∧
            ¬ (HeapPrefix D ℓ ∧ SettledMedianTimerStrong D)) ≤
      ((Rmax * n * n : ℕ) : ENNReal) := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hHeap : HeapPrefix C 1 := FreshRankingStart.to_heapPrefix_one hFresh
  have hTimer : SettledMedianTimerStrong C :=
    FreshRankingStart.to_timerStrong hn4 hFresh
  have hbase :
      Probability.expectedHittingTime
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D =>
          RankingEndpoint D ∨
            ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ < n ∧
              ¬ (HeapPrefix D ℓ ∧ SettledMedianTimerStrong D)) ≤
        (((n - 1) * (n * (n - 1)) : ℕ) : ENNReal) := by
    simpa using
      (PEM_heapPrefix_expected_until_rankingEndpoint_or_exit_from_level_le
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 (k₀ := 1) (j := 1)
        (by omega) (by omega) (by omega) C hHeap hTimer)
  have hnat :
      (n - 1) * (n * (n - 1)) ≤ Rmax * n * n := by
    have hnm1_le_n : n - 1 ≤ n := Nat.sub_le n 1
    have hnm1_le_Rmax : n - 1 ≤ Rmax := hnm1_le_n.trans hRmax
    calc
      (n - 1) * (n * (n - 1))
          ≤ n * (n * (n - 1)) := by
            exact Nat.mul_le_mul_right (n * (n - 1)) hnm1_le_n
      _ ≤ n * (n * Rmax) := by
            exact Nat.mul_le_mul_left n (Nat.mul_le_mul_left n hnm1_le_Rmax)
      _ = Rmax * n * n := by ac_rfl
  exact hbase.trans (by exact_mod_cast hnat)

/-- Fresh-ranking-start bound with the ranking endpoint expanded into the
phase target shape consumed by the probabilistic composition layer.  The
heap-exit disjunct is still explicit; closing the full ranking phase requires
the outer restart/normalizer argument to discharge that branch. -/
theorem PEM_FreshRankingStart_expected_until_srank_timer2_or_consensus_or_heap_exit_le
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hFresh : FreshRankingStart C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C
      (fun D =>
        ((InSrank D ∧ MedianTimerAtLeast 2 D) ∨ IsConsensusConfig D) ∨
          ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ < n ∧
            ¬ (HeapPrefix D ℓ ∧ SettledMedianTimerStrong D)) ≤
      ((Rmax * n * n : ℕ) : ENNReal) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let OldTarget : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      RankingEndpoint D ∨
        ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ < n ∧
          ¬ (HeapPrefix D ℓ ∧ SettledMedianTimerStrong D)
  let NewTarget : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      ((InSrank D ∧ MedianTimerAtLeast 2 D) ∨ IsConsensusConfig D) ∨
        ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ < n ∧
          ¬ (HeapPrefix D ℓ ∧ SettledMedianTimerStrong D)
  have hOld :
      Probability.expectedHittingTime P (by omega : 2 ≤ n) C OldTarget ≤
        ((Rmax * n * n : ℕ) : ENNReal) := by
    simpa [P, OldTarget] using
      (PEM_FreshRankingStart_expected_until_rankingEndpoint_or_heap_exit_le
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hn0 hRmax C hFresh)
  have hMono :
      Probability.expectedHittingTime P (by omega : 2 ≤ n) C NewTarget ≤
        Probability.expectedHittingTime P (by omega : 2 ≤ n) C OldTarget := by
    apply Probability.expectedHittingTime_mono_goal
    intro D hOldD
    rcases hOldD with hEndpoint | hExit
    · exact Or.inl (RankingEndpoint.to_InSrank_and_timerAtLeast_two_or_consensus hEndpoint)
    · exact Or.inr hExit
  exact hMono.trans hOld

/-! ### Conditional phase probability interface

The original Table-2 `probReached` standalone lemmas are intentionally not
asserted here.  The robust composition path in this file is the
`ProbHitWithin` chain below; exact-time `probReached` phase statements are
kept as explicit hypotheses in the legacy composition wrappers. -/

/-! ### Full Table-2 composition and expected time -/

/-- This is not the full Table-2 proof: it composes four explicit phase
probability hypotheses.  The key design is that the window is applied only
inside the protocol timer invariant.  This matches the paper's phase
analysis: Lemma 10 needs the median timer to be bounded by its protocol
initialization value `7 * (Rmax + 4)`, not merely positive. -/
theorem PEM_consensus_window_success_prob_from_phase_bounds
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InTswap28SswapTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSdecTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (hRankPhase :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((10 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C InSrank (2 * Rmax * n * n))
    (hSwapPhase :
      ∀ C : Config (AgentState n) Opinion n, InSrank C →
          ((20 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InTswap28SswapTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hDecisionLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianTimerAtLeast 28 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((8 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hPropagationLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianAnswerCorrect C →
        MedianTimerAtLeast 1 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n)) :
    ∃ c : ℕ, 0 < c ∧
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          pemTable2SuccessProb ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (c * Rmax * n * n) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n) with hP_def
  have hn2 : 2 ≤ n := by omega
  have hDecisionPhase :
      ∀ C : Config (AgentState n) Opinion n,
        InTswap28SswapTimerBounded (7 * (Rmax + 4)) C →
          ((8 : ENNReal)⁻¹) ≤
            Probability.probReached P hn2 C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n) := by
    intro C hC
    simpa [P] using
      (PEM_decision_phase_hypothesis_of_live_branch
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hDecisionLive C hC)
  have hPropagationPhase :
      ∀ C : Config (AgentState n) Opinion n,
        InSdecTimerBounded (7 * (Rmax + 4)) C →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.probReached P hn2 C IsConsensusConfig (20 * Rmax * n * n) := by
    intro C hC
    simpa [P] using
      (PEM_propagation_phase_hypothesis_of_live_branch
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hPropagationLive C hC)
  refine ⟨24, by omega, fun C hTimerBd hNotCon => ?_⟩
  have htotal : (((2 * Rmax * n * n + 4 * n * n) +
      4 * n * n) + 20 * Rmax * n * n) + 0 = (22 * Rmax + 8) * n * n := by ring
  have hle_window : (22 * Rmax + 8) * n * n ≤ 24 * Rmax * n * n := by
    have hle_factor : 22 * Rmax + 8 ≤ 24 * Rmax := by
      have hR4 : 4 ≤ Rmax := by omega
      omega
    exact Nat.mul_le_mul_right n (Nat.mul_le_mul_right n hle_factor)
  rw [show 24 * Rmax * n * n = 24 * Rmax * n * n from rfl]
  apply le_trans _ (Probability.ProbHitWithin_mono_time P hn2 C IsConsensusConfig hle_window)
  rw [← htotal]
  have phase1_ranking :
      ((10 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C InSrank (2 * Rmax * n * n) := by
    simpa [P] using hRankPhase C hTimerBd hNotCon
  have phase2_swap : ∀ C' : Config (AgentState n) Opinion n, InSrank C' →
      ((20 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C'
          (InTswap28SswapTimerBounded (7 * (Rmax + 4))) (4 * n * n) := by
    intro C' hC'
    simpa [P] using hSwapPhase C' hC'
  have phase3_decision : ∀ C' : Config (AgentState n) Opinion n,
      InTswap28SswapTimerBounded (7 * (Rmax + 4)) C' →
      ((8 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C'
          (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n) := by
    intro C' hC'
    simpa [P] using hDecisionPhase C' hC'
  have phase4_propagation : ∀ C' : Config (AgentState n) Opinion n,
      InSdecTimerBounded (7 * (Rmax + 4)) C' →
      ((1280 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C' IsConsensusConfig (20 * Rmax * n * n) := by
    intro C' hC'
    simpa [P] using hPropagationPhase C' hC'
  exact pem_table2_phase_window_to_ProbHitWithin P hn2 C
    (SrankPhase := InSrank)
    (SswapPhase := InTswap28SswapTimerBounded (7 * (Rmax + 4)))
    (SdecPhase := InSdecTimerBounded (7 * (Rmax + 4)))
    (StimPhase := IsConsensusConfig)
    (SemPhase := IsConsensusConfig)
    (2 * Rmax * n * n) (4 * n * n)
    (4 * n * n) (20 * Rmax * n * n) 0
    phase1_ranking phase2_swap phase3_decision phase4_propagation
    (fun C' hC' => by
      rw [Probability.probReached_zero_of_goal P hn2 C' IsConsensusConfig hC']
      norm_num)

/-- Concrete Table-2 window bound from the four legacy exact-time phase
hypotheses.  This wrapper is conditional: the file's unconditional composition
path is the `ProbHitWithin` chain below. -/
theorem PEM_consensus_window_success_prob_of_phase_hypotheses
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InTswap28SswapTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSdecTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRankPhase :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((10 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C InSrank (2 * Rmax * n * n))
    (hSwapPhase :
      ∀ C : Config (AgentState n) Opinion n, InSrank C →
          ((20 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InTswap28SswapTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hDecisionLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianTimerAtLeast 28 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((8 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hPropagationLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianAnswerCorrect C →
        MedianTimerAtLeast 1 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n)) :
    ∃ c : ℕ, 0 < c ∧
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          pemTable2SuccessProb ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (c * Rmax * n * n) := by
  exact PEM_consensus_window_success_prob_from_phase_bounds
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn4 hRmax hEmax hDmax hRankPhase hSwapPhase hDecisionLive
    hPropagationLive

/-! ### Non-vacuous time bound (corrected statement)

The above `PEM_expected_parallel_time_linear_param` has a vacuously false
hypothesis (`hTimerConst` quantifies over ALL `InSswap` configs, but
`AgentState.timer : ℕ` is unbounded).  The theorem is technically proved
but says nothing about actual time complexity.

For this coupled wrapper, the correct statement makes the time bound depend
on `Rmax` because it is also used as the timer parameter.  This gives
`O(Rmax · n)` expected parallel time.  For externally bounded `Rmax`, this
is `O(n)`; for `Rmax = n` (our literal instantiation), this is `O(n²)`. -/

/-- Conditional expected-time consequence of the Table-2 phase hypotheses.

This theorem deliberately exposes the four probabilistic phase statements as
hypotheses; until those are proved, it should not be read as a complete
formalization of Kanaya Lemma 13.  Its conclusion is `O(Rmax · n)` expected
parallel time from standard initial configurations.  When `Rmax = n`, this
is `O(n²)`, not the paper's `O(n)` bound. -/
theorem PEM_expected_parallel_time_from_phase_bounds
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InTswap28SswapTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSdecTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRankPhase :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((10 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C InSrank (2 * Rmax * n * n))
    (hSwapPhase :
      ∀ C : Config (AgentState n) Opinion n, InSrank C →
          ((20 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InTswap28SswapTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hDecisionLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianTimerAtLeast 28 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((8 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hPropagationLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianAnswerCorrect C →
        MedianTimerAtLeast 1 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C₀ : Config (AgentState n) Opinion n,
        IsInitialConfig C₀ →
        Probability.expectedParallelTimeToConsensus
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C₀ ≤
          ENNReal.ofReal (C * Rmax * n) := by
  classical
  obtain ⟨c, hc_pos, hwin⟩ :=
    PEM_consensus_window_success_prob_from_phase_bounds hn4 hRmax hEmax hDmax
      hRankPhase hSwapPhase hDecisionLive hPropagationLive
  set P := PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n) with hP_def
  have hn2 : 2 ≤ n := by omega
  have hRmax_pos : 0 < Rmax := by omega
  have hcRnn_pos : 0 < c * Rmax * n * n := by
    apply Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hc_pos hRmax_pos) (by omega)) (by omega)
  have hK_ne : NeZero (c * Rmax * n * n) := ⟨Nat.pos_iff_ne_zero.mp hcRnn_pos⟩
  have hInvStep : ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C → ∀ i j : Fin n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) (C.step P i j) := by
    intro C hC i j; rw [hP_def]
    exact PEMProtocolCoupled_preserves_timer_bounded (by omega : 0 < n) C hC i j
  refine ⟨c * pemTable2SuccessProb⁻¹.toReal, ?_, fun C₀ hInit => ?_⟩
  · apply mul_pos
    · exact Nat.cast_pos.mpr hc_pos
    · exact ENNReal.toReal_pos
        (ne_of_gt (ENNReal.inv_pos.mpr pemTable2SuccessProb_ne_top))
        pemTable2SuccessProb_inv_ne_top
  · have hTimer₀ : IsTimerBoundedConfig (7 * (Rmax + 4)) C₀ := by
      intro μ
      have ht0 : (C₀ μ).1.timer = 0 := (hInit μ).2.2.2.2.1
      omega
    have hle :=
      Probability.expectedParallelTime_le_window_mul_inv_of_invariant
        P hn2 C₀ IsConsensusConfig
        (IsTimerBoundedConfig (7 * (Rmax + 4)))
        (c * Rmax * n * n) pemTable2SuccessProb
        pemTable2SuccessProb_le_one hTimer₀ hInvStep hwin
    calc Probability.expectedParallelTimeToConsensus P hn2 C₀
        ≤ ((c * Rmax * n * n : ℕ) : ENNReal) * pemTable2SuccessProb⁻¹ / ↑n := hle
      _ = ↑(c * Rmax) * pemTable2SuccessProb⁻¹ * ↑n := by
          rw [show (c * Rmax * n * n : ℕ) = (c * Rmax) * n * n from by ring]
          exact ennreal_quadratic_window_div_cancel pemTable2SuccessProb
            (by omega) pemTable2SuccessProb_pos pemTable2SuccessProb_ne_top
      _ = ENNReal.ofReal (↑(c * Rmax) * pemTable2SuccessProb⁻¹.toReal * ↑n) :=
          ennreal_nat_mul_inv_mul_nat_eq_ofReal pemTable2SuccessProb
            pemTable2SuccessProb_pos pemTable2SuccessProb_ne_top
      _ = ENNReal.ofReal (↑c * pemTable2SuccessProb⁻¹.toReal * ↑Rmax * ↑n) := by
          congr 1; push_cast; ring

/-! ### Conditional exports -/

theorem PEM_consensus_window_success_prob
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InTswap28SswapTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSdecTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRankPhase :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((10 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C InSrank (2 * Rmax * n * n))
    (hSwapPhase :
      ∀ C : Config (AgentState n) Opinion n, InSrank C →
          ((20 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InTswap28SswapTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hDecisionLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianTimerAtLeast 28 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((8 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hPropagationLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianAnswerCorrect C →
        MedianTimerAtLeast 1 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n)) :
    ∃ c : ℕ, 0 < c ∧
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          pemTable2SuccessProb ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (c * Rmax * n * n) :=
  PEM_consensus_window_success_prob_of_phase_hypotheses hn4 hRmax hEmax hDmax
    hRankPhase hSwapPhase hDecisionLive hPropagationLive

theorem PEM_expected_parallel_time
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InTswap28SswapTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSdecTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRankPhase :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((10 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C InSrank (2 * Rmax * n * n))
    (hSwapPhase :
      ∀ C : Config (AgentState n) Opinion n, InSrank C →
          ((20 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InTswap28SswapTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hDecisionLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianTimerAtLeast 28 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((8 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hPropagationLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianAnswerCorrect C →
        MedianTimerAtLeast 1 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C₀ : Config (AgentState n) Opinion n,
        IsInitialConfig C₀ →
        Probability.expectedParallelTimeToConsensus
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C₀ ≤
          ENNReal.ofReal (C * Rmax * n) :=
  PEM_expected_parallel_time_from_phase_bounds hn4 hRmax hEmax hDmax
    hRankPhase hSwapPhase hDecisionLive hPropagationLive

end SSEM
