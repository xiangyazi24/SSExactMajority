import SSExactMajority.UpperBound.Time
import SSExactMajority.UpperBound.Time.PolynomialBound

/-!
# Optimal parallel-time bound — reduced to two expected-time keystones

The team's assembly `PEM_expected_parallel_time_from_global_expected_phase_bounds`
(Time.lean) already chains the ranking window, the proven swap window
(`PEM_swap_ProbHitWithin_InSswap_timer_live_const35_bounded`), and the consensus
window via `ProbHitWithin_add_ge_mul` + window-amplification. It is conditional on
exactly two universal expected-hitting-time bounds. Discharging them here yields the
**unconditional** optimal parallel-time theorem.

Remaining work = these two keystones:
* `OW_rankBound` — from any timer-bounded config, expected time to reach the ranking
  endpoint (`InSrank ∧ median timer ≥ 35 ∧ timer-bounded`) is `≤ Rmax·n²`.
  (Universal ranking time; needs reset-normalization from arbitrary configs +
  `PEM_FreshRankingStart_expected_until_srank_timer2_or_consensus_or_heap_exit_le`.)
* `OW_consensusBound` — from `InSswap` with a live, bounded median timer, expected
  time to consensus is `≤ 10·Rmax·n²`. (The decision→propagate→reset→re-rank renewal;
  "Lemma 9+11".)
-/

namespace SSEM

open scoped ENNReal

attribute [local instance] Classical.propDecidable

section
variable {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
  [DecidableEq (Config (AgentState n) Opinion n)]

/-- **Keystone 1 (universal ranking time).** From any timer-bounded configuration,
the expected time to reach a ranked configuration with a fresh (`≥ 35`) bounded
median timer is at most `Rmax·n²`. -/
theorem OW_rankBound (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        Probability.expectedHittingTime
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C
          (fun D => InSrank D ∧ MedianTimerAtLeast 35 D ∧
            IsTimerBoundedConfig (7 * (Rmax + 4)) D) ≤
          ((Rmax * n * n : ℕ) : ENNReal) := by
  sorry

/-- **Keystone 2 (consensus from a live swap).** From `InSswap` with a live, bounded
median timer, the expected time to consensus is at most `10·Rmax·n²`. -/
theorem OW_consensusBound (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∀ C : Config (AgentState n) Opinion n,
      InSswap C → MedianTimerAtLeast 1 C →
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        Probability.expectedHittingTime
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C IsConsensusConfig ≤
          ((10 * Rmax * n * n : ℕ) : ENNReal) := by
  sorry


/-- Markov-window form of `PEM_CRS_to_allR_or_break`: from a correct reset seed,
within `2·n²(n-1)` steps the epidemic reaches all-Resetting (nrc=0) or CRS breaks
(ranking starts, answers preserved) with probability ≥ 1/2. Forward building block. -/
theorem crs_to_allR_or_break_window (hn4 : 4 ≤ n) (hn0 : 0 < n) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n) (hSeed : CorrectResetSeed C) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => (nonResettingCount D = 0) ∨ ¬ CorrectResetSeed D)
        (2 * (n * n * (n - 1))) :=
  Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C _
    (PEM_CRS_to_allR_or_break hn4 hn0 hDmax C hSeed) (by omega)


/-- Decision-phase window (Markov form of `PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le`):
from `InSswap` with a live median timer and a wrong median answer, within `2·n(n-1)` steps
the median answer becomes correct (or the swap/timer region is left) with probability ≥ 1/2. -/
theorem decision_window (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n) (hC : InSswap C)
    (hT : MedianTimerAtLeast 1 C) (hND : ¬ MedianAnswerCorrect C) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => (InSswap D ∧ MedianAnswerCorrect D) ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * (n * (n - 1))) := by
  have hM := PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (by omega : 2 ≤ n) hn0 hn4 hC hT hND
  rw [inv_inv] at hM
  exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C _ hM (by omega)

/-- **Unconditional optimal parallel-time bound.** From any timer-bounded initial
configuration, the expected parallel time to consensus is
`≤ (2·Rmax·n² + 4·n² + 20·Rmax·n²)·16 / n = O(Rmax·n)`. Modulo the two keystones above. -/
theorem PEM_expectedParallelTime_optimal (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C₀ →
      Probability.expectedParallelTimeToConsensus
        (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀ ≤
        (((((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n : ℕ) : ENNReal) *
          ((16 : ENNReal)⁻¹)⁻¹) / n) :=
  PEM_expected_parallel_time_from_global_expected_phase_bounds
    hn4 hRmax hEmax hDmax
    (OW_rankBound hn4 hRmax hEmax hDmax)
    (OW_consensusBound hn4 hRmax hEmax hDmax)

end

end SSEM
