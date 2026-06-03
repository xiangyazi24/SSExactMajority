import SSExactMajority.UpperBound.Time

/-!
# Optimal parallel-time bound — five-window assembly (scaffold)

This reduces the unconditional optimal parallel-time bound to the five Table-2
phase-window claims, instantiated with concrete phase predicates and a quadratic
window `W = 20·Rmax·n²` per phase. It applies the existing composition theorem
`pem_table2_phase_windows_to_expectedParallelTime`. Each of the five windows is
an explicit `probReached ≥ const` lemma (currently `sorry`, to be discharged via
the per-phase descent / `probHitAndIn` machinery; `hRank` needs reset-normalization).

Replaces the vacuous-impostor placeholder `PEM_consensus_window_success_prob_vacuous_timer_const`.
-/

namespace SSEM

open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- Ranking phase reached: ranked with a live median timer (or already consensus). -/
def OWSrank (C : Config (AgentState n) Opinion n) : Prop :=
  (InSrank C ∧ MedianTimerAtLeast 2 C) ∨ IsConsensusConfig C

/-- Swap phase: in the swap regime with a live median timer (or consensus). -/
def OWSswap (C : Config (AgentState n) Opinion n) : Prop :=
  (InSswap C ∧ MedianTimerAtLeast 1 C) ∨ IsConsensusConfig C

/-- Decision phase: median answer correct in the swap regime (or consensus). -/
def OWSdec (C : Config (AgentState n) Opinion n) : Prop :=
  (InSswap C ∧ MedianAnswerCorrect C ∧ MedianTimerAtLeast 1 C) ∨ IsConsensusConfig C

/-- Timer/propagate phase: a correct reset seed has formed (or consensus). -/
def OWStim (C : Config (AgentState n) Opinion n) : Prop :=
  CorrectResetSeed C ∨ IsConsensusConfig C

section Windows
variable {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
  [DecidableEq (Config (AgentState n) Opinion n)]

/-- **Window 1 (ranking).** From any configuration, within `20·Rmax·n²` steps the
ranking phase is reached with probability ≥ 1/10. (Needs reset-normalization:
any config → fresh ranking start, then the ranking-time bound.) -/
theorem OW_hRank (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      ((10 : ENNReal)⁻¹) ≤
        Probability.probReached (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C₀ OWSrank (20 * Rmax * n * n) := by
  sorry

/-- **Window 2 (swap).** From the ranking phase, reach the swap phase within
`20·Rmax·n²` with probability ≥ 1/20. -/
theorem OW_hSwap (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∀ C : Config (AgentState n) Opinion n, OWSrank C →
      ((20 : ENNReal)⁻¹) ≤
        Probability.probReached (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C OWSswap (20 * Rmax * n * n) := by
  sorry

/-- **Window 3 (decision).** From the swap phase, reach a median-correct decision
within `20·Rmax·n²` with probability ≥ 1/8. (Decision descent:
`PEM_Tswap_to_MedianAnswerCorrect_or_exit_prob_window` + `probHitAndIn`.) -/
theorem OW_hDec (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∀ C : Config (AgentState n) Opinion n, OWSswap C →
      ((8 : ENNReal)⁻¹) ≤
        Probability.probReached (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C OWSdec (20 * Rmax * n * n) := by
  sorry

/-- **Window 4 (timer/propagate).** From a median-correct decision, form a correct
reset seed within `20·Rmax·n²` with probability ≥ 1/1280. (Timer drain:
`PEM_expected_timer_drain_poly` → Markov.) -/
theorem OW_hTim (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∀ C : Config (AgentState n) Opinion n, OWSdec C →
      ((1280 : ENNReal)⁻¹) ≤
        Probability.probReached (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C OWStim (20 * Rmax * n * n) := by
  sorry

/-- **Window 5 (epidemic to consensus).** From a correct reset seed, reach consensus
within `20·Rmax·n²` with probability ≥ 1/2. (CRS → AllR (`PEM_CRS_to_allR_or_break`)
→ re-rank → consensus; needs the polynomial re-ranking bound.) -/
theorem OW_hSem (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∀ C : Config (AgentState n) Opinion n, OWStim C →
      ((2 : ENNReal)⁻¹) ≤
        Probability.probReached (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n) := by
  sorry

/-- **Unconditional optimal parallel-time bound** (modulo the five window lemmas above).
`E[parallel time to consensus] ≤ 5·(20·Rmax·n²)·pemTable2SuccessProb⁻¹ / n`. -/
theorem PEM_expectedParallelTime_optimal (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      Probability.expectedParallelTimeToConsensus
        (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀ ≤
        (((((20 * Rmax * n * n) + (20 * Rmax * n * n)) + (20 * Rmax * n * n)) +
            (20 * Rmax * n * n)) + (20 * Rmax * n * n) : ℕ) * pemTable2SuccessProb⁻¹ / n := by
  classical
  have hpos : 0 < 20 * Rmax * n * n := by
    have : 0 < n := by omega
    have : 0 < Rmax := by omega
    positivity
  haveI : NeZero
      (((((20 * Rmax * n * n) + (20 * Rmax * n * n)) + (20 * Rmax * n * n)) +
          (20 * Rmax * n * n)) + (20 * Rmax * n * n)) := ⟨by omega⟩
  exact pem_table2_phase_windows_to_expectedParallelTime
    (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n)) (by omega : 2 ≤ n)
    OWSrank OWSswap OWSdec OWStim
    (20 * Rmax * n * n) (20 * Rmax * n * n) (20 * Rmax * n * n)
    (20 * Rmax * n * n) (20 * Rmax * n * n)
    (OW_hRank hn4 hRmax hEmax hDmax)
    (OW_hSwap hn4 hRmax hEmax hDmax)
    (OW_hDec hn4 hRmax hEmax hDmax)
    (OW_hTim hn4 hRmax hEmax hDmax)
    (OW_hSem hn4 hRmax hEmax hDmax)

end Windows

end SSEM
