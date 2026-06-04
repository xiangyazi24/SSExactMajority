import SSExactMajority.UpperBound.Time
import SSExactMajority.UpperBound.Time.EpidemicBound
import SSExactMajority.UpperBound.Time.EpidemicMechanics
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
  time to consensus is bounded by `OW_consensusExpectedSteps`, modulo the single
  cited [12] return/ranking hypothesis `hRank12`.
-/

namespace SSEM

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

section
variable {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
  [DecidableEq (Config (AgentState n) Opinion n)]

/-- The silence endpoint used by the renewal: a ranked swap configuration
with no remaining `phi` answers in the reservoir. -/
def OW_silenceEndpoint {n : ℕ} (C : Config (AgentState n) Opinion n) : Prop :=
  InSswap C ∧ ResAns (majorityAnswer C) C ∧ phiCount C = 0

/-- The branch on which the cited [12] return/ranking hypothesis is invoked. -/
def OW_restartBranch {n : ℕ} (C : Config (AgentState n) Opinion n) : Prop :=
  CorrectResetSeed C ∨ ¬ (InSswap C ∧ MedianTimerAtLeast 1 C)

/-- Proven swap-window length used in the consensus renewal. -/
def OW_swapWindow (n Rmax : ℕ) : ℕ :=
  2 * (n * (n - 1)) + 2 * (7 * (Rmax + 4) * n * (n - 1))

/-- Cited [12] return/ranking window budget, including the epidemic drain. -/
def OW_rank12Window (n Rmax : ℕ) : ℕ :=
  Rmax * n * n

/-- One renewal-cycle window for the consensus proof. -/
def OW_consensusCycleWindow (n Rmax : ℕ) : ℕ :=
  OW_swapWindow n Rmax + OW_rank12Window n Rmax

/-- Expected sequential-time bound produced by the `1/8` renewal window. -/
def OW_consensusExpectedSteps (n Rmax : ℕ) : ℕ :=
  8 * OW_consensusCycleWindow n Rmax

/-- End-to-end finite window used after converting the consensus expected-time
bound to a `1/2` hit window. -/
def OW_globalWindow (n Rmax : ℕ) : ℕ :=
  (2 * Rmax * n * n + 4 * n * n) + 2 * OW_consensusExpectedSteps n Rmax

/-- The endpoint supplied by the [12] ranking window after the reset epidemic has
already made the answer uniform: ranking has reached `InSswap`, the uniform
answer is still `m`, and the global majority answer agrees with `m`. -/
def OW_rankedEpidemicEndpoint {n : ℕ} (m : Answer)
    (C : Config (AgentState n) Opinion n) : Prop :=
  InSswap C ∧ EpidemicPhiGoal m C ∧ majorityAnswer C = m

omit [Inhabited (Fin n × Fin n)] [DecidableEq (Config (AgentState n) Opinion n)] in
/-- The proven silence link for a ranked uniform endpoint.  This is the Kanaya
part: no [12] timing statement is used here. -/
theorem OW_silenceEndpoint_of_rankedEpidemicEndpoint
    {m : Answer} {C : Config (AgentState n) Opinion n}
    (hC : OW_rankedEpidemicEndpoint m C) :
    OW_silenceEndpoint C := by
  rcases hC with ⟨hSswap, hEpi, hMaj⟩
  refine ⟨hSswap, ?_, hEpi.1⟩
  intro w
  exact Or.inl (by
    rw [hMaj]
    exact hEpi.2 w)

omit [Inhabited (Fin n × Fin n)] in
/-- Markov-window form of the proven abstract epidemic descent theorem. -/
theorem epidemic_phiCount_to_zero_window_ge_half
    (P : Protocol (AgentState n) Opinion Output) (hn : 2 ≤ n)
    {m : Answer} (C : Config (AgentState n) Opinion n)
    (Inv : Config (AgentState n) Opinion n → Prop)
    [DecidablePred Inv]
    (M T : ℕ)
    (hInv₀ : Inv C)
    (hAnsInv : ∀ D : Config (AgentState n) Opinion n,
      Inv D → EpidemicAnswerInv m D)
    (hInvStep : ∀ D : Config (AgentState n) Opinion n, Inv D →
      ¬ EpidemicPhiGoal m D →
        ∀ i j : Fin n, Inv (D.step P i j) ∨ EpidemicPhiGoal m (D.step P i j))
    (hNonincrease : ∀ D : Config (AgentState n) Opinion n, Inv D →
      ¬ EpidemicPhiGoal m D →
        ∀ i j : Fin n, phiCount (D.step P i j) ≤ phiCount D)
    (hGood : ∀ D : Config (AgentState n) Opinion n, Inv D →
      ¬ EpidemicPhiGoal m D → 0 < phiCount D →
        ∀ p : Fin n × Fin n, p ∈ phiNonPhiPairs D →
          EpidemicPhiGoal m (D.step P p.1 p.2) ∨
            (Inv (D.step P p.1 p.2) ∧
              phiCount (D.step P p.1 p.2) < phiCount D))
    (hSumLe :
      (∑ r ∈ Finset.range (phiCount C),
        ((((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal) *
            ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹)) ≤
        ((M : ℕ) : ENNReal))
    (hWindow : 2 * M ≤ T + 1) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn C (EpidemicPhiGoal m) T := by
  have hExp :=
    epidemic_phiCount_to_zero_expected_le
      P hn (m := m) C Inv hInv₀ hAnsInv hInvStep hNonincrease hGood
  exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
    P hn C (EpidemicPhiGoal m) (hExp.trans hSumLe) hWindow

omit [Inhabited (Fin n × Fin n)] in
/-- Faithful CRS-to-silence composition.

The epidemic half is discharged through `epidemic_phiCount_to_zero_expected_le`
and Markov.  The only timing hypothesis for the rank phase is `h12rank`, which
starts from a uniform no-`phi` epidemic endpoint and reaches the ranked epidemic
endpoint.  The final conversion to `OW_silenceEndpoint` is the proven silence
link above.

The product side condition is explicit on purpose: with an epidemic `1/2`
window and a rank `1/2` window, the chain gives `1/4`, not `1/2`.  A caller
that wants the old `hRank12` probability must provide either a probability-one
reset/epidemic window or a stronger rank-window lower bound. -/
theorem CRS_to_silence_of_rank12 (hn4 : 4 ≤ n)
    (T_reset T_rank M : ℕ)
    (Inv : Answer → Config (AgentState n) Opinion n → Prop)
    [hInvDec : ∀ m : Answer, DecidablePred (Inv m)]
    (rankProb : ENNReal)
    (hProduct : ((2 : ENNReal)⁻¹) ≤ ((2 : ENNReal)⁻¹) * rankProb)
    (hResetInv :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        CorrectResetSeed C →
        Inv (majorityAnswer C) C)
    (hAnsInv : ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
      Inv m D → EpidemicAnswerInv m D)
    (hInvStep : ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
      Inv m D → ¬ EpidemicPhiGoal m D →
        ∀ i j : Fin n,
          Inv m (D.step (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n)) i j) ∨
            EpidemicPhiGoal m
              (D.step (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n)) i j))
    (hNonincrease : ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
      Inv m D → ¬ EpidemicPhiGoal m D →
        ∀ i j : Fin n,
          phiCount
              (D.step (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n)) i j) ≤
            phiCount D)
    (hGood : ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
      Inv m D → ¬ EpidemicPhiGoal m D → 0 < phiCount D →
        ∀ p : Fin n × Fin n, p ∈ phiNonPhiPairs D →
          EpidemicPhiGoal m
              (D.step (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n)) p.1 p.2) ∨
            (Inv m
                (D.step (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n)) p.1 p.2) ∧
              phiCount
                  (D.step (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n)) p.1 p.2) <
                phiCount D))
    (hEpidemicSum :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        CorrectResetSeed C →
          (∑ r ∈ Finset.range (phiCount C),
            ((((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal) *
                ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹)) ≤
            ((M : ℕ) : ENNReal))
    (hResetWindow : 2 * M ≤ T_reset + 1)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
          rankProb ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
      CorrectResetSeed C →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin
            (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C OW_silenceEndpoint
            (T_reset + T_rank) := by
  classical
  intro C hTimer hSeed
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n) with hP
  haveI : DecidablePred (Inv (majorityAnswer C)) := hInvDec (majorityAnswer C)
  have hEpiWindow :
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C (EpidemicPhiGoal (majorityAnswer C))
          T_reset := by
    exact epidemic_phiCount_to_zero_window_ge_half
      P hn2 (m := majorityAnswer C) C (Inv (majorityAnswer C)) M T_reset
      (hResetInv C hTimer hSeed)
      (fun D hD => hAnsInv (majorityAnswer C) D hD)
      (fun D hD hNot i j => by
        simpa [P] using hInvStep (majorityAnswer C) D hD hNot i j)
      (fun D hD hNot i j => by
        simpa [P] using hNonincrease (majorityAnswer C) D hD hNot i j)
      (fun D hD hNot hPhi p hp => by
        simpa [P] using hGood (majorityAnswer C) D hD hNot hPhi p hp)
      (hEpidemicSum C hTimer hSeed)
      hResetWindow
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
  have hChain :
      ((2 : ENNReal)⁻¹) * rankProb ≤
        Probability.ProbHitWithin P hn2 C OW_silenceEndpoint
          (T_reset + T_rank) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C
      (EpidemicPhiGoal (majorityAnswer C)) OW_silenceEndpoint
      T_reset T_rank ((2 : ENNReal)⁻¹) rankProb
      hEpiWindow hRankToSilence
  exact hProduct.trans hChain

omit [Inhabited (Fin n × Fin n)] [DecidableEq (Config (AgentState n) Opinion n)] in
/-- In an epidemic region at least one agent carries the non-`phi` answer, so
the number of `phi` agents is strictly below `n`. -/
theorem epidemicRegion_phiCount_lt {m : Answer}
    {C : Config (AgentState n) Opinion n}
    (hReg : EpidemicRegion m C) :
    phiCount C < n := by
  classical
  rcases hReg.2.2.2 with ⟨w, hw⟩
  have hsub : phiAgents C ⊆ (Finset.univ : Finset (Fin n)) := by
    intro v hv
    simp
  have hproper : phiAgents C ⊂ (Finset.univ : Finset (Fin n)) := by
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨w, by simp, ?_⟩
    intro hwmem
    have hphi : (C w).1.answer = .phi := (Finset.mem_filter.mp hwmem).2
    exact hReg.2.2.1 (hw.symm.trans hphi)
  have hcard := Finset.card_lt_card hproper
  simpa [phiAgents_card, Fintype.card_fin] using hcard

omit [Inhabited (Fin n × Fin n)] [DecidableEq (Config (AgentState n) Opinion n)] in
/-- Coarse coupon bound for the one-way reset epidemic.  Each non-terminal
level has rate at least `1 / (n*(n-1))`, and there are at most `n` levels. -/
theorem epidemic_coupon_sum_le_quadratic {m : Answer}
    {C : Config (AgentState n) Opinion n}
    (hReg : EpidemicRegion m C) :
    (∑ r ∈ Finset.range (phiCount C),
      ((((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹)) ≤
      ((n * n * (n - 1) : ℕ) : ENNReal) := by
  classical
  have hPhi_lt : phiCount C < n := epidemicRegion_phiCount_lt hReg
  have hTerm :
      ∀ r ∈ Finset.range (phiCount C),
        ((((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal) *
            ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹) ≤
          ((n * (n - 1) : ℕ) : ENNReal) := by
    intro r hr
    have hr_lt : r < phiCount C := Finset.mem_range.mp hr
    have hrn : r + 1 < n := by omega
    have hleft : 0 < 2 * (r + 1) := by positivity
    have hright : 0 < n - (r + 1) := Nat.sub_pos_of_lt hrn
    have hApos : 0 < 2 * (r + 1) * (n - (r + 1)) :=
      Nat.mul_pos hleft hright
    have hAge1 : 1 ≤ 2 * (r + 1) * (n - (r + 1)) :=
      Nat.succ_le_of_lt hApos
    have hA_ne_zero :
        (((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal)) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hApos
    have hA_ne_top :
        (((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal)) ≠ ⊤ :=
      ENNReal.natCast_ne_top _
    rw [ENNReal.mul_inv (Or.inl hA_ne_zero) (Or.inl hA_ne_top), inv_inv]
    have hInv_le : (((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal))⁻¹ ≤ 1 := by
      apply ENNReal.inv_le_one.mpr
      exact_mod_cast hAge1
    calc
      (((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal))⁻¹ *
          ((n * (n - 1) : ℕ) : ENNReal)
          ≤ 1 * ((n * (n - 1) : ℕ) : ENNReal) :=
            by
              simpa [mul_comm] using
                (mul_le_mul_right hInv_le
                  (((n * (n - 1) : ℕ) : ENNReal)))
      _ = ((n * (n - 1) : ℕ) : ENNReal) := one_mul _
  calc
    (∑ r ∈ Finset.range (phiCount C),
      ((((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹))
        ≤ ∑ _r ∈ Finset.range (phiCount C),
            ((n * (n - 1) : ℕ) : ENNReal) :=
          Finset.sum_le_sum hTerm
    _ = (phiCount C : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (n : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal) := by
          have hPhi_le : (phiCount C : ENNReal) ≤ (n : ENNReal) := by
            exact_mod_cast le_of_lt hPhi_lt
          simpa [mul_comm] using
            (mul_le_mul_right hPhi_le (((n * (n - 1) : ℕ) : ENNReal)))
    _ = ((n * n * (n - 1) : ℕ) : ENNReal) := by
          push_cast
          ring

omit [Inhabited (Fin n × Fin n)] [DecidableEq (Config (AgentState n) Opinion n)] in
/-- Cited [12] reset-duration contract used to run the proven reset epidemic
mechanics faithfully.  The fields are exactly the reset-window facts not proved
by `EpidemicMechanics`: the CRS entry into the all-Resetting epidemic region,
the no-wake/no-Phase4 guard for arbitrary reset-window steps, the post-step
all-Resetting guard, and the rankDelta Resetting guard for scheduled
`(phi, non-phi)` pairs. -/
structure CRSResetDuration12 {n Rmax Emax Dmax : ℕ} (hn : 0 < n)
    (T_reset : ℕ) : Prop where
  resetInv :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
      CorrectResetSeed C →
      EpidemicRegion (majorityAnswer C) C
  stepNoPhase4 :
    ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
      EpidemicRegion m D → ¬ EpidemicPhiGoal m D →
        ∀ i j : Fin n,
          ¬ ((transitionPEM_prePhase4 n Rmax
                (rankDeltaOSSR Rmax Emax Dmax hn)
                (D i).1 (D j).1 (D i).2 (D j).2).1.role = .Settled ∧
              (transitionPEM_prePhase4 n Rmax
                (rankDeltaOSSR Rmax Emax Dmax hn)
                (D i).1 (D j).1 (D i).2 (D j).2).2.role = .Settled)
  stepAllResetting :
    ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
      EpidemicRegion m D → ¬ EpidemicPhiGoal m D →
        ∀ i j w : Fin n,
          ((D.step (PEMProtocolCoupled n Rmax Emax Dmax hn) i j) w).1.role =
            .Resetting
  pairRankResetting :
    ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
      EpidemicRegion m D → ¬ EpidemicPhiGoal m D →
        ∀ p : Fin n × Fin n, p ∈ phiNonPhiPairs D →
          (rankDeltaOSSR Rmax Emax Dmax hn ((D p.1).1, (D p.2).1)).1.role =
            .Resetting ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((D p.1).1, (D p.2).1)).2.role =
            .Resetting
  resetWindow : 2 * (n * n * (n - 1)) ≤ T_reset + 1

omit [Inhabited (Fin n × Fin n)] in
/-- Faithful concrete CRS-to-silence wrapper.  The only cited ingredients are
the [12] reset-duration contract and the [12] rank window; the epidemic
one-step obligations are discharged through the proved `EpidemicMechanics`
theorems with `Inv := EpidemicRegion`. -/
theorem CRS_to_silence_faithful (hn4 : 4 ≤ n)
    (T_reset T_rank : ℕ)
    (rankProb : ENNReal)
    (hProduct : ((2 : ENNReal)⁻¹) ≤ ((2 : ENNReal)⁻¹) * rankProb)
    (h12resetDuration :
      CRSResetDuration12 (n := n) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (by omega : 0 < n) T_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
          rankProb ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
      CorrectResetSeed C →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin
            (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C OW_silenceEndpoint
            (T_reset + T_rank) := by
  classical
  have hn0 : 0 < n := by omega
  refine CRS_to_silence_of_rank12
    (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn4 T_reset T_rank (n * n * (n - 1))
    (fun m D => EpidemicRegion m D) rankProb hProduct
    (fun C hTimer hSeed => h12resetDuration.resetInv C hTimer hSeed)
    (fun m D hD => epidemicRegion_answerInv hD)
    (fun m D hD hNot i j => ?_)
    (fun m D hD hNot i j => ?_)
    (fun m D hD hNot _hPhi p hp => ?_)
    (fun C hTimer hSeed =>
      epidemic_coupon_sum_le_quadratic (h12resetDuration.resetInv C hTimer hSeed))
    h12resetDuration.resetWindow
    h12rank
  · left
    have hClosed :=
      epidemicRegion_step_closed
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        (m := m) (C := D) hD i j
        (h12resetDuration.stepNoPhase4 m D hD hNot i j)
        (h12resetDuration.stepAllResetting m D hD hNot i j)
    simpa [PEMProtocolCoupled, PEMProtocol] using hClosed
  · have hMono :=
      epidemicRegion_phiCount_nonincrease
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        (m := m) (C := D) hD i j
        (h12resetDuration.stepNoPhase4 m D hD hNot i j)
    simpa [PEMProtocolCoupled, PEMProtocol] using hMono
  · have hPair := h12resetDuration.pairRankResetting m D hD hNot p hp
    have hClosed :=
      epidemicRegion_step_closed
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        (m := m) (C := D) hD p.1 p.2
        (h12resetDuration.stepNoPhase4 m D hD hNot p.1 p.2)
        (h12resetDuration.stepAllResetting m D hD hNot p.1 p.2)
    have hDesc :=
      epidemicRegion_phiPair_descent
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        (m := m) (C := D) hD p hp hPair.1 hPair.2
    right
    constructor
    · simpa [PEMProtocolCoupled, PEMProtocol] using hClosed
    · simpa [PEMProtocolCoupled, PEMProtocol] using hDesc

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


/-- Timer-drain/propagate window (Markov form of `PEM_expected_timer_drain_poly`):
from `InSswap`+`MAC`+bounded live timer, within `2·7(Rmax+4)·n(n-1)` steps reach
consensus, or form a correct reset seed, or leave the live-swap region, with prob ≥ 1/2. -/
theorem timer_drain_window (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) (hC : InSswap C)
    (hMAC : MedianAnswerCorrect C) (hTLo : MedianTimerAtLeast 1 C)
    (hTHi : IsTimerBoundedConfig (7 * (Rmax + 4)) C) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * (7 * (Rmax + 4) * n * (n - 1))) :=
  Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C _
    (PEM_expected_timer_drain_poly (Emax := Emax) (Dmax := Dmax) hn4 hn0 hRmax C hC hMAC hTLo hTHi)
    (by omega)


/-- Chain decision -> timer-drain (bounded invariant threaded). From InSswap with a
live, bounded median timer, within `2n(n-1) + 2*7(Rmax+4)n(n-1)` steps reach consensus /
a correct reset seed / leave the live-swap region, with probability >= 1/4. -/
theorem swap_live_to_cons_or_crs_or_break (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) (hC : InSswap C)
    (hT : MedianTimerAtLeast 1 C) (hB : IsTimerBoundedConfig (7 * (Rmax + 4)) C) :
    ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * (n * (n - 1)) + 2 * (7 * (Rmax + 4) * n * (n - 1))) := by
  have hn2 : (2 : ℕ) ≤ n := by omega
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0 with hP
  set Inv : Config (AgentState n) Opinion n → Prop :=
    fun D => IsTimerBoundedConfig (7 * (Rmax + 4)) D with hInvDef
  set Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨ ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
    with hGoalDef
  have hInvStep : ∀ D, Inv D → ∀ i j, Inv (D.step P i j) :=
    fun D hD i j => PEMProtocolCoupled_preserves_timer_bounded hn0 D hD i j
  by_cases hMAC : MedianAnswerCorrect C
  · refine le_trans ?_ (Probability.ProbHitWithin_mono_time P hn2 C Goal
      (m := 2 * (7 * (Rmax + 4) * n * (n - 1))) (by omega))
    refine le_trans ?_ (timer_drain_window hn4 hn0 hRmax C hC hMAC hT hB)
    rw [ENNReal.inv_le_inv]; norm_num
  · set dG : Config (AgentState n) Opinion n → Prop :=
      fun D => (InSswap D ∧ MedianAnswerCorrect D) ∨ ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
      with hdGDef
    set Mid : Config (AgentState n) Opinion n → Prop := fun D => dG D ∧ Inv D with hMidDef
    have hMid : ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C Mid (2 * (n * (n - 1))) := by
      rw [hMidDef,
        Probability.ProbHitWithin_eq_and_inv_of_invariant P hn2 C dG Inv hB hInvStep]
      exact decision_window hn4 hn0 C hC hT hMAC
    have hGoal : ∀ C' : Config (AgentState n) Opinion n, Mid C' →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C' Goal (2 * (7 * (Rmax + 4) * n * (n - 1))) := by
      intro C' hC'
      obtain ⟨hdg, hinv⟩ := hC'
      by_cases hlive : InSswap C' ∧ MedianTimerAtLeast 1 C'
      · have hmac : MedianAnswerCorrect C' := by
          rcases hdg with ⟨_, hm⟩ | hexit
          · exact hm
          · exact absurd hlive hexit
        exact timer_drain_window hn4 hn0 hRmax C' hlive.1 hmac hlive.2 hinv
      · have hgC' : Goal C' := Or.inr (Or.inr hlive)
        have h1 : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 C' Goal (2 * (7 * (Rmax + 4) * n * (n - 1))) := by
          calc (1 : ENNReal) = Probability.probReached P hn2 C' Goal 0 :=
                (Probability.probReached_zero_of_goal P hn2 C' Goal hgC').symm
            _ ≤ Probability.ProbHitWithin P hn2 C' Goal 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 C' Goal 0
            _ ≤ Probability.ProbHitWithin P hn2 C' Goal (2 * (7 * (Rmax + 4) * n * (n - 1))) :=
                Probability.ProbHitWithin_mono_time P hn2 C' Goal (Nat.zero_le _)
        exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) h1
    have hchain := Probability.ProbHitWithin_add_ge_mul P hn2 C Mid Goal
      (2 * (n * (n - 1))) (2 * (7 * (Rmax + 4) * n * (n - 1)))
      ((2 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹) hMid hGoal
    have harith : ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((4 : ENNReal)⁻¹) := by
      rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]; norm_num
    rwa [harith] at hchain

/-- **Keystone 2 (consensus from a live swap).** From `InSswap` with a live, bounded
median timer, the expected time to consensus is bounded by the explicit renewal
polynomial `OW_consensusExpectedSteps`.

The only external hypothesis is the cited [12] return/ranking window
`hRank12`: from a timer-bounded correct-reset seed or live-swap exit, [12]
plus the epidemic drain reaches the silence endpoint with probability at least
`1/2` inside `OW_rank12Window`. The existing silence link
`isConsensusConfig_of_InSswap_phiCount_zero` turns that endpoint into consensus. -/
theorem OW_consensusBound (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (hRank12 :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        OW_restartBranch C →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C OW_silenceEndpoint
              (OW_rank12Window n Rmax)) :
    ∀ C : Config (AgentState n) Opinion n,
      InSswap C → MedianTimerAtLeast 1 C →
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        Probability.expectedHittingTime
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C IsConsensusConfig ≤
          ((OW_consensusExpectedSteps n Rmax : ℕ) : ENNReal) := by
  classical
  intro C₀ _hS₀ _hT₀ hB₀
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0 with hP
  let Inv : Config (AgentState n) Opinion n → Prop :=
    IsTimerBoundedConfig (7 * (Rmax + 4))
  let Live : Config (AgentState n) Opinion n → Prop :=
    fun C => InSswap C ∧ MedianTimerAtLeast 1 C
  let SwapEvent : Config (AgentState n) Opinion n → Prop :=
    fun C => IsConsensusConfig C ∨ CorrectResetSeed C ∨ ¬ Live C
  let SwapMid : Config (AgentState n) Opinion n → Prop :=
    fun C => SwapEvent C ∧ Inv C
  let K : ℕ := OW_consensusCycleWindow n Rmax
  have hKpos : 0 < K := by
    dsimp [K, OW_consensusCycleWindow, OW_swapWindow, OW_rank12Window]
    have _hnpos : 0 < n := by omega
    have _hRpos : 0 < Rmax := by omega
    positivity
  haveI : NeZero K := ⟨Nat.pos_iff_ne_zero.mp hKpos⟩
  have hp_le_one : ((8 : ENNReal)⁻¹) ≤ 1 := by norm_num
  have hInvStep : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j) := by
    intro C hC i j
    simpa [P, Inv] using
      PEMProtocolCoupled_preserves_timer_bounded hn0 C hC i j
  have hSilenceToConsensus :
      ∀ C : Config (AgentState n) Opinion n,
        OW_silenceEndpoint C → IsConsensusConfig C := by
    intro C hC
    exact isConsensusConfig_of_InSswap_phiCount_zero hC.1 hC.2.1 hC.2.2
  have hRankToConsensus :
      ∀ C : Config (AgentState n) Opinion n, Inv C → OW_restartBranch C →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            (OW_rank12Window n Rmax) := by
    intro C hInvC hBranch
    exact (hRank12 C hInvC hBranch).trans
      (Probability.ProbHitWithin_mono_goal P hn2 C
        OW_silenceEndpoint IsConsensusConfig hSilenceToConsensus
        (OW_rank12Window n Rmax))
  have hHalfFromSwapMid :
      ∀ C : Config (AgentState n) Opinion n, SwapMid C →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            (OW_rank12Window n Rmax) := by
    intro C hC
    rcases hC with ⟨hEvent, hInvC⟩
    rcases hEvent with hCons | hRest
    · have hOne : (1 : ENNReal) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            (OW_rank12Window n Rmax) := by
        calc
          (1 : ENNReal) = Probability.probReached P hn2 C IsConsensusConfig 0 := by
              exact (Probability.probReached_zero_of_goal P hn2 C IsConsensusConfig hCons).symm
          _ ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig 0 :=
              Probability.probReached_le_ProbHitWithin P hn2 C IsConsensusConfig 0
          _ ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig
                (OW_rank12Window n Rmax) :=
              Probability.ProbHitWithin_mono_time P hn2 C IsConsensusConfig (Nat.zero_le _)
      exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) hOne
    · exact hRankToConsensus C hInvC hRest
  have hWindow : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ¬ IsConsensusConfig C →
      ((8 : ENNReal)⁻¹) ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig K := by
    intro C hInvC _hNotCons
    by_cases hLive : Live C
    · have hSwap : ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C SwapMid (OW_swapWindow n Rmax) := by
        have hBase : ((4 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 C SwapEvent (OW_swapWindow n Rmax) := by
          simpa [P, Live, SwapEvent, OW_swapWindow] using
            swap_live_to_cons_or_crs_or_break
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn4 hn0 hRmax C hLive.1 hLive.2 hInvC
        rw [show Probability.ProbHitWithin P hn2 C SwapMid (OW_swapWindow n Rmax) =
            Probability.ProbHitWithin P hn2 C SwapEvent (OW_swapWindow n Rmax) by
          exact Probability.ProbHitWithin_eq_and_inv_of_invariant
            P hn2 C SwapEvent Inv hInvC hInvStep (OW_swapWindow n Rmax)]
        exact hBase
      have hChain : ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            (OW_swapWindow n Rmax + OW_rank12Window n Rmax) :=
        Probability.ProbHitWithin_add_ge_mul P hn2 C SwapMid IsConsensusConfig
          (OW_swapWindow n Rmax) (OW_rank12Window n Rmax)
          ((4 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹)
          hSwap hHalfFromSwapMid
      have hprod : ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((8 : ENNReal)⁻¹) := by
        rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        norm_num
      simpa [K, OW_consensusCycleWindow, hprod] using hChain
    · have hRank := hRankToConsensus C hInvC (Or.inr hLive)
      have hRankK : ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig K := by
        exact hRank.trans
          (Probability.ProbHitWithin_mono_time P hn2 C IsConsensusConfig
            (by
              dsimp [K, OW_consensusCycleWindow]
              omega))
      exact le_trans (by norm_num : ((8 : ENNReal)⁻¹) ≤ ((2 : ENNReal)⁻¹)) hRankK
  have hExpected :=
    Probability.expectedHittingTime_le_window_mul_inv_of_invariant
      P hn2 C₀ IsConsensusConfig Inv K ((8 : ENNReal)⁻¹)
      hp_le_one hB₀ hInvStep hWindow
  calc
    Probability.expectedHittingTime P hn2 C₀ IsConsensusConfig
        ≤ (K : ENNReal) * ((8 : ENNReal)⁻¹)⁻¹ := hExpected
    _ = ((OW_consensusExpectedSteps n Rmax : ℕ) : ENNReal) := by
        simp [K, OW_consensusExpectedSteps, OW_consensusCycleWindow, mul_comm]

/-- **Unconditional parallel-time bound modulo `hRank12`.** From any timer-bounded
initial configuration, the expected parallel time to consensus is controlled by
the ranking window, the proven swap window, and the consensus renewal above. -/
theorem PEM_expectedParallelTime_optimal (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRank12 :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        OW_restartBranch C →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C OW_silenceEndpoint
              (OW_rank12Window n Rmax)) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C₀ →
      Probability.expectedParallelTimeToConsensus
        (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀ ≤
        (((OW_globalWindow n Rmax : ℕ) : ENNReal) *
          ((16 : ENNReal)⁻¹)⁻¹ / n) := by
  classical
  intro C₀ hTimer₀
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0 with hP
  let Inv : Config (AgentState n) Opinion n → Prop :=
    IsTimerBoundedConfig (7 * (Rmax + 4))
  let RankTarget : Config (AgentState n) Opinion n → Prop :=
    fun C =>
      InSrank C ∧ MedianTimerAtLeast 35 C ∧
        IsTimerBoundedConfig (7 * (Rmax + 4)) C
  let SwapLiveTarget : Config (AgentState n) Opinion n → Prop :=
    fun C =>
      InSswap C ∧ MedianTimerAtLeast 1 C ∧
        IsTimerBoundedConfig (7 * (Rmax + 4)) C
  let K : ℕ := OW_globalWindow n Rmax
  have hKpos : 0 < K := by
    dsimp [K, OW_globalWindow, OW_consensusExpectedSteps, OW_consensusCycleWindow,
      OW_swapWindow, OW_rank12Window]
    have hnpos : 0 < n := by omega
    have hRpos : 0 < Rmax := by omega
    positivity
  haveI : NeZero K := ⟨Nat.pos_iff_ne_zero.mp hKpos⟩
  have hp_le_one : ((16 : ENNReal)⁻¹) ≤ 1 := by norm_num
  have hInvStep : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j) := by
    intro C hC i j
    simpa [P, Inv] using
      PEMProtocolCoupled_preserves_timer_bounded hn0 C hC i j
  have hRankBound := OW_rankBound
    (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn4 hRmax hEmax hDmax
  have hConsensusBound := OW_consensusBound
    (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn4 hRmax hEmax hDmax hRank12
  have hwin : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ¬ IsConsensusConfig C →
      ((16 : ENNReal)⁻¹) ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig K := by
    intro C hInvC _hNot
    have hRankE : Probability.expectedHittingTime P hn2 C RankTarget ≤
        ((Rmax * n * n : ℕ) : ENNReal) := by
      simpa [P, RankTarget, Inv] using hRankBound C hInvC
    have hRankW : 2 * (Rmax * n * n) ≤ (2 * Rmax * n * n) + 1 := by nlinarith
    have hRankPH : ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C RankTarget (2 * Rmax * n * n) :=
      Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
        P hn2 C RankTarget hRankE hRankW
    have hSwapPH : ∀ D : Config (AgentState n) Opinion n, RankTarget D →
        ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 D SwapLiveTarget (4 * n * n) := by
      intro D hD
      simpa [P, RankTarget, SwapLiveTarget] using
        PEM_swap_ProbHitWithin_InSswap_timer_live_const35_bounded
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn4 hn0 hRmax hEmax hDmax D hD.1 hD.2.1 hD.2.2
    have hConsE : ∀ D : Config (AgentState n) Opinion n, SwapLiveTarget D →
        Probability.expectedHittingTime P hn2 D IsConsensusConfig ≤
          ((OW_consensusExpectedSteps n Rmax : ℕ) : ENNReal) := by
      intro D hD
      simpa [P, SwapLiveTarget] using
        hConsensusBound D hD.1 hD.2.1 hD.2.2
    have hConsW :
        2 * OW_consensusExpectedSteps n Rmax ≤
          2 * OW_consensusExpectedSteps n Rmax + 1 := by omega
    have hConsPH : ∀ D : Config (AgentState n) Opinion n, SwapLiveTarget D →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 D IsConsensusConfig
            (2 * OW_consensusExpectedSteps n Rmax) := by
      intro D hD
      exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
        P hn2 D IsConsensusConfig (hConsE D hD) hConsW
    have hAB : ((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C SwapLiveTarget
          (2 * Rmax * n * n + 4 * n * n) :=
      Probability.ProbHitWithin_add_ge_mul P hn2 C RankTarget SwapLiveTarget
        (2 * Rmax * n * n) (4 * n * n)
        ((2 : ENNReal)⁻¹) ((4 : ENNReal)⁻¹)
        hRankPH hSwapPH
    have hChain : (((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹)) * ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig
          ((2 * Rmax * n * n + 4 * n * n) + 2 * OW_consensusExpectedSteps n Rmax) :=
      Probability.ProbHitWithin_add_ge_mul P hn2 C SwapLiveTarget IsConsensusConfig
        (2 * Rmax * n * n + 4 * n * n)
        (2 * OW_consensusExpectedSteps n Rmax)
        (((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹)) ((2 : ENNReal)⁻¹)
        hAB hConsPH
    have hprod :
        ((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) =
          ((16 : ENNReal)⁻¹) := by
      have h24 : ((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) = ((8 : ENNReal)⁻¹) := by
        rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        norm_num
      calc
        ((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹)
            = ((8 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) := by rw [h24]
        _ = ((16 : ENNReal)⁻¹) := by
            rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
            norm_num
    simpa [K, OW_globalWindow, hprod] using hChain
  simpa [Probability.expectedParallelTimeToConsensus, P, Inv, K] using
    (Probability.expectedParallelTime_le_window_mul_inv_of_invariant
      P hn2 C₀ IsConsensusConfig Inv K ((16 : ENNReal)⁻¹)
      hp_le_one hTimer₀ hInvStep hwin)

end

end SSEM
