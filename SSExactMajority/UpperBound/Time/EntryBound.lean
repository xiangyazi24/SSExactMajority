import SSExactMajority.UpperBound.Time.RecoveryBound

namespace SSEM

open scoped ENNReal

variable {n : ℕ}

theorem rcLevelPotential_eq_zero_of_awakening
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C) :
    rcLevelPotential C = 0 := by
  classical
  have hmax0 : maxRC C = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply maxRC_le_of_all_le
    intro w hwR
    rcases hAwake with ⟨_hUnique, hLeaderOK, hFollowerOK⟩
    cases hwL : (C w).1.leader with
    | L =>
        have hwSettled := (hLeaderOK w hwL).1
        rw [hwR] at hwSettled
        cases hwSettled
    | F =>
        rcases hFollowerOK w hwL with hwUnsettled | hwReset
        · rw [hwR] at hwUnsettled
          cases hwUnsettled
        · exact Nat.le_of_eq hwReset.2
  unfold rcLevelPotential
  rw [if_pos hmax0]

theorem awakeningResettingFollowers_card_zero_of_fresh
    (C : Config (AgentState n) Opinion n)
    (hFresh : FreshRankingStart C) :
    (awakeningResettingFollowers C).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro w hw
  obtain ⟨root, hrootRole, _hrootRank, _hrootChildren, hothers⟩ := hFresh
  have hwR : (C w).1.role = .Resetting := (Finset.mem_filter.mp hw).2.2
  by_cases hwr : w = root
  · subst w
    rw [hrootRole] at hwR
    cases hwR
  · have hwUnsettled := hothers w hwr
    rw [hwUnsettled] at hwR
    cases hwR

theorem freshRankingStart_of_awakening_no_resetting_followers
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C)
    (hNoFollowers : (awakeningResettingFollowers C).card = 0) :
    FreshRankingStart C := by
  classical
  rcases hAwake with ⟨hUnique, hLeaderOK, hFollowerOK⟩
  obtain ⟨root, hrootL, hrootUnique⟩ := hUnique
  have hrootOK := hLeaderOK root hrootL
  refine ⟨root, hrootOK.1, hrootOK.2.1, hrootOK.2.2, ?_⟩
  intro w hwroot
  have hwF : (C w).1.leader = .F := by
    cases hwL : (C w).1.leader with
    | L =>
        exact False.elim (hwroot (hrootUnique w hwL))
    | F => rfl
  rcases hFollowerOK w hwF with hwUnsettled | hwReset
  · exact hwUnsettled
  · exfalso
    have hmem : w ∈ awakeningResettingFollowers C := by
      dsimp [awakeningResettingFollowers]
      simp [hwF, hwReset.1]
    have hpos : 0 < (awakeningResettingFollowers C).card :=
      Finset.card_pos.mpr ⟨w, hmem⟩
    omega

theorem freshRankingStart_iff_awakeningResettingFollowers_card_zero_of_awakening
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C) :
    FreshRankingStart C ↔ (awakeningResettingFollowers C).card = 0 := by
  constructor
  · exact awakeningResettingFollowers_card_zero_of_fresh C
  · exact freshRankingStart_of_awakening_no_resetting_followers C hAwake

theorem awakening_step_descent_witness
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C)
    (hpos : 0 < (awakeningResettingFollowers C).card) :
    ∃ root w : Fin n, root ≠ w ∧
      let P := PEMProtocolCoupled' n Rmax Emax Dmax hn
      let C' := C.step P root w
      IsAwakeningConfig C' ∧
        (awakeningResettingFollowers C').card <
          (awakeningResettingFollowers C).card := by
  classical
  rcases hAwake with ⟨hUnique, hLeaderOK, hFollowerOK⟩
  obtain ⟨root, hrootL, hrootUnique⟩ := hUnique
  obtain ⟨w, hwBad⟩ := Finset.card_pos.mp hpos
  have hwF : (C w).1.leader = .F := (Finset.mem_filter.mp hwBad).2.1
  have hwR : (C w).1.role = .Resetting := (Finset.mem_filter.mp hwBad).2.2
  have hwRc : (C w).1.resetcount = 0 := by
    rcases hFollowerOK w hwF with hwUnsettled | hwReset
    · rw [hwUnsettled] at hwR
      cases hwR
    · exact hwReset.2
  have hrootNeW : root ≠ w := by
    intro hrw
    subst w
    rw [hrootL] at hwF
    cases hwF
  let P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  let C' : Config (AgentState n) Opinion n := C.step P root w
  have hrootOK := hLeaderOK root hrootL
  have htrace := by
    simpa [P, PEMProtocolCoupled', C'] using
      (transitionPEM_settled_meets_dormant_trace
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 (C := C) (ℓ := root) (w := w) hrootNeW
        hrootOK.1 hrootOK.2.1 hrootOK.2.2 hrootL
        hwR hwRc hwF)
  have hOthers : ∀ x : Fin n, x ≠ root → x ≠ w → C' x = C x := by
    intro x hxroot hxw
    dsimp [C', P, PEMProtocolCoupled']
    simp [Config.step, hrootNeW, hxroot, hxw]
  have hAwake' : IsAwakeningConfig C' := by
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨root, htrace.2.2.2.1, ?_⟩
      intro y hyL
      by_cases hyroot : y = root
      · exact hyroot
      · by_cases hyw : y = w
        · subst y
          rw [htrace.2.2.2.2.2] at hyL
          cases hyL
        · have hyOld : (C y).1.leader = .L := by
            have hyState := hOthers y hyroot hyw
            rw [hyState] at hyL
            exact hyL
          exact hrootUnique y hyOld
    · intro y hyL
      have hyroot : y = root := by
        by_cases hyroot : y = root
        · exact hyroot
        · by_cases hyw : y = w
          · subst y
            rw [htrace.2.2.2.2.2] at hyL
            cases hyL
          · have hyOld : (C y).1.leader = .L := by
              have hyState := hOthers y hyroot hyw
              rw [hyState] at hyL
              exact hyL
            exact hrootUnique y hyOld
      subst y
      exact ⟨htrace.1, htrace.2.1, htrace.2.2.1⟩
    · intro y hyF
      by_cases hyroot : y = root
      · subst y
        rw [htrace.2.2.2.1] at hyF
        cases hyF
      · by_cases hyw : y = w
        · subst y
          exact Or.inl htrace.2.2.2.2.1
        · have hyOldF : (C y).1.leader = .F := by
            have hyState := hOthers y hyroot hyw
            rw [hyState] at hyF
            exact hyF
          rw [hOthers y hyroot hyw]
          exact hFollowerOK y hyOldF
  have hsubset :
      awakeningResettingFollowers C' ⊆ (awakeningResettingFollowers C).erase w := by
    intro x hx
    have hxF : (C' x).1.leader = .F := (Finset.mem_filter.mp hx).2.1
    have hxR : (C' x).1.role = .Resetting := (Finset.mem_filter.mp hx).2.2
    have hxNeW : x ≠ w := by
      intro hxw
      subst x
      rw [htrace.2.2.2.2.1] at hxR
      cases hxR
    have hxNeRoot : x ≠ root := by
      intro hxroot
      subst x
      rw [htrace.1] at hxR
      cases hxR
    have hxOldState := hOthers x hxNeRoot hxNeW
    have hxOld : x ∈ awakeningResettingFollowers C := by
      dsimp [awakeningResettingFollowers]
      rw [hxOldState] at hxF hxR
      simp [hxF, hxR]
    exact Finset.mem_erase.mpr ⟨hxNeW, hxOld⟩
  have hcardLt : (awakeningResettingFollowers C').card <
      (awakeningResettingFollowers C).card := by
    have hle := Finset.card_le_card hsubset
    have herase : ((awakeningResettingFollowers C).erase w).card =
        (awakeningResettingFollowers C).card - 1 :=
      Finset.card_erase_of_mem hwBad
    rw [herase] at hle
    omega
  exact ⟨root, w, hrootNeW, hAwake', hcardLt⟩

theorem awakening_step_descent_prob
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (k : ℕ) (hk : 0 < k)
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C)
    (hcard : (awakeningResettingFollowers C).card = k) :
    (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled' n Rmax Emax Dmax hn)
        (by omega : 2 ≤ n) C
        (fun D =>
          FreshRankingStart D ∨
            (IsAwakeningConfig D ∧
              (awakeningResettingFollowers D).card < k)) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      FreshRankingStart D ∨
        (IsAwakeningConfig D ∧
          (awakeningResettingFollowers D).card < k)
  have hpos : 0 < (awakeningResettingFollowers C).card := by
    rw [hcard]
    exact hk
  obtain ⟨root, w, hrootNeW, hAwake', hlt⟩ :=
    awakening_step_descent_witness
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C hAwake hpos
  have hstep : Goal (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) root w) := by
    right
    exact ⟨hAwake', by simpa [hcard] using hlt⟩
  by_cases hGoal : Goal C
  · have hzero :
        Probability.ProbHitWithin
          (PEMProtocolCoupled' n Rmax Emax Dmax hn)
          (by omega : 2 ≤ n) C Goal 0 = 1 :=
      Probability.probHitBy_zero_of_goal
        (PEMProtocolCoupled' n Rmax Emax Dmax hn)
        (by omega : 2 ≤ n) C Goal hGoal
    calc
      (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤ 1 := by
        exact ENNReal.inv_le_one.mpr (by
          have hn1 : 1 ≤ n := by omega
          have hpred1 : 1 ≤ n - 1 := by omega
          exact_mod_cast (Nat.mul_le_mul hn1 hpred1))
      _ = Probability.ProbHitWithin
            (PEMProtocolCoupled' n Rmax Emax Dmax hn)
            (by omega : 2 ≤ n) C Goal 0 := hzero.symm
      _ ≤ Probability.ProbHitWithin
            (PEMProtocolCoupled' n Rmax Emax Dmax hn)
            (by omega : 2 ≤ n) C Goal 1 :=
          Probability.ProbHitWithin_mono_time
            (PEMProtocolCoupled' n Rmax Emax Dmax hn)
            (by omega : 2 ≤ n) C Goal (by omega)
  · exact Probability.ProbHitWithin_one_lower_bound_of_step
      (PEMProtocolCoupled' n Rmax Emax Dmax hn)
      (by omega : 2 ≤ n) C Goal hGoal hrootNeW hstep

end SSEM
