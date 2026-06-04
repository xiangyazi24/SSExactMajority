import Mathlib.Data.Nat.Log
import SSExactMajority.Convergence.BurmanConvergenceFinal

namespace SSEM

def FreshResettingAt {n : ℕ} (Dmax : ℕ)
    (C : Config (AgentState n) Opinion n) (w : Fin n) : Prop :=
  (C w).1.role = .Resetting ∧
  (C w).1.resetcount = 0 ∧
  (C w).1.delaytimer = Dmax

def pairEndpoints {n : ℕ} : List (Fin n × Fin n) → Finset (Fin n)
  | [] => ∅
  | (u, v) :: ps => insert u (insert v (pairEndpoints ps))

def PairListDisjoint {n : ℕ} : List (Fin n × Fin n) → Prop
  | [] => True
  | (u, v) :: ps =>
      u ≠ v ∧ u ∉ pairEndpoints ps ∧ v ∉ pairEndpoints ps ∧ PairListDisjoint ps

theorem rankDeltaOSSR_both_rc_pos_snd_delay_final
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 0 < s.resetcount) (ht_rc : 0 < t.resetcount)
    (hnew : Nat.max (s.resetcount - 1) (t.resetcount - 1) = 0)
    (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.delaytimer = Dmax := by
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs, ht, hs_rc, ht_rc, hnew, show (Dmax : ℕ) ≠ 0 from by omega]
  by_cases hLL : s.leader = .L ∧ t.leader = .L <;> simp [hLL]

set_option maxHeartbeats 4000000 in
-- Transporting the rank-delta delay trace through `transitionPEM` exposes a
-- deeply nested structural passthrough tuple.
theorem step_both_rc_pos_snd_delay_final
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hnew : Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) = 0) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' v).1.delaytimer = Dmax := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd_role := rankDeltaOSSR_both_rc_pos_role (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hDmax
  have h_rd_delay := rankDeltaOSSR_both_rc_pos_snd_delay_final
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hnew hDmax
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd_role.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_snd := Config.step_snd_state P C huv huv.symm
  change (C.step P u v v).1.delaytimer = Dmax
  rw [congrArg AgentState.delaytimer h_snd]
  exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd_delay

set_option maxHeartbeats 8000000 in
-- The proof mirrors the existing one-sided pair-drain induction while carrying
-- the extra symmetric delaytimer endpoint.
theorem drain_pair_rc_with_both_delay
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      FreshResettingAt Dmax (runPairs P C L) u ∧
      FreshResettingAt Dmax (runPairs P C L) v ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices drain : ∀ k (C' : Config (AgentState n) Opinion n),
      (C' u).1.role = .Resetting → (C' v).1.role = .Resetting →
      0 < (C' u).1.resetcount → 0 < (C' v).1.resetcount →
      Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) ≤ k →
      ∃ L,
        FreshResettingAt Dmax (runPairs P C' L) u ∧
        FreshResettingAt Dmax (runPairs P C' L) v ∧
        ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C' L w = C' w by
    exact drain (Nat.max ((C u).1.resetcount) ((C v).1.resetcount))
      C hu_res hv_res hu_rc hv_rc le_rfl
  intro k
  induction k with
  | zero =>
      intros C' _ _ hu_rc' _ hmax
      exfalso
      have hle : (C' u).1.resetcount ≤
          Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) :=
        Nat.le_max_left _ _
      omega
  | succ k ih =>
      intros C' hu_res' hv_res' hu_rc' hv_rc' hmax
      have h_step := step_both_rc_pos (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc'
      have hu_role₁ : (C'.step P u v u).1.role = .Resetting := h_step.1
      have hv_role₁ : (C'.step P u v v).1.role = .Resetting := h_step.2.1
      have hu_rc₁_eq : (C'.step P u v u).1.resetcount =
          Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) :=
        h_step.2.2.1
      have hv_rc₁_eq : (C'.step P u v v).1.resetcount =
          Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) :=
        h_step.2.2.2.1
      have h_others : ∀ w, w ≠ u → w ≠ v → C'.step P u v w = C' w := by
        intro w hwu hwv
        simp [Config.step, huv, hwu, hwv]
      have hM_le :
          Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount) ≤ k := by
        have hu_pred_le : (C' u).1.resetcount - 1 ≤ k := by
          have hu_le_succ : (C' u).1.resetcount ≤ k + 1 :=
            Nat.le_trans (Nat.le_max_left ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
          omega
        have hv_pred_le : (C' v).1.resetcount - 1 ≤ k := by
          have hv_le_succ : (C' v).1.resetcount ≤ k + 1 :=
            Nat.le_trans (Nat.le_max_right ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
          omega
        have hpred :
            Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) ≤ k :=
          max_le hu_pred_le hv_pred_le
        rw [hu_rc₁_eq, hv_rc₁_eq]
        exact max_le hpred hpred
      by_cases hdone :
          Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount) = 0
      · have hu_zero : (C'.step P u v u).1.resetcount = 0 := by
          have hle := Nat.le_max_left ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount)
          exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
        have hv_zero : (C'.step P u v v).1.resetcount = 0 := by
          have hle := Nat.le_max_right ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount)
          exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
        have hnew :
            Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) = 0 := by
          have hdone' := hdone
          rw [hu_rc₁_eq, hv_rc₁_eq] at hdone'
          simpa using hdone'
        have hu_delay₁ : (C'.step P u v u).1.delaytimer = Dmax :=
          step_both_rc_pos_fst_delay_final
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc' hnew
        have hv_delay₁ : (C'.step P u v v).1.delaytimer = Dmax :=
          step_both_rc_pos_snd_delay_final
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc' hnew
        refine ⟨[(u, v)], ?_, ?_, ?_⟩
        · change FreshResettingAt Dmax (C'.step P u v) u
          exact ⟨hu_role₁, hu_zero, hu_delay₁⟩
        · change FreshResettingAt Dmax (C'.step P u v) v
          exact ⟨hv_role₁, hv_zero, hv_delay₁⟩
        · intro w hwu hwv
          change C'.step P u v w = C' w
          exact h_others w hwu hwv
      · have hu_pos₁ : 0 < (C'.step P u v u).1.resetcount := by
          have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
              ((C'.step P u v v).1.resetcount) :=
            Nat.pos_of_ne_zero hdone
          simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
        have hv_pos₁ : 0 < (C'.step P u v v).1.resetcount := by
          have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
              ((C'.step P u v v).1.resetcount) :=
            Nat.pos_of_ne_zero hdone
          simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
        obtain ⟨Ltail, hu_fresh_t, hv_fresh_t, h_others_t⟩ :=
          ih (C'.step P u v) hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hM_le
        refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_⟩
        · rw [runPairs_append]
          change FreshResettingAt Dmax (runPairs P (C'.step P u v) Ltail) u
          simpa [runPairs] using hu_fresh_t
        · rw [runPairs_append]
          change FreshResettingAt Dmax (runPairs P (C'.step P u v) Ltail) v
          simpa [runPairs] using hv_fresh_t
        · intro w hwu hwv
          rw [runPairs_append]
          change runPairs P (C'.step P u v) Ltail w = C' w
          rw [h_others_t w hwu hwv]
          exact h_others w hwu hwv

theorem drain_pair_list_to_fresh_on_endpoints
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (pairs : List (Fin n × Fin n))
    (C : Config (AgentState n) Opinion n)
    (hdis : PairListDisjoint pairs)
    (hAllReset : ∀ w : Fin n, w ∈ pairEndpoints pairs → (C w).1.role = .Resetting)
    (hAllPos : ∀ w : Fin n, w ∈ pairEndpoints pairs → 0 < (C w).1.resetcount) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (∀ w : Fin n, w ∈ pairEndpoints pairs →
        FreshResettingAt Dmax (runPairs P C L) w) ∧
      (∀ w : Fin n, w ∉ pairEndpoints pairs → runPairs P C L w = C w) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  induction pairs generalizing C with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · intro w hw
        simp [pairEndpoints] at hw
      · intro w _hw
        simp only [runPairs_nil]
  | cons p ps ih =>
      rcases p with ⟨u, v⟩
      rcases hdis with ⟨huv, hu_not_tail, hv_not_tail, hdis_tail⟩
      have hu_mem : u ∈ pairEndpoints ((u, v) :: ps) := by
        simp [pairEndpoints]
      have hv_mem : v ∈ pairEndpoints ((u, v) :: ps) := by
        simp [pairEndpoints]
      obtain ⟨Luv, hu_fresh, hv_fresh, hothers⟩ :=
        drain_pair_rc_with_both_delay
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax C huv (hAllReset u hu_mem) (hAllReset v hv_mem)
          (hAllPos u hu_mem) (hAllPos v hv_mem)
      let C₁ : Config (AgentState n) Opinion n := runPairs P C Luv
      have hAllReset_tail :
          ∀ w : Fin n, w ∈ pairEndpoints ps → (C₁ w).1.role = .Resetting := by
        intro w hw
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hu_not_tail hw
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hv_not_tail hw
        have hw_cons : w ∈ pairEndpoints ((u, v) :: ps) := by
          simp [pairEndpoints, hw]
        dsimp [C₁]
        rw [hothers w hwu hwv]
        exact hAllReset w hw_cons
      have hAllPos_tail :
          ∀ w : Fin n, w ∈ pairEndpoints ps → 0 < (C₁ w).1.resetcount := by
        intro w hw
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hu_not_tail hw
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hv_not_tail hw
        have hw_cons : w ∈ pairEndpoints ((u, v) :: ps) := by
          simp [pairEndpoints, hw]
        dsimp [C₁]
        rw [hothers w hwu hwv]
        exact hAllPos w hw_cons
      obtain ⟨Ltail, hfresh_tail, hunchanged_tail⟩ :=
        ih C₁ hdis_tail hAllReset_tail hAllPos_tail
      refine ⟨Luv ++ Ltail, ?_, ?_⟩
      · intro w hw
        rw [runPairs_append]
        change FreshResettingAt Dmax (runPairs P C₁ Ltail) w
        have hw' := hw
        simp only [pairEndpoints, Finset.mem_insert] at hw'
        rcases hw' with hwu_eq | hv_or_tail
        · subst w
          have hkeep := hunchanged_tail _ hu_not_tail
          unfold FreshResettingAt
          rw [hkeep]
          simpa [FreshResettingAt, C₁, P] using hu_fresh
        · rcases hv_or_tail with hwv_eq | htail
          · subst w
            have hkeep := hunchanged_tail _ hv_not_tail
            unfold FreshResettingAt
            rw [hkeep]
            simpa [FreshResettingAt, C₁, P] using hv_fresh
          · exact hfresh_tail w htail
      · intro w hw
        rw [runPairs_append]
        change runPairs P C₁ Ltail w = C w
        have hnot_tail : w ∉ pairEndpoints ps := by
          intro htail
          exact hw (by simp [pairEndpoints, htail])
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hw (by simp [pairEndpoints])
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hw (by simp [pairEndpoints])
        rw [hunchanged_tail w hnot_tail]
        exact hothers w hwu hwv

/-- Log-fuel reset drain from an explicit balanced-growth certificate.

The theorem discharges the deterministic Phase B exactly: once a Phase A
schedule grown from a log-fueled seed has made every agent Resetting with
positive resetcount, any disjoint covering pair list can be drained without
selecting dormant agents again, ending with every agent Resetting, resetcount
zero, and delaytimer exactly `Dmax`.

The remaining Phase A combinatorics are isolated in `hBalancedTreeGrowth`;
this is the explicit precondition that a later balanced-doubling construction
must remove. -/
theorem all_fresh_from_log_seed
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax R : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hfuel : Nat.clog 2 n + 1 ≤ R)
    (C : Config (AgentState n) Opinion n)
    (hseed : ∃ r : Fin n, (C r).1.role = .Resetting ∧ R ≤ (C r).1.resetcount)
    (hBalancedTreeGrowth :
      ∀ r : Fin n,
        (C r).1.role = .Resetting →
        Nat.clog 2 n + 1 ≤ (C r).1.resetcount →
        ∃ Lgrow : List (Fin n × Fin n),
          let C₁ := runPairs (protocolPEM n Rmax Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C Lgrow
          ∀ w : Fin n, (C₁ w).1.role = .Resetting ∧ 0 < (C₁ w).1.resetcount)
    (pairs : List (Fin n × Fin n))
    (hdis : PairListDisjoint pairs)
    (hcover : ∀ w : Fin n, w ∈ pairEndpoints pairs) :
    ∃ L : List (Fin n × Fin n),
      let C₂ := runPairs (protocolPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      ∀ w : Fin n, FreshResettingAt Dmax C₂ w := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨r, hr_role, hr_fuel⟩ := hseed
  have hr_log : Nat.clog 2 n + 1 ≤ (C r).1.resetcount :=
    Nat.le_trans hfuel hr_fuel
  obtain ⟨Lgrow, hAllPositive⟩ := hBalancedTreeGrowth r hr_role hr_log
  let C₁ : Config (AgentState n) Opinion n := runPairs P C Lgrow
  have hAllReset_pairs :
      ∀ w : Fin n, w ∈ pairEndpoints pairs → (C₁ w).1.role = .Resetting := by
    intro w _
    exact (hAllPositive w).1
  have hAllPos_pairs :
      ∀ w : Fin n, w ∈ pairEndpoints pairs → 0 < (C₁ w).1.resetcount := by
    intro w _
    exact (hAllPositive w).2
  obtain ⟨Ldrain, hfresh, _hunchanged⟩ :=
    drain_pair_list_to_fresh_on_endpoints
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax pairs C₁ hdis hAllReset_pairs hAllPos_pairs
  refine ⟨Lgrow ++ Ldrain, ?_⟩
  change ∀ w : Fin n, FreshResettingAt Dmax (runPairs P C (Lgrow ++ Ldrain)) w
  intro w
  rw [runPairs_append]
  exact hfresh w (hcover w)

end SSEM
