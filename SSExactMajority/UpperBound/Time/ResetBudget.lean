import SSExactMajority.Defs.Config
import SSExactMajority.Protocol.RankDelta
import SSExactMajority.Protocol.Transition
import Mathlib.Tactic

namespace SSEM

open scoped BigOperators

variable {n : ℕ}

/-- Ordered pairs of distinct settled agents with the same rank.  This is the
collision part of the reset budget: a collision reset removes at least the
scheduled ordered pair from this set. -/
def sameRankSettledPairs (C : Config (AgentState n) Opinion n) :
    Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter fun p =>
    p.1 ≠ p.2 ∧
      (C p.1).1.role = .Settled ∧
      (C p.2).1.role = .Settled ∧
      (C p.1).1.rank = (C p.2).1.rank

/-- Reset budget currently certified in this file: the number of ordered
same-rank settled collisions. -/
def resetBudget (C : Config (AgentState n) Opinion n) : ℕ :=
  (sameRankSettledPairs C).card

theorem resetBudget_le_quadratic (C : Config (AgentState n) Opinion n) :
    resetBudget C ≤ n * n := by
  classical
  unfold resetBudget sameRankSettledPairs
  calc
    ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun p : Fin n × Fin n =>
          p.1 ≠ p.2 ∧
            (C p.1).1.role = .Settled ∧
            (C p.2).1.role = .Settled ∧
            (C p.1).1.rank = (C p.2).1.rank)).card
        ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
          Finset.card_filter_le _ _
    _ = n * n := by simp

theorem rankDeltaOSSR_collision_roles
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Settled) (ht : t.role = .Settled)
    (hrank : s.rank = t.rank) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
      (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting := by
  unfold rankDeltaOSSR
  simp [hs, ht, hrank]

theorem transitionPEM_collision_roles
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} {x y : Opinion}
    (hs : s.role = .Settled) (ht : t.role = .Settled)
    (hrank : s.rank = t.rank) :
    (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((s, x), (t, y))).1.role = .Resetting ∧
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((s, x), (t, y))).2.role = .Resetting := by
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 rankDeltaOSSR
  simp [hs, ht, hrank]

/-- A fresh collision reset strictly decreases the certified collision budget.

The theorem is for the concrete coupled PEM transition using `rankDeltaOSSR`.
The two scheduled agents are Settled with the same rank, so the ranking
subprotocol makes both Resetting; phase 4 is then disabled, and every other
agent is unchanged. -/
theorem resetBudget_strict_decrease_at_collision
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n) {i j : Fin n}
    (hij : i ≠ j)
    (hi : (C i).1.role = .Settled)
    (hj : (C j).1.role = .Settled)
    (hrank : (C i).1.rank = (C j).1.rank) :
    resetBudget
        (C.step
          (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j) <
      resetBudget C := by
  classical
  let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P i j
  have hdelta :=
    transitionPEM_collision_roles
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := (C i).1) (t := (C j).1) (x := (C i).2) (y := (C j).2)
      hi hj hrank
  have hiReset : (C' i).1.role = .Resetting := by
    dsimp [C', P, protocolPEM, Config.step]
    simp [hij, hdelta.1]
  have hjReset : (C' j).1.role = .Resetting := by
    dsimp [C', P, protocolPEM, Config.step]
    simp [hij, hij.symm, hdelta.2]
  have hOther : ∀ w : Fin n, w ≠ i → w ≠ j → C' w = C w := by
    intro w hwi hwj
    dsimp [C', P, Config.step]
    simp [hij, hwi, hwj]
  have hsubset : sameRankSettledPairs C' ⊆ (sameRankSettledPairs C).erase (i, j) := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    rcases hp' with ⟨hpne, hp1Set, hp2Set, hprank⟩
    have hp1_ne_i : p.1 ≠ i := by
      intro h
      rw [h] at hp1Set
      rw [hiReset] at hp1Set
      cases hp1Set
    have hp1_ne_j : p.1 ≠ j := by
      intro h
      rw [h] at hp1Set
      rw [hjReset] at hp1Set
      cases hp1Set
    have hp2_ne_i : p.2 ≠ i := by
      intro h
      rw [h] at hp2Set
      rw [hiReset] at hp2Set
      cases hp2Set
    have hp2_ne_j : p.2 ≠ j := by
      intro h
      rw [h] at hp2Set
      rw [hjReset] at hp2Set
      cases hp2Set
    have hp_ne_pair : p ≠ (i, j) := by
      intro h
      exact hp1_ne_i (congrArg Prod.fst h)
    have hstate1 : C' p.1 = C p.1 := hOther p.1 hp1_ne_i hp1_ne_j
    have hstate2 : C' p.2 = C p.2 := hOther p.2 hp2_ne_i hp2_ne_j
    apply Finset.mem_erase.mpr
    constructor
    · exact hp_ne_pair
    · rw [sameRankSettledPairs, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hpne, ?_, ?_, ?_⟩
      · rw [← hstate1]
        exact hp1Set
      · rw [← hstate2]
        exact hp2Set
      · rw [← hstate1, ← hstate2]
        exact hprank
  have hijmem : (i, j) ∈ sameRankSettledPairs C := by
    rw [sameRankSettledPairs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hij, hi, hj, hrank⟩
  have hle := Finset.card_le_card hsubset
  have herase :
      ((sameRankSettledPairs C).erase (i, j)).card =
        (sameRankSettledPairs C).card - 1 :=
    Finset.card_erase_of_mem hijmem
  change (sameRankSettledPairs C').card < (sameRankSettledPairs C).card
  rw [herase] at hle
  have hpos : 0 < (sameRankSettledPairs C).card :=
    Finset.card_pos.mpr ⟨(i, j), hijmem⟩
  omega

end SSEM
