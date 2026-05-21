/-
Handoff 030: counter-bound invariant proof snippets.

Do not import this file into the main build as-is.  It is written in a
separate namespace so it can be read as Lean code without colliding with
`Time.lean`.  To integrate, paste the proof bodies/lemmas into
`SSExactMajority/UpperBound/Time.lean` near the existing
`AgentCountersBounded` block, then drop the `Handoff030` namespace wrapper.

The main change from the failing attempt is that the expensive `grind` calls
are replaced by small `split_ifs`/`omega` proofs.  The two larger case splits
are wrapped in `set_option maxHeartbeats 400000 in`.

Local check status: this file passes
`lake env lean HANDOFF/outbox/2026-05-19-codex-030-invariant-proofs.lean`
with warnings only.  The final `PEMProtocol_preserves_bounded` skeleton and
the decomposition into smaller lemmas are the intended integration shape.
-/

import SSExactMajority.Defs.Config
import SSExactMajority.Protocol.RankDelta
import SSExactMajority.Protocol.Transition

namespace SSEM
namespace Handoff030

abbrev PEMProtocol (n Rmax Emax Dmax : ℕ) (hn : 0 < n) :
    Protocol (AgentState n) Opinion Output :=
  protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)

def IsBoundedConfig (M : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n,
    (C μ).1.timer ≤ M ∧
    (C μ).1.resetcount ≤ M ∧
    (C μ).1.errorcount ≤ M ∧
    (C μ).1.delaytimer ≤ M ∧
    (C μ).1.children ≤ M

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

set_option maxHeartbeats 400000 in
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

set_option maxHeartbeats 400000 in
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

set_option maxHeartbeats 400000 in
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

set_option maxHeartbeats 400000 in
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

private theorem transitionPEM_preserves_counter_bound
    {n Rmax Emax Dmax M : ℕ} {hn : 0 < n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hTimer : 7 * (Rmax + 4) ≤ M)
    (hRmax : Rmax ≤ M) (hEmax : Emax ≤ M) (hDmax : Dmax ≤ M)
    (hTwo : 2 ≤ M)
    (hs₀ : AgentCountersBounded M s₀) (hs₁ : AgentCountersBounded M s₁) :
    AgentCountersBounded M
        ((PEMProtocol n Rmax Emax Dmax hn).δ ((s₀, x₀), (s₁, x₁))).1 ∧
      AgentCountersBounded M
        ((PEMProtocol n Rmax Emax Dmax hn).δ ((s₀, x₀), (s₁, x₁))).2 := by
  have hrd :=
    rankDeltaOSSR_preserves_counter_bound (hn := hn)
      hRmax hEmax hDmax hTwo hs₀ hs₁
  have hpre :=
    transitionPEM_prePhase4_preserves_counter_bound
      (x₀ := x₀) (x₁ := x₁) hTimer hrd
  simpa [PEMProtocol, protocolPEM, transitionPEM] using
    transitionPEM_phase4_preserves_counter_bound
      (x₀ := x₀) (x₁ := x₁) hRmax hpre.1 hpre.2

theorem PEMProtocol_preserves_bounded
    {n Rmax Emax Dmax : ℕ} (hn : 0 < n) :
    let M := 7 * (Rmax + 4) + Emax + Dmax
    ∀ C : Config (AgentState n) Opinion n,
      IsBoundedConfig M C →
      ∀ i j : Fin n,
        IsBoundedConfig M (C.step (PEMProtocol n Rmax Emax Dmax hn) i j) := by
  classical
  change ∀ C : Config (AgentState n) Opinion n,
      IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C →
      ∀ i j : Fin n,
        IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax)
          (C.step (PEMProtocol n Rmax Emax Dmax hn) i j)
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

end Handoff030
end SSEM
