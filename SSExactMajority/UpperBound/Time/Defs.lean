/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# §5.2 Quantitative Upper Bound — scaffold

Kanaya §5.2 / Theorem 4 (quantitative): `P_EM` reaches a silent
configuration in O(n) expected parallel time and O(n log n) parallel time
with high probability on `n ≥ 4` agents under uniform random scheduling.
This scaffold states the Lean upper bound with an explicit
constant/externally bounded timer hypothesis; the literal
`protocolPEM n n n ...` timer range needs a separate theorem or a weakened
O(n²)-parallel statement.

Proof outline (`docs/TIME_BOUND_PLAN.md`):
- Phase A (ranking, Burman 2021 §3): O(n) expected parallel time.
- Phase B (swap): O(n) parallel time (`misorderedCount` decreases
  under uniform random pair selection).
- Phase C (decision/propagation/timer): O(n) expected parallel time.
- The constant-success phase argument gives O(n) expected time; repeating
  O(log n) windows gives O(n log n) with high probability.

This file is a **scaffold**.  The quantitative upper-bound claim is kept
as a target proposition until the phase-window stochastic proof is closed,
and the file lives outside the root import graph until then.  See
`docs/TIME_BOUND_PLAN.md` for the full plan.
-/

import SSExactMajority.Convergence.BurmanConvergenceFinal
import SSExactMajority.Probability.ExpectedTime
import Mathlib.Analysis.PSeries

namespace SSEM

open scoped ENNReal

/-- PEM protocol family used by the time-bound layer.

The paper treats `trank` (the ranking-time/timer parameter) separately from
`Rmax` (the reset-count parameter).  In particular, Kanaya §5.2 assumes
`trank = O(1)`, while some qualitative Lean wrappers instantiate both
parameters by the same value. -/
abbrev PEMProtocol (n trank Rmax Emax Dmax : ℕ) (hn : 0 < n) :
    Protocol (AgentState n) Opinion Output :=
  protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)

/-- Legacy/coupled time-layer instance used by the existing deterministic
proof blocks in this file.  This is not the paper's constant-`trank` regime
unless `Rmax` is externally bounded. -/
abbrev PEMProtocolCoupled (n Rmax Emax Dmax : ℕ) (hn : 0 < n) :
    Protocol (AgentState n) Opinion Output :=
  PEMProtocol n Rmax Rmax Emax Dmax hn

/-- Literal protocol instance from the current prompt.  The timer parameter is
linear in `n`, so Kanaya's constant-`trank` timer-drain argument does not
directly give an O(n) parallel-time bound for this instance. -/
abbrev ConcretePEM (n Emax Dmax : ℕ) (hn : 0 < n) :
    Protocol (AgentState n) Opinion Output :=
  PEMProtocol n n n Emax Dmax hn

/-! ### Initial configuration predicate -/

/-- A configuration is *initial* when every agent's internal state is at the
protocol's default: `Unsettled`, rank 0, no leader, all counters zero.
Only the input opinion varies.  This matches the standard population-protocol
initialization where agents carry only their input. -/
def IsInitialConfig (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n,
    (C μ).1.role = .Unsettled ∧
    (C μ).1.rank.val = 0 ∧
    (C μ).1.leader = .F ∧
    (C μ).1.resetcount = 0 ∧
    (C μ).1.timer = 0 ∧
    (C μ).1.answer = .outA ∧
    (C μ).1.errorcount = 0 ∧
    (C μ).1.delaytimer = 0 ∧
    (C μ).1.children = 0

/-- A weaker predicate: all internal counters are bounded by `M`.
This is preserved by protocol execution when `M` is large enough. -/
def IsBoundedConfig (M : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n,
    (C μ).1.timer ≤ M ∧
    (C μ).1.resetcount ≤ M ∧
    (C μ).1.errorcount ≤ M ∧
    (C μ).1.delaytimer ≤ M ∧
    (C μ).1.children ≤ M

def IsTimerBoundedConfig (K : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n, (C μ).1.timer ≤ K

theorem IsInitialConfig.isBounded {C : Config (AgentState n) Opinion n}
    (h : IsInitialConfig C) : IsBoundedConfig 0 C := by
  intro μ; obtain ⟨_, _, _, hr, ht, _, he, hd, hc⟩ := h μ
  exact ⟨le_of_eq ht, le_of_eq hr, le_of_eq he, le_of_eq hd, Nat.le_of_eq hc⟩

theorem IsInitialConfig.isTimerBounded {C : Config (AgentState n) Opinion n}
    (h : IsInitialConfig C) : IsTimerBoundedConfig 0 C := by
  intro μ; exact le_of_eq (h μ).2.2.2.2.1

/-! ### Phase predicates for the stochastic layer -/

/-- `Sdec`-style local decision predicate: every median-rank agent already
carries the current exact-majority answer.  For odd `n` this is the single
median agent; for even `n` this is the lower median used by
`ceilHalf`. -/
def MedianAnswerCorrect (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n,
    (C μ).1.rank.val + 1 = ceilHalf n →
      (C μ).1.answer = majorityAnswer C

/-- Live median timer predicate used by the decision/timer phase windows. -/
def MedianTimerAtLeast (k : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n,
    (C μ).1.rank.val + 1 = ceilHalf n →
      k ≤ (C μ).1.timer

theorem MedianTimerAtLeast.mono {a b : ℕ}
    (hab : a ≤ b) {C : Config (AgentState n) Opinion n} :
    MedianTimerAtLeast b C → MedianTimerAtLeast a C := by
  intro hb μ hμ
  exact le_trans hab (hb μ hμ)

def MedianTimerAtMost (k : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n,
    (C μ).1.rank.val + 1 = ceilHalf n →
      (C μ).1.timer ≤ k

/-- Paper Table-2 `Tswap`: ranked configuration with the median timer still
large enough for the decision-window Chernoff argument.  Since `InSrank`
gives a unique median rank, the universal form is equivalent to the paper's
existential median-agent formulation. -/
def InTswap28 (C : Config (AgentState n) Opinion n) : Prop :=
  InSrank C ∧ MedianTimerAtLeast 28 C

/-- Timer-bounded version of paper `Tswap`, used when a protocol invariant is
threaded through a phase proof. -/
def InTswap28TimerBounded (K : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  (InSrank C ∧ MedianTimerAtLeast 28 C ∧ MedianTimerAtMost K C) ∨
    IsConsensusConfig C

/-- After-swap version of paper `Tswap`, used by the current phase
composition: the swap work has already reached `Sswap`, and the median timer
still has the `28` units needed for the Lemma-9 survival/decision window. -/
def InTswap28SswapTimerBounded (K : ℕ)
    (C : Config (AgentState n) Opinion n) : Prop :=
  (InSswap C ∧ MedianTimerAtLeast 28 C ∧ MedianTimerAtMost K C) ∨
    IsConsensusConfig C

/-- Legacy helper, not paper `Tswap`: it starts after `Sswap` and requires only
positive median timer.  It is useful for already-closed coupled proofs, but is
too weak for the paper Lemma-9 timer-survival argument. -/
def InTswapTimerBounded (K : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  (InSswap C ∧ MedianTimerAtLeast 1 C ∧ MedianTimerAtMost K C) ∨
    IsConsensusConfig C

def InSdecTimerBounded (K : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  (InSswap C ∧ MedianAnswerCorrect C ∧ MedianTimerAtLeast 1 C ∧
      MedianTimerAtMost K C) ∨
    IsConsensusConfig C

theorem MedianTimerAtMost_of_IsTimerBounded
    {K : ℕ} {C : Config (AgentState n) Opinion n}
    (h : IsTimerBoundedConfig K C) : MedianTimerAtMost K C := by
  intro μ _hμ
  exact h μ

theorem RankingEndpoint.to_InSrank {C : Config (AgentState n) Opinion n}
    (h : RankingEndpoint C) : InSrank C :=
  h.1

theorem RankingEndpoint.to_timerAtLeast_two_or_consensus
    {C : Config (AgentState n) Opinion n}
    (h : RankingEndpoint C) :
    MedianTimerAtLeast 2 C ∨ IsConsensusConfig C :=
  h.2

theorem RankingEndpoint.to_InSrank_and_timerAtLeast_two_or_consensus
    {C : Config (AgentState n) Opinion n}
    (h : RankingEndpoint C) :
    (InSrank C ∧ MedianTimerAtLeast 2 C) ∨ IsConsensusConfig C := by
  rcases h.2 with hTimer | hCons
  · exact Or.inl ⟨h.1, hTimer⟩
  · exact Or.inr hCons

/-- A median-wrong witness is exactly the negation of
`MedianAnswerCorrect`. -/
theorem not_MedianAnswerCorrect_iff_exists_median_wrong
    {C : Config (AgentState n) Opinion n} :
    ¬ MedianAnswerCorrect C ↔
      ∃ μ : Fin n,
        (C μ).1.rank.val + 1 = ceilHalf n ∧
          (C μ).1.answer ≠ majorityAnswer C := by
  classical
  unfold MedianAnswerCorrect
  constructor
  · intro h
    push_neg at h
    exact h
  · rintro ⟨μ, hμ, hwrong⟩ hcorr
    exact hwrong (hcorr μ hμ)

theorem MedianAnswerCorrect_of_no_median_wrong
    {C : Config (AgentState n) Opinion n}
    (h :
      ¬ ∃ μ : Fin n,
        (C μ).1.rank.val + 1 = ceilHalf n ∧
          (C μ).1.answer ≠ majorityAnswer C) :
    MedianAnswerCorrect C := by
  classical
  rw [← not_MedianAnswerCorrect_iff_exists_median_wrong] at h
  exact not_not.mp h

end SSEM
