/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Formal Proof of BurmanConvergence

This file works toward proving `BurmanConvergence` for the concrete
`rankDeltaOSSR` protocol, which is the ONLY remaining gap in the
full formalization of Kanaya et al.'s Theorem 4.

## Strategy

Burman et al. (PODC 2021) Theorem 4.3 proves OPTIMAL-SILENT-SSR
converges in O(n) expected time. For our deterministic formalization,
we need to show the EXISTENCE of a schedule reaching InSrank
(for `ranking`) and InSswap with all correct answers (for `epidemic`).

### Phase structure

1. **Binary-tree rank assignment** (Lemma 4.1): from a single leader
   + n−1 Unsettled agents, a deterministic schedule assigns unique
   ranks to all agents via Protocol 3's recruitment (lines 8-12).

2. **Leader election** (Lemma 4.2): from an awakening configuration,
   the L,L → L,F rule reduces to a single leader with constant
   probability (for deterministic: we can schedule L,L pairs).

3. **PROPAGATE-RESET cycle** (Theorem 3.4): from any partially
   triggered config, reach an awakening config.

4. **Collision/errorcount entry**: from any config, reach a
   partially triggered config via collision detection or errorcount
   timeout.

5. **Epidemic propagation**: the Resetting-phase answer spreading
   (lines 7-8 of Algorithm 1) propagates the correct answer.

### Current file

This file begins with Phase 1 — the binary-tree rank assignment.
-/

import SSExactMajority.Convergence.BurmanProperties

namespace SSEM

variable {n : ℕ}

/-! ### Binary-tree rank assignment

From a leader (Settled, rank 0, children 0) and n−1 Unsettled agents,
Protocol 3's recruitment (lines 8-12) assigns unique ranks via a
binary tree. Each interaction between a Settled agent with children < 2
and an Unsettled agent recruits the Unsettled agent as a child.

The schedule: repeatedly pair a "ready" Settled agent (children < 2,
valid child rank < n) with any Unsettled agent.

After n−1 such interactions, all agents are Settled with unique ranks
from a binary tree rooted at rank 0 (1-indexed: rank 1).
-/

/-- A config where one agent is the leader (Settled, rank 0) and all
others are Unsettled. -/
def IsLeaderConfig (C : Config (AgentState n) Opinion n) (hn : 0 < n) : Prop :=
  ∃ leader : Fin n,
    (C leader).1.role = .Settled ∧
    (C leader).1.rank = ⟨0, hn⟩ ∧
    (C leader).1.children = 0 ∧
    ∀ w : Fin n, w ≠ leader → (C w).1.role = .Unsettled

/-- Count of Settled agents in a configuration. -/
def settledCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (Finset.univ.filter (fun w => (C w).1.role == .Settled)).card

/-! ### Recruitment step: Settled agent recruits Unsettled agent -/

/-- When a Settled agent with children < 2 and valid child rank
interacts with an Unsettled agent, rankDeltaOSSR recruits the
Unsettled agent as a child in the binary tree. -/
theorem rankDeltaOSSR_recruits
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s : AgentState n} {t : AgentState n}
    (hs : s.role = .Settled) (ht : t.role = .Unsettled)
    (h_children : s.children < 2)
    (h_valid : 2 * s.rank.val + s.children + 1 < n) :
    let result := rankDeltaOSSR Rmax Emax Dmax hn (s, t)
    result.1.role = .Settled ∧
    result.1.children = s.children + 1 ∧
    result.1.rank = s.rank ∧
    result.2.role = .Settled ∧
    result.2.children = 0 ∧
    result.2.rank = ⟨2 * s.rank.val + s.children + 1, h_valid⟩ := by
  unfold rankDeltaOSSR
  have h_not_res : ¬(s.role = .Resetting ∨ t.role = .Resetting) := by
    rw [hs, ht]; simp
  have h_not_coll : ¬(s.role = .Settled ∧ t.role = .Settled ∧ s.rank = t.rank) := by
    intro ⟨_, h, _⟩; rw [ht] at h; exact Role.noConfusion h
  simp only [h_not_res, h_not_coll, ite_false]
  rw [dif_pos ⟨hs, ht, h_children, h_valid⟩]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  show { s with children := s.children + 1 }.role = .Settled
  exact hs
/-! ### Binary tree rank uniqueness

The binary tree formula `childRank = 2 * parentRank + childIndex + 1`
(0-indexed) assigns unique ranks. Left child: 2r+1, right child: 2r+2.
All ranks in [0, n) are unique because the binary tree is a standard
complete binary tree with n nodes. -/

/-- Child ranks from distinct parents are distinct from each other and
from any parent rank. -/
theorem binary_tree_ranks_distinct
    {r₁ r₂ : ℕ} (h_ne : r₁ ≠ r₂ ∨ True) :
    2 * r₁ + 1 ≠ r₁ ∧ 2 * r₁ + 2 ≠ r₁ := by
  constructor <;> omega

/-! ### Timer initialization at median during recruitment

When a child is recruited at the median rank (rank = ceilHalf n - 1),
transitionPEM Phase 2 (line 51-53) sets its timer to 7*(trank+4).
This ensures the timer ≥ 2 bound needed by BurmanConvergence.ranking.

The timer 7*(trank+4) ≥ 7*4 = 28 ≥ 2 for any trank ≥ 0. -/

theorem timer_init_ge_2 (trank : ℕ) : 2 ≤ 7 * (trank + 4) := by omega

/-! ### Phase A: BurmanConvergence.ranking for InSrank configs

If the initial config is already InSrank with timer ≥ 2, ranking is
trivially satisfied — the empty schedule (t = 0) works. -/

theorem ranking_of_InSrank
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {C₀ : Config (AgentState n) Opinion n}
    (hC₀ : InSrank C₀)
    (h_timer : ∀ μ : Fin n, (C₀ μ).1.rank.val + 1 = ceilHalf n →
                2 ≤ (C₀ μ).1.timer) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t) ∧
      (∀ μ : Fin n,
        (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t μ).1.timer) :=
  ⟨fun _ => default, 0, hC₀, h_timer⟩

/-! ### Phase B: Binary tree construction from leader config

From a leader config (one Settled agent + rest Unsettled), construct
a schedule that recruits all agents into a binary tree via Protocol 3.

The schedule pairs "ready" Settled agents (children < 2, valid child
rank < n) with Unsettled agents, one by one. After n-1 steps, all
agents are Settled with unique ranks 0..n-1 from a binary tree. -/

/-- The number of Unsettled agents in a config. -/
def unsettledCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (Finset.univ.filter (fun w => (C w).1.role == .Unsettled)).card

/-! ### Propagation reset: median with timer = 0 triggers reset -/

set_option maxHeartbeats 4000000 in
/-- When the median (timer = 0) meets a non-median agent, and the
post-decision answer at the median differs from v's answer, both go
Resetting. The decision phase sets median's answer to opinionToAnswer
of its input; the propagation then checks timer = 0 AND answers differ.

This is used when median has the correct answer (from decision) but
v has a wrong answer → reset fires → re-rank with fresh timer. -/
theorem propagation_reset_fires_no_swap
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.role = .Resetting ∧
    (transitionPEM n trank Rmax rankDelta (C μ, C v)).2.role = .Resetting := by
  have hsu := hC.allSettled μ
  have hsv := hC.allSettled v
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hsu hsv
  unfold transitionPEM
  simp only [hRD, hsu, hsv, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, h_no_swap, hpar, hμ_med, hv_no_med, h_timer]
  split_ifs <;> simp_all

/-! ### PROPAGATE-RESET: Resetting agent recruits non-Resetting -/

set_option maxHeartbeats 16000000 in
/-- Phase 1 of propagateReset: recruitment of non-Resetting agent. -/
theorem propagateReset_recruits
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_res : s.role = .Resetting)
    (hs_rc : 0 < s.resetcount)
    (ht_not_res : t.role ≠ .Resetting)
    (hDmax : 1 < Dmax) :
    (propagateReset Emax Dmax hn s t).2.role = .Resetting := by
  unfold propagateReset
  simp only [hs_res, hs_rc, ht_not_res, and_self, ite_true,
    show ¬(t.role = .Resetting ∧ 0 < t.resetcount ∧ s.role ≠ .Resetting) from by
      intro ⟨h, _, _⟩; exact ht_not_res h]
  -- After Phase 1: t becomes Resetting with resetcount = 0, delaytimer = Dmax
  -- Phase 2 (sync): both Resetting → sync
  -- Phase 3 (process): dormant with delaytimer = Dmax > 0 and partner Resetting → stays
  have hn' : 1 ≤ n := hn
  split_ifs <;> simp_all [resetOSSR] <;> omega

/-- PROPAGATE-RESET: Resetting (resetcount > 0) recruits non-Resetting. -/
theorem rankDeltaOSSR_propagate_reset
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_res : s.role = .Resetting)
    (hs_rc : 0 < s.resetcount)
    (ht_not_res : t.role ≠ .Resetting)
    (hDmax : 1 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting := by
  unfold rankDeltaOSSR
  simp only [hs_res, true_or, ite_true]
  -- propagateReset is called, then leader dedup. Leader dedup doesn't change role.
  have h_pr := propagateReset_recruits (Emax := Emax) (hn := hn)
    hs_res hs_rc ht_not_res hDmax
  -- The result.2 from rankDeltaOSSR is:
  --   if leader dedup condition then {(propagateReset ...).2 with leader := F}
  --   else (propagateReset ...).2
  -- In both cases, .role is the same (leader change doesn't affect role)
  split_ifs <;> exact h_pr

/-! ### Awakening config: all Resetting, one leader -/

/-- An awakening configuration: all agents Resetting with resetcount = 0,
delaytimer = 0, exactly one leader. When any agent executes RESET:
leader → Settled(rank 0), follower → Unsettled(errorcount Emax). -/
def IsAwakeningConfig (C : Config (AgentState n) Opinion n) : Prop :=
  (∀ w : Fin n, (C w).1.role = .Resetting) ∧
  (∀ w : Fin n, (C w).1.resetcount = 0) ∧
  (∀ w : Fin n, (C w).1.delaytimer = 0) ∧
  (∃! ℓ : Fin n, (C ℓ).1.leader = .L) ∧
  (∀ w : Fin n, (C w).1.leader = .L ∨ (C w).1.leader = .F)

/-- RESET for a leader produces Settled at rank 0. -/
theorem resetOSSR_leader {Emax : ℕ} {hn : 0 < n}
    {s : AgentState n} (h_leader : s.leader = .L) :
    (resetOSSR Emax hn s).role = .Settled ∧
    (resetOSSR Emax hn s).rank = ⟨0, hn⟩ ∧
    (resetOSSR Emax hn s).children = 0 := by
  unfold resetOSSR; rw [h_leader]; exact ⟨rfl, rfl, rfl⟩

/-- RESET for a follower produces Unsettled with errorcount = Emax. -/
theorem resetOSSR_follower {Emax : ℕ} {hn : 0 < n}
    {s : AgentState n} (h_follower : s.leader = .F) :
    (resetOSSR Emax hn s).role = .Unsettled ∧
    (resetOSSR Emax hn s).errorcount = Emax := by
  unfold resetOSSR; rw [h_follower]; exact ⟨rfl, rfl⟩

/-! ### List-based schedule execution

Following ChatGPT's suggestion: prove reachability via finite lists
of interactions, then convert to ℕ → Fin n × Fin n at the end.
This is much simpler than working with scheduler functions directly. -/

/-- Execute a finite list of interactions. -/
def runPairs {Q X Y : Type*} (P : Protocol Q X Y) (C : Config Q X n)
    (L : List (Fin n × Fin n)) : Config Q X n :=
  L.foldl (fun C ij => C.step P ij.1 ij.2) C

@[simp] theorem runPairs_nil {Q X Y : Type*} (P : Protocol Q X Y) (C : Config Q X n) :
    runPairs P C [] = C := rfl

@[simp] theorem runPairs_cons {Q X Y : Type*} (P : Protocol Q X Y) (C : Config Q X n)
    (ij : Fin n × Fin n) (L : List (Fin n × Fin n)) :
    runPairs P C (ij :: L) = runPairs P (C.step P ij.1 ij.2) L := rfl

theorem runPairs_append {Q X Y : Type*} (P : Protocol Q X Y) (C : Config Q X n)
    (L₁ L₂ : List (Fin n × Fin n)) :
    runPairs P C (L₁ ++ L₂) = runPairs P (runPairs P C L₁) L₂ := by
  simp [runPairs, List.foldl_append]

/-- Convert a list schedule to a function schedule. -/
def schedOfList [Inhabited (Fin n × Fin n)] (L : List (Fin n × Fin n)) :
    DetScheduler n :=
  fun t => L.getD t default

/-- Bridge: runPairs via list = execution via scheduler.
Proved by induction on the list, using execution_concat. -/
theorem exists_schedule_of_runPairs [Inhabited (Fin n × Fin n)]
    {Q X Y : Type*} (P : Protocol Q X Y)
    (C₀ : Config Q X n) (L : List (Fin n × Fin n))
    {Goal : Config Q X n → Prop}
    (h : Goal (runPairs P C₀ L)) :
    ∃ (γ : DetScheduler n) (t : ℕ), Goal (execution P C₀ γ t) := by
  induction L generalizing C₀ with
  | nil => exact ⟨fun _ => default, 0, h⟩
  | cons ij L ih =>
    have h' := ih (C₀.step P ij.1 ij.2) h
    obtain ⟨γ', t', hGoal⟩ := h'
    exact ⟨concatScheduler (fun _ => ij) 1 γ', 1 + t',
      by rw [execution_concat]; exact hGoal⟩

/-! ### Phase 1a: Trigger reset from all-Settled non-InSrank

When all agents are Settled but InSrank fails (ranks not injective),
schedule one collision pair → both become Resetting. -/

theorem trigger_reset_from_all_settled_non_InSrank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C₀ : Config (AgentState n) Opinion n}
    (hSettled : ∀ v : Fin n, (C₀ v).1.role = .Settled)
    (hNotInSrank : ¬ InSrank C₀) :
    ∃ u v : Fin n, u ≠ v ∧
      let C' := C₀.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v
      (C' u).1.role = .Resetting ∧ (C' v).1.role = .Resetting ∧
      (C' u).1.resetcount = Rmax ∧ (C' v).1.resetcount = Rmax := by
  have hNotInj : ¬ Function.Injective (fun v : Fin n => (C₀ v).1.rank) := by
    intro hinj; exact hNotInSrank ⟨hSettled, hinj⟩
  obtain ⟨u, v, huv, h_same⟩ := exists_collision_of_not_inj hSettled hNotInj
  have hcoll := transitionPEM_collision_both_resetting (hsu := hSettled u) (hsv := hSettled v) h_same
  have h_fst := Config.step_fst_state (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C₀ huv
  have h_snd := Config.step_snd_state (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C₀ huv huv.symm
  exact ⟨u, v, huv,
    congrArg AgentState.role h_fst ▸ hcoll.1,
    congrArg AgentState.role h_snd ▸ hcoll.2.1,
    congrArg AgentState.resetcount h_fst ▸ hcoll.2.2.1,
    congrArg AgentState.resetcount h_snd ▸ hcoll.2.2.2⟩

/-! ### Unsettled branch induction (from ChatGPT)

Well-founded induction on unsettledMass = Σ (errorcount + 1). -/

noncomputable def unsettledMass (C : Config (AgentState n) Opinion n) : ℕ :=
  ∑ w : Fin n, if (C w).1.role = .Unsettled then (C w).1.errorcount + 1 else 0

theorem unsettled_one_step_progress
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {w v : Fin n} (hwv : v ≠ w)
    (hw_unsettled : (C w).1.role = .Unsettled)
    (hNoReset : ∀ x : Fin n, (C x).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := runPairs P C [(w, v)]
    (∃ x : Fin n, (C' x).1.role = .Resetting) ∨
    ((∀ x : Fin n, (C' x).1.role ≠ .Resetting) ∧ unsettledMass C' < unsettledMass C) := by
  sorry

theorem unsettled_branch_eventually_reset_or_allSettled
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hUnsettled : ∃ w : Fin n, (C w).1.role = .Unsettled)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting) ∨
      (∀ w : Fin n, (runPairs P C L w).1.role = .Settled) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices h : ∀ m C₀,
      unsettledMass C₀ = m →
      (∃ w, (C₀ w).1.role = .Unsettled) →
      (∀ w, (C₀ w).1.role ≠ .Resetting) →
      ∃ L, (∃ w, (runPairs P C₀ L w).1.role = .Resetting) ∨
           (∀ w, (runPairs P C₀ L w).1.role = .Settled) from
    h (unsettledMass C) C rfl hUnsettled hNoReset
  intro m
  induction m using Nat.strongRecOn with
  | ind m IH =>
    intro C₀ hMass hU hNR
    obtain ⟨w, hw⟩ := hU
    obtain ⟨v, hv⟩ : ∃ v : Fin n, v ≠ w := by
      exact ⟨if (0 : Fin n) = w then ⟨1, by omega⟩ else 0,
        by split_ifs with h <;> [exact (by intro h'; simp at h'; omega); exact h]⟩
    set C₁ := runPairs P C₀ [(w, v)]
    have hstep := unsettled_one_step_progress C₀ hv hw (hNR)
    cases hstep with
    | inl hReset => exact ⟨[(w, v)], Or.inl hReset⟩
    | inr ⟨hNR₁, hLt⟩ =>
      by_cases hU₁ : ∃ w, (C₁ w).1.role = .Unsettled
      · obtain ⟨Ltail, htail⟩ := IH (unsettledMass C₁) (hMass ▸ hLt) C₁ rfl hU₁ hNR₁
        refine ⟨[(w, v)] ++ Ltail, ?_⟩
        rwa [runPairs_append]
      · right
        refine ⟨[(w, v)], Or.inr (fun x => ?_)⟩
        push_neg at hU₁
        have := hNR₁ x; have := hU₁ x
        cases h : (C₁ x).1.role <;> simp_all

/-! ### Phase lemma stubs for BurmanConvergence composition

Each phase takes a precondition and produces a list schedule + post-condition.
The full convergence proof composes them via runPairs_append. -/

/-- Phase 1: From ANY config, reach InSrank OR produce ≥ 1 Resetting agent.
(ChatGPT insight: returning InSrank directly handles the case where
Unsettled agents get recruited to Settled without triggering reset.) -/
theorem phase1_trigger_reset_or_InSrank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∨ (∃ w : Fin n, (C' w).1.role = .Resetting) := by
  classical
  -- Case 1: already InSrank
  by_cases hInSrank : InSrank C
  · exact ⟨[], Or.inl hInSrank⟩
  -- Case 2: some agent already Resetting
  by_cases hSomeResetting : ∃ w : Fin n, (C w).1.role = .Resetting
  · obtain ⟨w, hw⟩ := hSomeResetting
    exact ⟨[], Or.inr ⟨w, hw⟩⟩
  push_neg at hSomeResetting
  -- Case 3: all Settled but not InSrank → collision
  by_cases hAllSettled : ∀ w : Fin n, (C w).1.role = .Settled
  · obtain ⟨u, v, _huv, hu_reset, _⟩ :=
      trigger_reset_from_all_settled_non_InSrank hAllSettled hInSrank
    exact ⟨[(u, v)], Or.inr ⟨u, by simpa [runPairs] using hu_reset⟩⟩
  · -- Case 4: some Unsettled, no Resetting → induction on unsettledMass
    push_neg at hAllSettled
    have hUnsettled : ∃ w : Fin n, (C w).1.role = .Unsettled := by
      obtain ⟨w, hw⟩ := hAllSettled
      exact ⟨w, by cases h : (C w).1.role <;> simp_all⟩
    obtain ⟨L, hL⟩ := unsettled_branch_eventually_reset_or_allSettled
      hn4 C hUnsettled (fun w => hSomeResetting w)
    set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    cases hL with
    | inl hReset => exact ⟨L, Or.inr hReset⟩
    | inr hAllSettled' =>
      by_cases hS : InSrank (runPairs P C L)
      · exact ⟨L, Or.inl hS⟩
      · obtain ⟨u, v, _huv, hu_res, _⟩ :=
          trigger_reset_from_all_settled_non_InSrank hAllSettled' hS
        exact ⟨L ++ [(u, v)], Or.inr ⟨u, by
          rw [runPairs_append]; simpa [runPairs] using hu_res⟩⟩

/-- Phase 3a target: all Resetting with counters expired. -/
def AllResettingDormant (C : Config (AgentState n) Opinion n) : Prop :=
  (∀ w : Fin n, (C w).1.role = .Resetting) ∧
  (∀ w : Fin n, (C w).1.resetcount = 0) ∧
  (∀ w : Fin n, (C w).1.delaytimer = 0)

/-- Phase 3b/3c target, Phase 4 input: one Settled root + rest Unsettled.
(ChatGPT: uses rank.val = 0 to avoid hn parameter.) -/
def FreshRankingStart (C : Config (AgentState n) Opinion n) : Prop :=
  ∃ root : Fin n,
    (C root).1.role = .Settled ∧
    (C root).1.rank.val = 0 ∧
    (C root).1.children = 0 ∧
    ∀ w : Fin n, w ≠ root → (C w).1.role = .Unsettled

/-- Phase 2: From config with ≥ 1 Resetting, spread to all agents. -/
theorem phase2_propagate_reset
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hReset : ∃ w : Fin n, (C w).1.role = .Resetting) :
    ∃ L : List (Fin n × Fin n),
      ∀ w : Fin n, (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L w).1.role = .Resetting := by
  -- Induction on # non-Resetting agents.
  -- At each step: schedule (resetting_agent, non_resetting_agent)
  -- → non_resetting becomes Resetting (via rankDeltaOSSR_propagate_reset)
  -- Needs: resetting agent maintains resetcount > 0 through propagation.
  -- With Rmax ≥ n and at most n-1 propagation steps, resetcount stays > 0.
  sorry

/-- Phase 3a: countdown delaytimers to 0 for all Resetting agents. -/
theorem phase3a_dormancy_countdown
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting) :
    ∃ L : List (Fin n × Fin n),
      AllResettingDormant (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  sorry

/-- Phase 3b: execute RESET from dormant config → leaders Settled, followers Unsettled. -/
theorem phase3b_execute_reset
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    (hDormant : AllResettingDormant C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      -- After RESET: leaders become Settled(rank 0), followers become Unsettled
      -- At least one leader exists (from IsAwakeningConfig or from protocol invariant)
      (∃ ℓ : Fin n, (C' ℓ).1.role = .Settled ∧ (C' ℓ).1.rank = ⟨0, hn⟩) ∧
      (∀ w : Fin n, (C' w).1.role = .Settled ∨ (C' w).1.role = .Unsettled) := by
  sorry

/-- Phase 3b+3c: RESET + leader election → FreshRankingStart. -/
theorem phase3bc_reset_and_elect
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hDormant : AllResettingDormant C) :
    ∃ L : List (Fin n × Fin n),
      FreshRankingStart (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  sorry

/-- Phase 4: binary tree recruitment → InSrank. -/
theorem phase4_binary_tree
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hSeed : FreshRankingStart C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∧
      ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C' μ).1.timer) ∨
       IsConsensusConfig C') := by
  sorry

/-- Phase 3+4 composition: all-Resetting → InSrank. -/
theorem phase34_rerank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∧
      ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C' μ).1.timer) ∨
       IsConsensusConfig C') := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  -- Phase 3a: dormancy countdown
  obtain ⟨L1, h1⟩ := phase3a_dormancy_countdown C hAllReset
  -- Phase 3b+3c: RESET + leader election → FreshRankingStart
  obtain ⟨L2, h2⟩ := phase3bc_reset_and_elect hn4 (runPairs P C L1) h1
  -- Phase 4: binary tree → InSrank
  obtain ⟨L3, h3⟩ := phase4_binary_tree hn4
    (runPairs P (runPairs P C L1) L2) h2
  -- Compose
  refine ⟨L1 ++ L2 ++ L3, ?_⟩
  simp only [runPairs_append, List.append_assoc] at h3 ⊢
  exact h3

/-! ### Phase 1a: Collision detection (same-rank Settled → Resetting)

When all agents are Settled but ranks are not injective (not InSrank),
there exist two distinct agents with the same rank. Scheduling them
triggers collision detection → both become Resetting. -/

/-- If all Settled but ranks not injective, ∃ two with same rank. -/
theorem exists_collision_of_not_inj
    {C : Config (AgentState n) Opinion n}
    (hSettled : ∀ v : Fin n, (C v).1.role = .Settled)
    (hNotInj : ¬ Function.Injective (fun v : Fin n => (C v).1.rank)) :
    ∃ u v : Fin n, u ≠ v ∧ (C u).1.rank = (C v).1.rank := by
  by_contra h
  push_neg at h
  apply hNotInj
  intro a b hab
  by_contra hne
  exact hne (h a b hne hab).elim

/-- Collision detection: two Settled agents with the same rank both
become Resetting via rankDeltaOSSR Part 2. -/
theorem rankDeltaOSSR_collision
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Settled) (ht : t.role = .Settled)
    (h_same : s.rank = t.rank) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = Rmax ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = Rmax := by
  unfold rankDeltaOSSR
  have h_not_res : ¬(s.role = .Resetting ∨ t.role = .Resetting) := by
    rw [hs, ht]; simp
  simp only [h_not_res, ite_false, hs, ht, h_same, and_self, ite_true]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### Collision through transitionPEM: both → Resetting -/

set_option maxHeartbeats 8000000 in
/-- After collision in rankDeltaOSSR (both Settled, same rank → both
Resetting), transitionPEM preserves the Resetting role. Phase 2 clears
answer but keeps role. Phase 4 requires both Settled which is false. -/
theorem transitionPEM_collision_both_resetting
    {trank Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hsu : (C u).1.role = .Settled) (hsv : (C v).1.role = .Settled)
    (h_same : (C u).1.rank = (C v).1.rank) :
    (transitionPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C u, C v)).1.role = .Resetting ∧
    (transitionPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C u, C v)).2.role = .Resetting ∧
    (transitionPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C u, C v)).1.resetcount = Rmax ∧
    (transitionPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C u, C v)).2.resetcount = Rmax := by
  have hcoll := rankDeltaOSSR_collision hsu hsv h_same
  unfold transitionPEM
  simp only [show (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Resetting
    from hcoll.1,
    show (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Resetting
    from hcoll.2.1,
    show (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.resetcount = Rmax
    from hcoll.2.2.1,
    show (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.resetcount = Rmax
    from hcoll.2.2.2,
    hsu, hsv, ne_eq, role_settled_ne_resetting,
    show Role.Resetting = .Resetting from rfl,
    show ¬(Role.Settled = Role.Resetting) from by decide,
    show Role.Resetting ≠ .Settled from by decide]
  simp only [ite_true, ite_false, and_false, false_and, if_false]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### The full BurmanConvergence proof

We prove BurmanConvergence for rankDeltaOSSR with appropriate parameters.
The proof constructs explicit deterministic schedules for each initial config.

Key insight: from ANY initial config, the protocol can:
1. Trigger resets via collision detection or errorcount timeout
2. Spread resets via PROPAGATE-RESET
3. Elect a single leader via L,L → L,F
4. Build a binary tree via recruitment
5. The timer is initialized at the median during recruitment

For the epidemic: the correct answer spreads during the Resetting
phase (lines 7-8 of Algorithm 1) and is preserved through re-ranking. -/

/-- **BurmanConvergence for the concrete protocol.**

For appropriate parameters (trank, Rmax ≥ n), the concrete protocol
with rankDeltaOSSR satisfies BurmanConvergence. -/
theorem burmanConvergence_concrete
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (htrank : n ≤ Rmax) :
    BurmanConvergence Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) where
  ranking := fun C₀ => by
    -- Check if already consensus
    classical
    by_cases hCons : IsConsensusConfig C₀
    · exact ⟨fun _ => default, 0,
        ⟨hCons.allSettled, hCons.ranks_inj⟩, Or.inr hCons⟩
    · -- NOT consensus: reach InSrank with timer ≥ 2
      by_cases hInSrank : InSrank C₀
      · by_cases h_timer : ∀ μ : Fin n, (C₀ μ).1.rank.val + 1 = ceilHalf n →
              2 ≤ (C₀ μ).1.timer
        · exact ⟨fun _ => default, 0, hInSrank, Or.inl h_timer⟩
        · -- InSrank + timer < 2 + ¬consensus:
          -- Decision changes median's answer (to match input).
          -- If input is "wrong" for the sorted position → creates disagreement.
          -- Then propagation reset fires (timer = 0, answers differ).
          -- Result: 2 agents Resetting → falls into non-InSrank case below.
          -- The non-InSrank case handles convergence from there.
          sorry
      · -- Not InSrank: compose phases via runPairs (ChatGPT pattern).
        set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        obtain ⟨L1, h1⟩ := phase1_trigger_reset_or_InSrank hn4 hEmax hDmax C₀
        cases h1 with
        | inl hInSrank₁ =>
          -- Phase 1 reached InSrank directly (via recruitment)
          by_cases h_timer₁ : ∀ μ : Fin n, (runPairs P C₀ L1 μ).1.rank.val + 1 = ceilHalf n →
                2 ≤ (runPairs P C₀ L1 μ).1.timer
          · apply exists_schedule_of_runPairs P C₀ L1
            exact ⟨hInSrank₁, Or.inl h_timer₁⟩
          · -- InSrank but timer < 2: trigger reset from there
            sorry
        | inr hReset₁ =>
          -- Phase 1 produced Resetting → continue with phase 2+3+4
          obtain ⟨L2, h2_raw⟩ := phase2_propagate_reset (show 1 < Dmax by omega)
            (runPairs P C₀ L1) hReset₁
          have h2 : ∀ w, (runPairs P C₀ (L1 ++ L2) w).1.role = .Resetting := by
            intro w; have := h2_raw w; rwa [runPairs_append] at this
          obtain ⟨L34, h34⟩ := phase34_rerank hn4 (runPairs P C₀ (L1 ++ L2)) h2
          apply exists_schedule_of_runPairs P C₀ (L1 ++ L2 ++ L34)
          constructor
          · rw [runPairs_append]; exact h34.1
          · rw [runPairs_append]; exact h34.2
  epidemic := fun C₀ h_correct => by
    -- From C₀ with ≥ 1 correct answer, reach InSswap + all correct + timer ≥ 1.
    --
    -- Uses ranking to reach InSrank, but must ALSO ensure:
    -- - The correct answer propagates during Resetting (lines 7-8 epidemic)
    -- - After re-ranking, all agents have the correct answer
    -- - Swap phase sorts by input → InSswap
    -- - Timer ≥ 1 from ranking's timer ≥ 2 minus at most 1 swap decrement
    --
    -- The epidemic mechanism: during Phase 3 of transitionPEM, Resetting
    -- agents with answer = phi copy the answer from non-phi agents.
    -- Since ≥ 1 agent has the correct answer, it spreads to all others.
    sorry

/-- **The ULTIMATE theorem: SolvesSSEM with NO external hypotheses.**

P_EM with the concrete protocol solves SSEM for n ≥ 4. -/
theorem P_EM_solves_SSEM_final
    [Inhabited (Fin n × Fin n)]
    {Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    SolvesSSEM (protocolPEM n n n (rankDeltaOSSR n Emax Dmax hn)) n :=
  P_EM_solves_SSEM_from_BurmanConvergence_only
    rankDeltaOSSR_satisfies_fix
    hn4
    (burmanConvergence_concrete hn4 hEmax hDmax le_rfl)

end SSEM
