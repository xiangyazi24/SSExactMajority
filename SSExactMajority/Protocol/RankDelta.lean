/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Concrete Ranking Subprotocol (OPTIMAL-SILENT-SSR)

This file defines the concrete `rankDeltaOSSR` implementing Protocol 3
from Burman, Chen, Chen, Doty, Nowak, Severson, Xu (PODC 2021):
"Time-Optimal Self-Stabilizing Leader Election in Population Protocols".

## Components

* `resetOSSR` — Protocol 4 (RESET subroutine for OPTIMAL-SILENT-SSR):
  Leaders become Settled at rank 1; followers become Unsettled.

* `propagateReset` — Protocol 2 (PROPAGATE-RESET):
  Epidemic-style reset propagation with resetcount synchronization
  and delaytimer-based dormancy.

* `rankDeltaOSSR` — Protocol 3 (OPTIMAL-SILENT-SSR):
  Binary-tree ranking with collision detection and error monitoring.

## Key property

`rankDeltaOSSR_settled_distinct_ranks`: when both agents are Settled
with distinct ranks, the protocol is the identity (no state change).
-/

import SSExactMajority.Protocol.State
import SSExactMajority.Convergence.Silent

namespace SSEM

variable {n : ℕ}

/-! ### Protocol 4: RESET for OPTIMAL-SILENT-SSR -/

/-- Protocol 4 from Burman et al.: wake an agent from the Resetting role.
Leaders (leader = L) become Settled at rank 1 (0-indexed: rank 0).
Followers (leader = F) become Unsettled with errorcount initialized. -/
def resetOSSR (Emax : ℕ) (hn : 0 < n) (s : AgentState n) : AgentState n :=
  match s.leader with
  | .L => { s with role := .Settled, rank := ⟨0, hn⟩, children := 0 }
  | .F => { s with role := .Unsettled, errorcount := Emax }

/-! ### Protocol 2: PROPAGATE-RESET -/

/-- Protocol 2 from Burman et al.: epidemic-style reset propagation.

Called when at least one of `a`, `b` has `role = Resetting`.

Phase 1 (lines 1-2): If `a` is propagating (resetcount > 0) and `b`
  is not yet Resetting, recruit `b` into Resetting role.
Phase 2 (line 3-4): If both are Resetting, synchronize resetcounts
  via `max(a.resetcount - 1, b.resetcount - 1, 0)`.
Phase 3 (lines 5-11): For each dormant agent (resetcount = 0):
  - If resetcount just became 0: initialize delaytimer
  - Otherwise: decrement delaytimer
  - If delaytimer = 0 or partner is not Resetting: execute RESET -/
def propagateReset (Emax Dmax : ℕ) (hn : 0 < n)
    (a b : AgentState n) : AgentState n × AgentState n :=
  -- Phase 1: recruitment (line 1-2)
  let (a, b) :=
    if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
      (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
    else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
      ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
    else (a, b)
  -- Save old resetcounts for "just became 0" check
  let oldRcA := a.resetcount
  let oldRcB := b.resetcount
  -- Phase 2: resetcount synchronization (lines 3-4)
  let (a, b) :=
    if a.role = .Resetting ∧ b.role = .Resetting then
      let newRc := max (a.resetcount - 1) (b.resetcount - 1)
      ({ a with resetcount := newRc }, { b with resetcount := newRc })
    else (a, b)
  -- Phase 3: dormant agent processing (lines 5-11)
  let processAgent (s : AgentState n) (oldRc : ℕ) (partnerResetting : Bool) :=
    if s.role = .Resetting ∧ s.resetcount = 0 then
      let s :=
        if 0 < oldRc then
          { s with delaytimer := Dmax }
        else
          { s with delaytimer := s.delaytimer - 1 }
      if s.delaytimer = 0 ∨ !partnerResetting then
        resetOSSR Emax hn s
      else s
    else s
  let aRes := b.role == .Resetting
  let bRes := a.role == .Resetting
  (processAgent a oldRcA aRes, processAgent b oldRcB bRes)

/-! ### Protocol 3: OPTIMAL-SILENT-SSR -/

/-- Protocol 3 from Burman et al.: the complete ranking subprotocol.

Parameters:
* `Rmax` — maximum resetcount (paper: R_max = 60 ln n)
* `Emax` — error counter for Unsettled agents (paper: E_max = Θ(n))
* `Dmax` — delay timer for dormant agents (paper: D_max = Θ(n))

The protocol has four parts:
1. **PROPAGATE-RESET** (lines 1-4): Handle Resetting agents, including
   leader deduplication.
2. **Collision detection** (lines 5-7): Two Settled agents with the
   same rank → both become Resetting.
3. **Binary-tree ranking** (lines 8-12): Settled agents recruit
   Unsettled agents as children in a binary tree.
4. **Error monitoring** (lines 13-18): Unsettled agents decrement
   errorcount; if it reaches 0, trigger reset. -/
def rankDeltaOSSR (Rmax Emax Dmax : ℕ) (hn : 0 < n)
    (pair : AgentState n × AgentState n) : AgentState n × AgentState n :=
  let (a, b) := pair
  -- Part 1: PROPAGATE-RESET + leader deduplication (lines 1-4)
  if a.role = .Resetting ∨ b.role = .Resetting then
    let (a, b) := propagateReset Emax Dmax hn a b
    let b := if a.leader = .L ∧ b.leader = .L ∧
                a.role = .Resetting ∧ b.role = .Resetting
             then { b with leader := .F }
             else b
    (a, b)
  -- Part 2: Collision detection (lines 5-7)
  else if a.role = .Settled ∧ b.role = .Settled ∧ a.rank = b.rank then
    ({ a with role := .Resetting, resetcount := Rmax, leader := .L },
     { b with role := .Resetting, resetcount := Rmax, leader := .L })
  else
    -- Part 3: Binary-tree ranking (lines 8-12)
    -- Try (a recruits b), then (b recruits a)
    if h_ab : a.role = .Settled ∧ b.role = .Unsettled ∧
       a.children < 2 ∧ 2 * a.rank.val + a.children + 1 < n then
      let childRank : Fin n := ⟨2 * a.rank.val + a.children + 1, h_ab.2.2.2⟩
      ({ a with children := a.children + 1 },
       { b with role := .Settled, children := 0, rank := childRank })
    else if h_ba : b.role = .Settled ∧ a.role = .Unsettled ∧
       b.children < 2 ∧ 2 * b.rank.val + b.children + 1 < n then
      let childRank : Fin n := ⟨2 * b.rank.val + b.children + 1, h_ba.2.2.2⟩
      ({ a with role := .Settled, children := 0, rank := childRank },
       { b with children := b.children + 1 })
    else
      -- Part 4: Error monitoring (lines 13-18)
      let a' :=
        if a.role = .Unsettled then
          let a'' := { a with errorcount := a.errorcount - 1 }
          if a''.errorcount = 0 then
            { a'' with role := .Resetting, resetcount := Rmax, leader := .L }
          else a''
        else a
      let b' :=
        if b.role = .Unsettled then
          let b'' := { b with errorcount := b.errorcount - 1 }
          if b''.errorcount = 0 then
            { b'' with role := .Resetting, resetcount := Rmax, leader := .L }
          else b''
        else b
      if (a'.role = .Resetting ∧ a.role = .Unsettled) ∨
         (b'.role = .Resetting ∧ b.role = .Unsettled) then
        ({ a' with role := .Resetting, resetcount := Rmax, leader := .L },
         { b' with role := .Resetting, resetcount := Rmax, leader := .L })
      else (a', b')

/-! ### Key property: identity on Settled pairs with distinct ranks -/

theorem rankDeltaOSSR_settled_distinct_ranks
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Settled) (ht : t.role = .Settled)
    (hne : s.rank ≠ t.rank) :
    rankDeltaOSSR Rmax Emax Dmax hn (s, t) = (s, t) := by
  have hsr : s.role ≠ .Resetting := by rw [hs]; decide
  have htr : t.role ≠ .Resetting := by rw [ht]; decide
  have hsu : s.role ≠ .Unsettled := by rw [hs]; decide
  have htu : t.role ≠ .Unsettled := by rw [ht]; decide
  unfold rankDeltaOSSR
  dsimp only []
  rw [if_neg (show ¬(s.role = .Resetting ∨ t.role = .Resetting) from
    fun h => h.elim hsr htr)]
  rw [if_neg (show ¬(s.role = .Settled ∧ t.role = .Settled ∧ s.rank = t.rank) from
    fun ⟨_, _, h⟩ => hne h)]
  rw [dif_neg (show ¬(s.role = .Settled ∧ t.role = .Unsettled ∧
    s.children < 2 ∧ 2 * s.rank.val + s.children + 1 < n) from
    fun ⟨_, h, _⟩ => htu h)]
  rw [dif_neg (show ¬(t.role = .Settled ∧ s.role = .Unsettled ∧
    t.children < 2 ∧ 2 * t.rank.val + t.children + 1 < n) from
    fun ⟨_, h, _⟩ => hsu h)]
  rw [if_neg (show ¬(s.role = .Unsettled) from hsu)]
  rw [if_neg (show ¬(t.role = .Unsettled) from htu)]
  rw [if_neg (show ¬((s.role = .Resetting ∧ s.role = .Unsettled) ∨
    (t.role = .Resetting ∧ t.role = .Unsettled)) from by
    intro h; cases h with
    | inl h => exact hsr h.1
    | inr h => exact htr h.1)]

/-! ### Stabilized wrapper satisfying `RankDeltaSettledFix`

The full `rankDeltaOSSR` resets on same-rank Settled pairs (collision
detection, Protocol 3 lines 5-7). This is correct protocol behavior
needed BEFORE stabilization, but `RankDeltaSettledFix` requires identity
on ALL Settled pairs.

`rankDeltaStable` is identity on Settled pairs by construction, and
delegates to `rankDeltaOSSR` otherwise. After ranking has stabilized
(InSrank: all Settled with unique ranks), `rankDeltaStable` and
`rankDeltaOSSR` are behaviorally identical — the collision case never
fires because ranks are unique. -/
def rankDeltaStable (Rmax Emax Dmax : ℕ) (hn : 0 < n)
    (pair : AgentState n × AgentState n) : AgentState n × AgentState n :=
  if pair.1.role = .Settled ∧ pair.2.role = .Settled then pair
  else rankDeltaOSSR Rmax Emax Dmax hn pair

theorem rankDeltaOSSR_satisfies_fix {Rmax Emax Dmax : ℕ} {hn : 0 < n} :
    RankDeltaSettledFix (rankDeltaOSSR Rmax Emax Dmax hn) :=
  fun _ _ hs ht hne => rankDeltaOSSR_settled_distinct_ranks hs ht hne

theorem rankDeltaStable_satisfies_fix {Rmax Emax Dmax : ℕ} {hn : 0 < n} :
    RankDeltaSettledFix (rankDeltaStable Rmax Emax Dmax hn) := by
  intro s t hs ht _
  simp only [rankDeltaStable, hs, ht, and_self, ite_true]

theorem rankDeltaStable_eq_rankDeltaOSSR_non_settled
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (h : ¬(s.role = .Settled ∧ t.role = .Settled)) :
    rankDeltaStable Rmax Emax Dmax hn (s, t) =
    rankDeltaOSSR Rmax Emax Dmax hn (s, t) := by
  simp only [rankDeltaStable, h, ite_false]

theorem rankDeltaStable_eq_of_distinct_ranks
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Settled) (ht : t.role = .Settled)
    (hne : s.rank ≠ t.rank) :
    rankDeltaStable Rmax Emax Dmax hn (s, t) = (s, t) := by
  simp only [rankDeltaStable, hs, ht, and_self, ite_true]

end SSEM
