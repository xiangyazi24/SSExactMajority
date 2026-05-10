/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Transition Function for P_EM

Algorithm 1 from Kanaya et al. (2025), parameterized by a ranking
subprotocol (Optimal-Silent-SSR from Burman et al. PODC 2021).

The protocol has four phases:
1. Ranking: Execute the ranking subprotocol to assign unique ranks.
2. Swapping: Swap states so A-agents get lower ranks.
3. Decision: Median-ranked agent(s) decide the majority opinion.
4. Propagation: Median agent propagates answer; reset on disagreement.
-/

import SSExactMajority.Defs.Protocol
import SSExactMajority.Protocol.State

namespace SSEM

/-- The ceiling half: ⌈n/2⌉. -/
def ceilHalf (n : ℕ) : ℕ := (n + 1) / 2

def opinionToAnswer : Opinion → Answer
  | .A => .outA
  | .B => .outB

/-- The full P_EM transition function (Algorithm 1).
    Parameterized by `rankDelta` (the ranking subprotocol's transition)
    and constants `trank` (ranking stabilization time) and `Rmax`. -/
def transitionPEM (n : ℕ) (trank Rmax : ℕ)
    (rankDelta : AgentState n × AgentState n → AgentState n × AgentState n) :
    ((AgentState n × Opinion) × (AgentState n × Opinion)) →
    (AgentState n × AgentState n) :=
  fun ⟨⟨s₀, x₀⟩, ⟨s₁, x₁⟩⟩ =>
  -- Phase 1: Execute ranking subprotocol (line 1)
  let (r₀, r₁) := rankDelta (s₀, s₁)
  -- Phase 2: Handle role transitions (lines 2-6)
  -- Line 3-4: role becomes Resetting → clear answer
  let a₀ := if r₀.role = .Resetting ∧ s₀.role ≠ .Resetting then
      { r₀ with answer := .phi }
    else r₀
  let a₁ := if r₁.role = .Resetting ∧ s₁.role ≠ .Resetting then
      { r₁ with answer := .phi }
    else r₁
  -- Line 5-6: role becomes Settled at median rank → set timer
  let a₀ := if a₀.role = .Settled ∧ s₀.role ≠ .Settled ∧ a₀.rank.val + 1 = ceilHalf n then
      { a₀ with timer := 7 * (trank + 4) }
    else a₀
  let a₁ := if a₁.role = .Settled ∧ s₁.role ≠ .Settled ∧ a₁.rank.val + 1 = ceilHalf n then
      { a₁ with timer := 7 * (trank + 4) }
    else a₁
  -- Phase 3: Epidemic during resetting (lines 7-8)
  let (a₀, a₁) :=
    if a₀.role = .Resetting ∧ a₁.role = .Resetting then
      if a₀.answer = .phi ∧ a₁.answer ≠ .phi then
        ({ a₀ with answer := a₁.answer }, a₁)
      else if a₁.answer = .phi ∧ a₀.answer ≠ .phi then
        (a₀, { a₁ with answer := a₀.answer })
      else (a₀, a₁)
    else (a₀, a₁)
  -- Phase 4: Both Settled → swap + decide + propagate (lines 9-24)
  if a₀.role = .Settled ∧ a₁.role = .Settled then
    -- Swapping (lines 10-11): swap states if B-agent has lower rank than A-agent
    let (b₀, b₁) :=
      if a₀.rank < a₁.rank ∧ x₀ = .B ∧ x₁ = .A then (a₁, a₀)
      else (a₀, a₁)
    -- Decision (lines 12-18)
    let (b₀, b₁) :=
      if n % 2 = 0 then
        -- Even n: median pair decides (lines 12-16)
        if b₀.rank.val + 1 = n / 2 ∧ b₁.rank.val + 1 = n / 2 + 1 then
          if x₀ = x₁ then
            ({ b₀ with answer := opinionToAnswer x₀ },
             { b₁ with answer := opinionToAnswer x₀ })
          else
            ({ b₀ with answer := .outT }, { b₁ with answer := .outT })
        else if b₁.rank.val + 1 = n / 2 ∧ b₀.rank.val + 1 = n / 2 + 1 then
          if x₁ = x₀ then
            ({ b₀ with answer := opinionToAnswer x₁ },
             { b₁ with answer := opinionToAnswer x₁ })
          else
            ({ b₀ with answer := .outT }, { b₁ with answer := .outT })
        else (b₀, b₁)
      else
        -- Odd n: median agent decides alone (lines 17-18)
        let b₀ := if b₀.rank.val + 1 = ceilHalf n then
            { b₀ with answer := opinionToAnswer x₀ }
          else b₀
        let b₁ := if b₁.rank.val + 1 = ceilHalf n then
            { b₁ with answer := opinionToAnswer x₁ }
          else b₁
        (b₀, b₁)
    -- Propagation (lines 19-24)
    if b₀.rank.val + 1 = ceilHalf n then
      -- b₀ is the median agent
      let b₀ := if b₁.rank.val + 1 = n then
          { b₀ with timer := b₀.timer - 1 }
        else b₀
      if b₀.timer = 0 ∧ b₀.answer ≠ b₁.answer then
        ({ b₀ with role := .Resetting, leader := .L, resetcount := Rmax },
         { b₁ with answer := b₀.answer,
                   role := .Resetting, leader := .L, resetcount := Rmax })
      else (b₀, b₁)
    else if b₁.rank.val + 1 = ceilHalf n then
      -- b₁ is the median agent (symmetric)
      let b₁ := if b₀.rank.val + 1 = n then
          { b₁ with timer := b₁.timer - 1 }
        else b₁
      if b₁.timer = 0 ∧ b₁.answer ≠ b₀.answer then
        ({ b₀ with answer := b₁.answer,
                   role := .Resetting, leader := .L, resetcount := Rmax },
         { b₁ with role := .Resetting, leader := .L, resetcount := Rmax })
      else (b₀, b₁)
    else (b₀, b₁)
  else (a₀, a₁)

/-- The output function for P_EM. -/
def outputPEM (n : ℕ) : AgentState n × Opinion → Output :=
  fun ⟨s, _⟩ => agentOutput s

/-- The protocol P_EM as a Protocol instance, parameterized by the ranking
    subprotocol and constants. -/
def protocolPEM (n : ℕ) (trank Rmax : ℕ)
    (rankDelta : AgentState n × AgentState n → AgentState n × AgentState n) :
    Protocol (AgentState n) Opinion Output where
  δ := transitionPEM n trank Rmax rankDelta
  π_out := outputPEM n

end SSEM
