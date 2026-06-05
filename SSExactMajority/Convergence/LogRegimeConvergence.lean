import SSExactMajority.Convergence.LogTreeReset

namespace SSEM

/-!
This file records the log-regime rethreading audit facts that can be
discharged from the current public interfaces.

The new logarithmic reset theorem needs an explicit lower bound on the
seed's reset fuel.  The existing epidemic seed package `CorrectResetSeed`
only exposes `nonResettingCount C < resetcount`; its callers know the reset
step wrote `Rmax`, but that fact is erased before re-entry.  Consequently the
capstone log theorem cannot be obtained by a wrapper around the existing
chain without strengthening the seed-or-progress interface.
-/

/-- Explicit log-fueled seed reaches the all-fresh reset state. -/
theorem log_seed_to_all_fresh
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hn2 : 2 ≤ n)
    (hRlog : Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hseed :
      ∃ r : Fin n,
        (C r).1.role = .Resetting ∧ Rmax ≤ (C r).1.resetcount) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      ∀ w : Fin n, FreshResettingAt Dmax C' w := by
  exact
    all_fresh_from_log_seed_unconditional
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (R := Rmax)
      (hn := hn) hDmax hn2 hRlog C hseed

/-- The role component exposed by an all-fresh endpoint. -/
theorem all_resetting_of_all_fresh
    {Dmax : ℕ} {C : Config (AgentState n) Opinion n}
    (hFresh : ∀ w : Fin n, FreshResettingAt Dmax C w) :
    ∀ w : Fin n, (C w).1.role = .Resetting := by
  intro w
  exact (hFresh w).1

/-- The resetcount-zero component exposed by an all-fresh endpoint. -/
theorem all_resetcount_zero_of_all_fresh
    {Dmax : ℕ} {C : Config (AgentState n) Opinion n}
    (hFresh : ∀ w : Fin n, FreshResettingAt Dmax C w) :
    ∀ w : Fin n, (C w).1.resetcount = 0 := by
  intro w
  exact (hFresh w).2.1

/-- The delaytimer component exposed by an all-fresh endpoint. -/
theorem all_delaytimer_eq_of_all_fresh
    {Dmax : ℕ} {C : Config (AgentState n) Opinion n}
    (hFresh : ∀ w : Fin n, FreshResettingAt Dmax C w) :
    ∀ w : Fin n, (C w).1.delaytimer = Dmax := by
  intro w
  exact (hFresh w).2.2

/-- Once the missing answer and unique-leader facts are supplied, the fresh
state enters the existing answer-preserving Phase-A bridge with only
`0 < Dmax`; the old `n <= Dmax` positive-resetcount budget is not used. -/
theorem fresh_uniform_unique_to_FreshRankingStart_resAns_noPhi
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax : 0 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hFresh : ∀ w : Fin n, FreshResettingAt Dmax C w)
    (hUniqueLeader : ∃! ℓ : Fin n, (C ℓ).1.leader = .L)
    (hm₀ : m₀ = majorityAnswer C)
    (hUniform : ∀ w : Fin n, (C w).1.answer = m₀) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      FreshRankingStart C' ∧
      ResAns m₀ C' ∧
      (∀ w : Fin n, (C' w).1.answer ≠ .phi) ∧
      majorityAnswer C' = majorityAnswer C := by
  exact
    all_resetting_zero_unique_uniform_to_FreshRankingStart_resAns_noPhi
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (m₀ := m₀) hn4 hRmax hDmax
      (all_resetting_of_all_fresh hFresh)
      (all_resetcount_zero_of_all_fresh hFresh)
      hUniqueLeader hm₀ hUniform

end SSEM
