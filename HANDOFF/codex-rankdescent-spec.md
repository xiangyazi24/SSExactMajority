# Codex task (uisai1): ranking-init coupon-collector descent (design fully specified)

Build on the PROVEN `SSExactMajority/UpperBound/Time/ConvStep.lean`
(`step_converts_resetting_rc0`, `_follower`). NEW file
`SSExactMajority/UpperBound/Time/RankInitDescent.lean`.

## Potential (USE THIS — design is settled)
`φ D := ∑ w : Fin n, (if (D w).1.role = .Resetting then 1 + (D w).1.delaytimer else 0)`

Facts to prove and feed to `expectedHittingTime_le_of_variable_descent_until_goal`
(Probability/ExpectedTime.lean:4379):
- **hZeroGoal**: `Inv D ∧ φ D = 0 → Goal D`. φ=0 ⟹ no `.Resetting` agent. With the
  single-`.L`-leader invariant, that means root(.L)→Settled + others→Unsettled, i.e.
  a valid no-Resetting ranking state. Goal := `(∀ w, (D w).1.role ≠ .Resetting)` (then a
  later lemma — NOT your job here — runs the heapPrefix descent to InSrank).
- **hInvStep**: the invariant `Inv` (all rc=0 maintained while Resetting + single L-leader
  + delaytimer ≤ M, i.e. IsBoundedConfig) is preserved by every step or Goal reached.
- **hNonincrease**: every step has `φ (step) ≤ φ`. Processing a Resetting agent either
  drains its delaytimer (−1) or converts it (removes its `1+dt` term, via ConvStep);
  other agents' terms unchanged. Untouched agents: unchanged.
- **hp (per-level descent prob)**: from `Inv D`, `φ D = k > 0`, there is a scheduled pair
  whose step strictly decreases φ, hit with probability ≥ `1/(n(n-1))`. (Pick any agent
  w with role=.Resetting; the pair (w, partner) where the step processes w decreases φ;
  selection prob ≥ 1/(n(n-1)). Mirror the existing `*_descent_prob_lower_bound` lemmas
  in Time.lean for the probability plumbing.)

Resulting bound: `E[T to Goal] ≤ ∑_{k<φ(C)} (n(n-1)) ≤ φ(C)·n(n-1) ≤ n(1+M)·n(n-1) = poly`.

## Target
```
theorem allR_to_noResetting_expected_le
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hDmaxN : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hAllR : ∀ w, (C w).1.role = .Resetting) (hRc0 : ∀ w, (C w).1.resetcount = 0)
    (hBounded : IsBoundedConfig (7*(Rmax+4)+Emax+Dmax) C) :
    Probability.expectedHittingTime (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C (fun D => ∀ w, (D w).1.role ≠ .Resetting)
      ≤ ((n * (1 + (7*(Rmax+4)+Emax+Dmax)) * (n*(n-1)) : ℕ) : ENNReal)
```
(Adjust the exact constant/invariant to what's provable; keep it E[T] ≤ explicit poly.)

## HARD RULES
- NO sorry/axiom/native_decide. Blocked → write exact goal+missing lemma to
  HANDOFF/outbox/codex-rankdescent-report.md. Don't weaken to trivial, don't reorganize.
- Touch ONLY RankInitDescent.lean. Self-verify `PATH=$HOME/.elan/bin:$PATH lake env lean
  SSExactMajority/UpperBound/Time/RankInitDescent.lean`. NEVER lake build.
- The per-step probability plumbing is mechanical — copy the structure of an existing
  `PEM_*_descent_prob_lower_bound` in Time.lean. The math (φ decreases) is settled above.
