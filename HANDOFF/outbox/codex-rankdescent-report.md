# codex-rankdescent report

## 2026-06-03

Created `SSExactMajority/UpperBound/Time/RankInitDescent.lean`.

Verified:

```bash
PATH=$HOME/.elan/bin:$PATH lake env lean SSExactMajority/UpperBound/Time/RankInitDescent.lean
```

What is proved in the new file:

- `rankInitPotential`: the requested `φ D = ∑ w, if role Resetting then 1 + delaytimer else 0`.
- `rankInitPotential_zero_noResetting`: `φ = 0` implies the no-Resetting goal.
- `exists_resetting_of_rankInitPotential_pos`: positive `φ` gives a Resetting witness.
- `rankInitPotential_le_of_bounded`: under `IsBoundedConfig M`, `φ C ≤ n * (1 + M)`.
- `rankInit_one_step_lower_bound_of_witness`: a concrete successful ordered pair has probability at least `1/(n(n-1))`.
- `allR_to_noResetting_expected_le_of_rankInit_descent`: the full `expectedHittingTime_le_of_variable_descent_until_goal` plumbing and ENNReal polynomial bound, conditional on the deterministic invariant/nonincrease/progress hypotheses.

Blocked target theorem:

```lean
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

Exact missing deterministic obligations for the variable-descent lemma:

```lean
hInvStep :
  ∀ D, Inv D → ¬ (∀ w, (D w).1.role ≠ .Resetting) →
    ∀ i j,
      Inv (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) ∨
      (∀ w, (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j w).1.role ≠ .Resetting)

hNonincrease :
  ∀ D, Inv D → ¬ (∀ w, (D w).1.role ≠ .Resetting) →
    ∀ i j,
      rankInitPotential (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) ≤
      rankInitPotential D

hp :
  ∀ k, 0 < k → ∀ D, Inv D → rankInitPotential D = k →
    (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) D
        (fun E =>
          (∀ w, (E w).1.role ≠ .Resetting) ∨
          (Inv E ∧ rankInitPotential E < k)) 1
```

Reason this is not just missing plumbing: `ConvStep.lean` proves that a selected `Resetting`/`rc=0` agent can leave `Resetting`. It does not rule out other scheduler pairs increasing `φ`. In the concrete protocol, once some agents have awakened while other agents are still `Resetting`, a scheduler step on two non-Resetting agents can create fresh `Resetting` agents through rank collision or Unsettled error monitoring. That violates `hNonincrease` for the proposed `φ`.

Concrete obstruction shape: take `n ≥ 4`, a state with at least one `Resetting rc=0` agent and two `Unsettled` agents with `errorcount = 0`. The ordered pair of those two `Unsettled` agents takes the rankDeltaOSSR error-monitoring branch and makes them `Resetting` with `resetcount = Rmax`, while the old Resetting agent remains. The no-Resetting goal is not reached and `rankInitPotential` increases from the two new Resetting contributions. Similarly, with multiple awakened `Settled` rank-0 leaders, a later Settled/Settled same-rank pair can trigger collision reset.

Conclusion: the stochastic variable-descent wrapper is proved conditionally, but the requested unconditional `allR_to_noResetting_expected_le` cannot be completed from the stated hypotheses with this `φ` unless the invariant is strengthened to exclude fresh-reset pairs, or the potential is changed to account for non-Resetting agents that can still trigger resets.
