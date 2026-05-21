The user is asking to prove the first `sorry` in `SSExactMajority/Convergence/BurmanProof.lean`. Here are the lines around the `sorry` block (~80-150 lines):

```lean
/-! ### Unsettled branch induction (from ChatGPT)

Well-founded induction on unsettledMass = Σ (errorcount + 1). -/

def unsettledMass (C : Config (AgentState n) Opinion n) : ℕ :=
  Finset.fold (· + ·) 0 (fun w : Fin n =>
    if (C w).1.role == .Unsettled then (C w).1.errorcount + 1 else 0) Finset.univ

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
  sorry -- Complex protocol trace: rankDeltaOSSR Part 3 recruitment / Part 4 errorcount
  -- Cases: (A) v Settled + recruit guard → w Settled → mass ↓
  --        (B) Part 4: errorcount hits 0 → both Resetting (left disjunct)
  --        (C) Part 4: errorcount > 0 → mass ↓ by errorcount decrease
```

Could you provide the replacement proof block for `unsettled_one_step_progress`? Please format it carefully and just return the final Lean code for that theorem block so I can drop it in.