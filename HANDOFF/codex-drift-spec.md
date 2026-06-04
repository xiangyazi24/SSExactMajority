# Codex task (uisai1): additive-drift hitting-time theorem (abstract probability)

We proved the protocol has NO per-step monotone potential, so `variable_descent` (requires
hNonincrease) is unusable. We need the DRIFT analog. NEW file
`SSExactMajority/Probability/DriftHittingTime.lean` (import the Probability layer only).

## Target (additive / variable drift hitting-time bound)
```
theorem expectedHittingTime_le_of_drift
    {Q X Y : Type*} {n : ℕ} [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Region : Config Q X n → Prop)
    [DecidablePred Goal] [DecidablePred Region]
    (φ : Config Q X n → ℕ) (ε : ENNReal) (hε0 : 0 < ε) (hεtop : ε ≠ ⊤)
    (hReg0 : Region C₀)
    (hZeroGoal : ∀ C, Region C → φ C = 0 → Goal C)
    (hRegStep : ∀ C, Region C → ¬ Goal C → ∀ i j : Fin n,
        Region (C.step P i j) ∨ Goal (C.step P i j))
    (hDrift : ∀ C, Region C → ¬ Goal C →
        (∑' D : Config Q X n, (stepDist P hn C D) * (φ D : ENNReal)) + ε ≤ (φ C : ENNReal)) :
    Probability.expectedHittingTime P hn C₀ Goal ≤ ((φ C₀ : ENNReal)) / ε
```
(`stepDist P hn C` is the one-step PMF; `∑' D, stepDist C D * φ D` is `E[φ after one step]`.
Adjust to the exact `stepDist`/`nthStepDist`/`probNotHitBy` API in ExpectedTime.lean.)

## Proof idea (standard additive drift / optional stopping)
`M_t := φ(X_t) + ε·(t ∧ τ)` is a supermartingale until the hitting time τ of Goal (hDrift
gives `E[φ(X_{t+1}) | not yet hit] + ε ≤ φ(X_t)`). So `ε·E[t∧τ] ≤ φ(C₀)`, giving
`E[τ] ≤ φ(C₀)/ε`. Concretely, mirror the structure of
`expectedHittingTime_le_of_variable_descent` / `expectedHittingTime_le_of_tail_bound`
(ExpectedTime.lean:4265/2926): bound `probNotHitBy`/the tail via the drift telescoping.
Likely cleanest: show `∑_{t} probNotHitBy P hn C₀ Goal t ≤ φ(C₀)/ε` by a drift-on-the-tail
induction, then `expectedHittingTime = ∑_t probNotHitBy` (or ≤ via the existing tail lemma).

## HARD RULES
- NO sorry/axiom/native_decide. Blocked → exact goal+missing API to
  HANDOFF/outbox/codex-drift-report.md. This is ABSTRACT probability — no protocol unfolding,
  so it should be fully provable from the ExpectedTime API. Don't weaken to trivial.
- ONLY DriftHittingTime.lean. Self-verify `PATH=$HOME/.elan/bin:$PATH lake env lean
  SSExactMajority/Probability/DriftHittingTime.lean`. NEVER lake build. Report status.
