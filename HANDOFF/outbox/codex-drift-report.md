# codex drift report

## 2026-06-03

Status: complete.

Implemented `SSExactMajority/Probability/DriftHittingTime.lean` with
`Probability.expectedHittingTime_le_of_drift`.

Proof structure:
- works from `ExpectedTime`/`RandomScheduler` PMF APIs only;
- no protocol-specific transition unfolding beyond the abstract `stepDist` and hit-flag chain definitions;
- defines private PMF expectation helpers and a false-flag tail potential;
- proves false-hit support remains in `Region` until `Goal`;
- proves the one-step drift inequality
  `tailPotential (t + 1) + ε * probNotHitBy t ≤ tailPotential t`;
- telescopes finite tails and passes through `ENNReal.tsum_eq_iSup_nat`;
- converts `finiteTail * ε ≤ φ C₀` to `finiteTail ≤ φ C₀ / ε`.

Verification:
```
PATH=$HOME/.elan/bin:$PATH lake env lean SSExactMajority/Probability/DriftHittingTime.lean
```
passed with no output.

Forbidden constructs check:
```
rg -n "sorry|axiom|native_decide" SSExactMajority/Probability/DriftHittingTime.lean
```
had no matches.
