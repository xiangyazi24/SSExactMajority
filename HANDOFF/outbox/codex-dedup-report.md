# codex-dedup report

Date: 2026-06-04

## Relationship checked

The two old `P_EM_solves_SSEM_concrete` declarations were different
theorems, not duplicate proofs of the same statement:

* `Convergence/Final.lean` keeps the parameterized concrete theorem for an
  arbitrary `rankDelta`, assuming `RankDeltaSettledFix rankDelta`,
  `hRankPhase`, `hNonMed`, and `hSout`.
* `Convergence/BurmanProperties.lean` is the Burman/OSSR concrete theorem:
  it fixes `rankDeltaOSSR Rmax Emax Dmax hn` and assumes one
  `BurmanConvergence` hypothesis plus `4 <= n`.

## Fix

Renamed the Burman/OSSR theorem to
`P_EM_solves_SSEM_concrete_burman`.

Updated `AxiomCheck.lean` so the "Concrete protocol -- single hypothesis"
audit prints `P_EM_solves_SSEM_concrete_burman`, preserving the intended
target instead of falling through to `Final.lean`'s parameterized theorem.

No statements were weakened; no `sorry`, `axiom`, or `native_decide` was
introduced.

## Verification

* `lake build`
  * Result: success.
  * Final line: `Build completed successfully (2606 jobs).`
  * The build included the formerly blocking root import closure and no
    duplicate `SSEM.P_EM_solves_SSEM_concrete` environment error appeared.
* `lake env lean SSExactMajority/AxiomCheck.lean`
  * Result: success.
  * `P_EM_solves_SSEM_concrete_burman` depends only on
    `[propext, Classical.choice, Quot.sound]`.

