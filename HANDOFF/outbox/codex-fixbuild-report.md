# codex-fixbuild report

- Fixed `DrainProductive.lean` hTimer0 `Finset.le_sup` elaboration by passing
  the supremum function explicitly.
- Fixed `OptimalWindows.lean` build-only elaboration issues:
  - `CRS_to_silence_of_rank12` now omits the unused
    `[Inhabited (Fin n x Fin n)]` section variable, matching its callers.
  - `OW_consensusBound` proves `K > 0` from explicit `decisionWindow n > 0`
    instead of relying on `positivity`.
- Builds:
  - `lake build SSExactMajority.UpperBound.Time.DrainProductive`: success
    (`Built ... DrainProductive (536s)`).
  - `lake build SSExactMajority.UpperBound.Time.OptimalWindows`: success
    (`Build completed successfully (3251 jobs)`).
- Audit:
  - No `sorry`, `axiom`, `native_decide`, or `admit` tokens in
    `DrainProductive.lean` or `OptimalWindows.lean`.
  - `PEM_expectedParallelTime_optimal` has only the [12] hypotheses
    `h12ranking`, `h12resetDuration`, `h12rank`, and `h12reRank`; no
    `hRank12` parameter remains.
