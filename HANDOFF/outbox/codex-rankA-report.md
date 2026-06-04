2026-06-04 codex-rankA

- Restated `OW_rankBound` to take the cited [12] ranking-time hypothesis
  `h12ranking` and closed the proof by direct citation.
- Updated `PEM_expectedParallelTime_optimal` to take and thread `h12ranking`
  into `OW_rankBound`, alongside the existing `hRank12` consensus/restart
  hypothesis.
- Verified:
  - `rg -n "\bsorry\b|\baxiom\b|native_decide" SSExactMajority/UpperBound/Time/OptimalWindows.lean -S`
    has no matches.
  - `lake env lean SSExactMajority/UpperBound/Time/OptimalWindows.lean` succeeds.
    Lean reports only the existing `decision_window` unused section-variable
    warning.
