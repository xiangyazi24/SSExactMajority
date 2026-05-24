# SSExactMajority — Work Log

## Current state (2026-05-18)

- **Qualitative formalization complete.** `P_EM_solves_SSEM_final`
  (`Convergence/BurmanConvergenceFinal.lean:16052`) is the ultimate
  unconditional theorem: for `n ≥ 4`, the concrete protocol
  `protocolPEM n n n (rankDeltaOSSR n Emax Dmax hn)` solves SSEM.
  Axioms = `[propext, Classical.choice, Quot.sound]` only.
- **`sorry` count: 0** across the entire tree (verified via
  comment-stripping scan + clean `lake build` on uisai1).
- **Burman 2021 ranking convergence**: now a *proved theorem*
  (`ranking_field_proof`), no longer an external hypothesis.
- **All four historical "residual gaps"** (`h_burman_ranking`,
  `BurmanMacroDecision`, `hStrictMajority`, `h_inv_swap` / `h_inv_dec`)
  discharged inside `P_EM_solves_SSEM_final`'s proof chain.
- **`OddRecruitDriver.lean` removed** (commit `a186ac78`, 2026-05-18).
  Bypassed by `EndpointRepair.lean` (`d1d54a94`); the file had been
  explicitly marked "no longer the main proof path" and had 3 stale
  compile errors against a never-defined `heapPrefix_recruit_step_with_child`.

### What remains — the "time-optimal" half of the paper title

| Item | File | Status |
|------|------|--------|
| Probabilistic scheduler / parallel-time definition | `Probability/RandomScheduler.lean`, `Probability/ExpectedTime.lean` | **scaffold only** |
| Theorem 3 — Ω(n log n) expected parallel time lower bound | `LowerBound/Time.lean` | **scaffold only** |
| §5.2 quantitative — O(n log n) expected parallel time upper bound for P_EM | `UpperBound/Time.lean` | **scaffold only** |

See `docs/TIME_BOUND_PLAN.md` for the planned probability layer + proof
strategy.

### Recent sessions

#### 2026-05-18 — Final sync session

- Audited codex's "all sorry cleared" claim. Initially saw `sorryAx` in
  uisai1 build log; traced to stale `.olean` cache on the build server.
- Cleaned `.lake/build/lib/lean/SSExactMajority` on uisai1 and ran fresh
  `lake build`: cache-free `#print axioms P_EM_solves_SSEM_final` shows
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
- Found `OddRecruitDriver.lean` had 3 real compile errors against the
  non-existent `heapPrefix_recruit_step_with_child` and was explicitly
  bypassed by `EndpointRepair.lean`. Removed (`a186ac78`).
- Documented current state across README / CHECKPOINT / WORK_LOG /
  UNDERSTANDING.
- Scaffolded the unfinished time-bound half (probability framework +
  Theorem 3 + upper-bound statement + design doc) for parallel work
  with codex + ChatGPT.

#### 2026-05-17 — Endpoint repair lands, sorry hits zero

- `EndpointRepair.lean` switched to the endpoint-repair approach via
  Phase C (`d1d54a94`), bypassing the abandoned per-step ResAns invariant
  in `OddRecruitDriver.lean`.
- Composition closed by `cac19f27`, consensus branch closed by
  `c13f5266`.
- The final `hMedCorrectExit` sorry inside `burmanConvergence_concrete`
  was discharged by threading `med_correct_live_seed_or_progress` +
  `reservoir_case_seed_or_progress` through
  `hMedCorrectExit_from_reentry_and_seed_prefixes`.

#### 2026-05-13 / 2026-05-15 — Multi-agent drain + dedup

- `BurmanConvergenceFinal.lean` epidemic / median-wrong / strong recursion
  on `phiCount` infrastructure built up.
- Disjunctive seed-or-progress shape replaced the over-strong pure-seed
  Props #2 / #3 (`e670e276`).

#### 2026-05-09 / 2026-05-10 — Timer descent + Burman core

- `TimerDescentNoSwap.lean` + Burman macro-step trajectory.
- `BurmanProof.lean` ranking-convergence machinery.

#### 2026-05-08 — Macro-step scaffolding

- See sections "A1 / A2 / E1 / E3" in earlier revisions of this file;
  all those gaps are now superseded by the proven `ranking_field_proof`
  + `burmanConvergence_concrete`.

## Next-up backlog (the time-optimal half)

Tracked in `docs/TIME_BOUND_PLAN.md`.  Top of the queue:

1. Decide on the probability model: `PMF`-on-pairs random scheduler vs.
   `MeasureTheory` Markov-chain semantics.  See `docs/TIME_BOUND_PLAN.md`
   "Design decision 1".
2. Define `parallelTime` (sequential steps ÷ n).
3. State and prove `time_lower_bound_omega_n_log_n` (Theorem 3) via the
   coupon-collector lifting from Theorem 2.
4. State and prove `P_EM_parallel_time_upper_bound` (§5.2 quantitative).

Each step is sized for an individual session.  Codex + ChatGPT
collaboration handles 1 and 3 in parallel.
