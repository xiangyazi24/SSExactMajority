# codex-consensus report

Status: blocked; `OW_consensusBound` was not closed.

Date: 2026-06-04

I checked the requested route in `SSExactMajority/UpperBound/Time/OptimalWindows.lean`
against the available APIs:

- `swap_live_to_cons_or_crs_or_break` gives a `1/4` window only for the union
  `IsConsensusConfig ∨ CorrectResetSeed ∨ ¬(InSswap ∧ MedianTimerAtLeast 1)`.
  It does not give any positive lower bound for the `IsConsensusConfig` branch
  itself.
- `OW_rankBound`, even taken as the other keystone, only returns to
  `InSrank ∧ MedianTimerAtLeast 35 ∧ IsTimerBoundedConfig ...`.
  Composing it with
  `PEM_swap_ProbHitWithin_InSswap_timer_live_const35_bounded` returns to a live
  swap window, but does not turn the CRS/exit branch into consensus.
- `crs_to_allR_or_break_window` reaches `(nonResettingCount = 0) ∨ ¬ CorrectResetSeed`.
  On the all-resetting side, `allR_to_consensus_bound` needs all answers correct
  and returns `Rmax*n*n + B` where `B` is a finite-state-space existential
  constant, not an explicit `O(Rmax*n^2)` bound.  The deterministic
  `correct_reset_seed_to_InSswap_ResAns_phi_zero` / `cycle_potential_reaches_consensus`
  results give existence of schedules but no explicit length/expectation bound.

Therefore the proposed renewal cannot currently satisfy the hypothesis of
`expectedHittingTime_le_window_mul_inv`:

```lean
∀ C, ¬ IsConsensusConfig C →
  p ≤ ProbHitWithin P hn C IsConsensusConfig K
```

nor the live-swap restricted version one would need before applying a geometric
restart.  The missing quantitative bridge is one of:

1. a direct constant-probability window from live `InSswap` to `IsConsensusConfig`
   in `O(Rmax*n^2)` steps, not to the union with CRS/exit;
2. an explicit polynomial CRS/all-resetting re-entry-to-consensus bound that
   preserves the correct-answer/`ResAns` information and removes the existential
   finite-state `B`;
3. an abstract renewal lemma whose hypotheses include a genuine per-cycle
   success probability and an explicit bounded return time, plus the concrete
   theorem establishing that CRS/exit cycles have such a success probability.

Verification:

```bash
lake env lean SSExactMajority/UpperBound/Time/OptimalWindows.lean
```

Result: success.  Warnings are the existing `OW_rankBound` and
`OW_consensusBound` `sorry`s, plus the existing unused-section-variable warning
on `decision_window`.

Note: running `lake env lean OptimalWindows.lean` from
`SSExactMajority/UpperBound/Time/` fails because Lake does not put the package
root on the import search path in that invocation (`unknown module prefix
'SSExactMajority'`).  The successful check above is the project-root form.
