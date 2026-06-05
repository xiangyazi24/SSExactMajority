# cxfix report

## Result

- Added `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean`.
- Defined the faithful `[12]` reset-completion contract targeting a fresh reset seed, not `EpidemicPhiGoal`.
- Proved the faithful reset-to-phi-goal composition over `PEMProtocol n 1` by chaining `freshSeedReach` with `answer_epidemic_bridge_from_fresh_resetting` via `Probability.ProbHitWithin_add_ge_mul`.
- No `sorry`, `axiom`, or `native_decide` in `OptimalWindowsFaithful.lean`.

## Theorems

- `SSEM.FreshResetSeedTarget`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:11`
- `SSEM.CRSReset12Faithful`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:21`
- `SSEM.faithful_reset_to_phiGoal`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:38`

## Verification

```bash
/data/home/xhuan5/.elan/bin/elan run leanprover/lean4:v4.30.0 lake build SSExactMajority.UpperBound.Time.OptimalWindowsFaithful
```

Result: build completed successfully.

## Capstone Result

- Appended the faithful capstone bridge to `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean`.
- Added import `SSExactMajority.UpperBound.Time.GenericKeystone`.
- Proved `SSEM.crsReset12Faithful_to_generic`, constructing
  `CRSResetCompletion12Generic (trank := 1)` from the faithful fresh-reset
  contract plus the proven answer-epidemic bridge, using
  `Probability.ProbHitWithin_mono_goal` to drop the `AllAgentsResetting`
  conjunct.
- Proved `SSEM.PEM_expectedParallelTime_On_faithful` by calling the existing
  `PEM_expectedParallelTime_On` with reset probability `p_reset * (pE / 2)`
  and window `K_reset + K_bridge`.
- No `sorry`, `axiom`, or `native_decide` in `OptimalWindowsFaithful.lean`.

## Capstone Theorems

- `SSEM.FreshResetSeedTarget`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:12`
- `SSEM.CRSReset12Faithful`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:22`
- `SSEM.faithful_reset_to_phiGoal`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:39`
- `SSEM.crsReset12Faithful_to_generic`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:87`
- `SSEM.PEM_expectedParallelTime_On_faithful`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:162`

## Capstone Verification

```bash
/data/home/xhuan5/.elan/bin/elan run leanprover/lean4:v4.30.0 lake build SSExactMajority.UpperBound.Time.OptimalWindowsFaithful
```

Result: build completed successfully.

O(n) status: yes, genuinely O(n). The theorem reuses the generic renewal
machinery with global window
`OW_globalWindow n C_rank PEM_trank1_timer (K_reset + K_bridge) T_rank T_rerank`;
the reset and bridge windows are both assumed quadratic, and the final bound is
that window divided by `n`. The probability factor
`(p_reset * (pE / 2)) * 128⁻¹` is a positive constant under
`h12reset.resetProb_pos` and `hpE_pos`.

## Drain-Tail Result

- Added `SSExactMajority/UpperBound/Time/DrainTailBound.lean`.
- Proved the closed-form drain-tail bound using `Nat.choose_le_pow_div`
  and `Stirling.le_factorial_stirling`.
- Final constant: `11`, from `4 * Real.exp 1 < 11`.
- No `sorry`, `axiom`, or `native_decide` in `DrainTailBound.lean`.

## Drain-Tail Theorems

- `SSEM.drainNoWakeTail_le_geom`:
  `SSExactMajority/UpperBound/Time/DrainTailBound.lean:139`
- `SSEM.drainNoWakeTail_le_geom_at_Dmax_ge_n`:
  `SSExactMajority/UpperBound/Time/DrainTailBound.lean:162`

## Drain-Tail Verification

```bash
/data/home/xhuan5/.elan/bin/elan run leanprover/lean4:v4.30.0 lake build SSExactMajority.UpperBound.Time.DrainTailBound
```

Result: build completed successfully.

Asymptotic-to-zero status: not included as a separate topological eventual
theorem. The delivered corollary is the spec-minimum closed form:
when `Dmax >= n`, `drainNoWakeTail n K Dmax <= n * (1/2)^n`.

## Epidemic Rephrase Result

- Updated `SSEM.StandardEpidemicFastHypothesisPEM` to use the faithful target
  `fun D => EpidemicPhiGoal m D OR SomeAgentAwake D`.
- Re-derived `SSEM.answer_epidemic_bridge_from_fresh_resetting` with a
  top-level split on that disjunction. Its conclusion is unchanged:
  `pE / 2 <= ProbHitWithin (EpidemicPhiGoal m AND AllAgentsResetting) K`.
- Strengthened `SSEM.CRSReset12Faithful.freshSeedReach` to require
  `WellFormed 1 Rmax Emax Dmax C`.
- Threaded the strengthened precondition through
  `faithful_reset_to_phiGoal`, `crsReset12Faithful_to_generic`, and
  `PEM_expectedParallelTime_On_faithful`.
- Added the [12] fresh-seed doc-comment explaining the simultaneous
  all-Resetting, `delaytimer = Dmax` stopping event.
- No `sorry`, `axiom`, or `native_decide` in the two touched files.

## Epidemic Rephrase Theorems

- `SSEM.StandardEpidemicFastHypothesisPEM`:
  `SSExactMajority/UpperBound/Time/AnswerEpidemicBridge.lean:73`
- `SSEM.answer_epidemic_bridge_from_fresh_resetting`:
  `SSExactMajority/UpperBound/Time/AnswerEpidemicBridge.lean:115`
- `SSEM.CRSReset12Faithful`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:29`
- `SSEM.faithful_reset_to_phiGoal`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:46`
- `SSEM.crsReset12Faithful_to_generic`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:94`
- `SSEM.PEM_expectedParallelTime_On_faithful`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:169`

## Epidemic Rephrase Verification

```bash
/data/home/xhuan5/.elan/bin/elan run leanprover/lean4:v4.30.0 lake build SSExactMajority.UpperBound.Time.OptimalWindowsFaithful
```

Result: build completed successfully.

Keystone conclusion status: unchanged. The theorem
`SSEM.PEM_expectedParallelTime_On_faithful` still concludes the same bound
with reset probability `p_reset * (pE / 2)` and the same global window
`OW_globalWindow n C_rank PEM_trank1_timer (K_reset + K_bridge) T_rank T_rerank`.

## Wake-Budget Result

- Replaced the exact-fresh target with `SSEM.ResetSeedWithWakeBudget`, charging
  only dormant agents (`role = Resetting` and `resetcount = 0`) with budget `d`.
- Generalized `SSEM.WakeLoadCertificateAt` and the PEM no-wake certificate to
  `d ≤ Dmax`, including the positive-resetcount and recruitment refresh cases.
- Generalized the unconditional drain tail to
  `n * choose K d * (2/n)^d`.
- Threaded `d` through the answer-epidemic bridge and the faithful keystone.
  The keystone expected-time conclusion keeps the same global window and
  probability factor `p_reset * (pE / 2)`.
- `FreshResetSeedTarget` is gone from `SSExactMajority/`.
- No `sorry`, `axiom`, or `native_decide` in the touched Lean files.

## Wake-Budget Theorems

- `SSEM.WakeLoadCertificateAt`:
  `SSExactMajority/UpperBound/Time/DrainNoWake.lean:75`
- `SSEM.wake_load_certificate_PEM_on_no_wake_prefix`:
  `SSExactMajority/UpperBound/Time/DrainNoWakeCert.lean:685`
- `SSEM.drain_probHitWithin_le_choose_unconditional`:
  `SSExactMajority/UpperBound/Time/DrainNoWakeTrace.lean:441`
- `SSEM.no_wake_prob_ge_half`:
  `SSExactMajority/UpperBound/Time/AnswerEpidemicBridge.lean:44`
- `SSEM.answer_epidemic_bridge_from_fresh_resetting`:
  `SSExactMajority/UpperBound/Time/AnswerEpidemicBridge.lean:115`
- `SSEM.ResetSeedWithWakeBudget`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:18`
- `SSEM.CRSReset12Faithful`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:34`
- `SSEM.faithful_reset_to_phiGoal`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:52`
- `SSEM.crsReset12Faithful_to_generic`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:100`
- `SSEM.PEM_expectedParallelTime_On_faithful`:
  `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:176`

## Wake-Budget Verification

```bash
/data/home/xhuan5/.elan/bin/elan run leanprover/lean4:v4.30.0 lake build SSExactMajority.UpperBound.Time.OptimalWindowsFaithful
```

Result: build completed successfully.

Fresh `#print axioms` for
`wake_load_certificate_PEM_on_no_wake_prefix`,
`drain_probHitWithin_le_choose_unconditional`,
`answer_epidemic_bridge_from_fresh_resetting`,
`faithful_reset_to_phiGoal`, `crsReset12Faithful_to_generic`, and
`PEM_expectedParallelTime_On_faithful`:
`[propext, Classical.choice, Quot.sound]`.

O(n) status: unchanged and still genuinely O(n) under the same window
assumptions. The final faithful theorem still bounds expected parallel time by
the existing `OW_globalWindow ... (K_reset + K_bridge) ...` divided by `n`,
with constant probability factor `(p_reset * (pE / 2)) * 128⁻¹`.

## Log-Tree Reset Result

- Added `SSExactMajority/Convergence/LogTreeReset.lean`.
- Proved the missing symmetric delaytimer endpoint for positive-resetcount
  Resetting/Resetting synchronization.
- Proved exact two-sided pair drain: two positive Resetting agents can be
  repeatedly paired until both have `role = Resetting`, `resetcount = 0`, and
  `delaytimer = Dmax`, while all other agents are unchanged.
- Proved disjoint covering pair-list drain: a disjoint list of pairs covering
  the agents drains all covered agents to the exact fresh state without
  selecting them after dormancy.
- Wired these into `all_fresh_from_log_seed`.

Important preconditions landed for `all_fresh_from_log_seed`:

- `hDmax : 1 < Dmax`
- `hfuel : Nat.clog 2 n + 1 ≤ R`
- a seed `r` with `(C r).1.role = .Resetting` and `R ≤ (C r).1.resetcount`
- `hBalancedTreeGrowth`: explicit Phase-A balanced-growth certificate from
  any log-fueled seed, producing a schedule after which every agent is
  `Resetting` with positive resetcount
- a disjoint pair list `pairs` satisfying `PairListDisjoint pairs`

## Endpoint Strong-Seed Time Windows

- Added `SSExactMajority/UpperBound/Time/LogWindows.lean`.
- Re-defined the time-side endpoint locally as `SSEM.StrongResetSeed`, matching
  the correctness-side strong seed shape but avoiding a heavy `LogRegimeFinal`
  import.
- Re-derived the time-window chain with the strong endpoint:
  `generic_crs_of_InSswap_break_with_MedC_strong`,
  `generic_timer_ge_two_descent_step_strong`,
  `generic_PEM_expected_timer_drain_poly_strong`,
  `generic_timer_drain_window_strong`,
  `generic_timer_drain_to_zero_productive_strong`,
  `generic_PEM_expected_reset_trigger_v2_strong`,
  `generic_MAClive_to_consensus_or_crs_strong`,
  `generic_MAClive_to_consensus_or_crs_window_strong`, and
  `generic_swap_live_to_cons_or_strong_or_break`.
- Rewired the faithful reset input through `CRSReset12FaithfulStrong` and
  `CRSResetCompletion12StrongGeneric`, whose reset reach premise consumes
  `StrongResetSeed Rmax` rather than old `CorrectResetSeed`.
- Proved `PEM_expectedParallelTime_On_faithful_log` over `PEMProtocol n 1`
  using strong renewal endpoint. It has no `n ≤ Rmax`, `n ≤ Emax`, or
  `n ≤ Dmax` hypothesis. The only timer-budget constraint is
  `d ≤ Dmax`, carried by `h12reset.wakeBudget_le_Dmax`.
- No proof uses the old `nonResettingCount < resetcount` dominance clause.

## Endpoint Theorems

- `SSEM.StrongResetSeed`: `SSExactMajority/UpperBound/Time/LogWindows.lean:26`
- `SSEM.generic_crs_of_InSswap_break_with_MedC_strong`:
  `SSExactMajority/UpperBound/Time/LogWindows.lean:946`
- `SSEM.generic_timer_ge_two_descent_step_strong`:
  `SSExactMajority/UpperBound/Time/LogWindows.lean:1057`
- `SSEM.generic_timer_drain_to_zero_productive_strong`:
  `SSExactMajority/UpperBound/Time/LogWindows.lean:1275`
- `SSEM.generic_PEM_expected_timer_drain_poly_strong`:
  `SSExactMajority/UpperBound/Time/LogWindows.lean:1530`
- `SSEM.generic_timer_drain_window_strong`:
  `SSExactMajority/UpperBound/Time/LogWindows.lean:1581`
- `SSEM.generic_PEM_expected_reset_trigger_v2_strong`:
  `SSExactMajority/UpperBound/Time/LogWindows.lean:1603`
- `SSEM.generic_MAClive_to_consensus_or_crs_strong`:
  `SSExactMajority/UpperBound/Time/LogWindows.lean:1882`
- `SSEM.generic_MAClive_to_consensus_or_crs_window_strong`:
  `SSExactMajority/UpperBound/Time/LogWindows.lean:1959`
- `SSEM.generic_swap_live_to_cons_or_strong_or_break`:
  `SSExactMajority/UpperBound/Time/LogWindows.lean:1983`
- `SSEM.CRSReset12FaithfulStrong`:
  `SSExactMajority/UpperBound/Time/LogWindows.lean:2070`
- `SSEM.CRSResetCompletion12StrongGeneric`:
  `SSExactMajority/UpperBound/Time/LogWindows.lean:2134`
- `SSEM.crsReset12FaithfulStrong_to_generic`:
  `SSExactMajority/UpperBound/Time/LogWindows.lean:2151`
- `SSEM.CRSStrong_to_consensus_faithful_product_generic`:
  `SSExactMajority/UpperBound/Time/LogWindows.lean:2224`
- `SSEM.PEM_expectedParallelTime_optimal_generic_strong`:
  `SSExactMajority/UpperBound/Time/LogWindows.lean:2343`
- `SSEM.PEM_expectedParallelTime_On_faithful_log`:
  `SSExactMajority/UpperBound/Time/LogWindows.lean:2743`

## Endpoint Final Hypotheses

`PEM_expectedParallelTime_On_faithful_log` assumes:

- `[Inhabited (Fin n × Fin n)]`
- `hn4 : 4 ≤ n`
- `hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax`
- `hd_pos : 0 < d`
- constants `C_rank T_rank T_rerank`
- cited ranking window `h12ranking`
- strong faithful reset contract
  `h12reset : CRSReset12FaithfulStrong ... d p_reset C_reset K_reset`
- cited epidemic-speed hypothesis `epidemicFast`
- tail hypothesis `hTail : drainNoWakeTail n K_bridge d ≤ pE / 2`
- `hpE_pos : 0 < pE`, `hpE_le_one : pE ≤ 1`
- bridge window bound `hBridgeWindow : K_bridge ≤ C_bridge * n * n`
- cited rank and re-rank windows `h12rank`, `h12reRank`

The conclusion is the same O(n)-form renewal bound with global window
`OW_globalWindow n C_rank PEM_trank1_timer (K_reset + K_bridge) T_rank T_rerank`
and probability factor `(p_reset * (pE / 2)) * 128⁻¹`.

O(n) status: yes, genuinely O(n) under the stated constant-probability and
quadratic-window cited premises. The global sequential window is quadratic in
`n` and the expected parallel time theorem divides it by `n`.

## Endpoint Verification

```bash
/data/home/xhuan5/.elan/bin/lake env lean SSExactMajority/UpperBound/Time/LogWindows.lean --json
/data/home/xhuan5/.elan/bin/lake build SSExactMajority.UpperBound.Time.LogWindows
```

Result: both commands completed successfully. The target Lake build still
prints pre-existing lint warnings from dependencies and style warnings in the
new large copied proofs, but no errors.

Actual command-form scan for `sorry`, `axiom`, and `native_decide` in the
touched source files is empty.

## No-Answer / Finalwire Audit Result

- Added the answer-agnostic fresh+unique endpoint
  `SSEM.all_fresh_unique_from_log_seed_no_answer`.
- Re-routed reset snapshots through the log-tree fresh+unique endpoint and
  then `dormant_to_RankingEndpoint`, with no answer hypothesis and no
  `n <= Dmax`, `n <= Rmax`, or `n <= Emax`.
- Re-derived the bad-ranking parity handlers at clog level:
  the reset-trigger branches now use
  `step_reset_snapshot_to_RankingEndpoint_log`; the consensus-only branches
  reuse the existing no-linear lemmas.
- Re-derived the no-reset ranking entry at clog level:
  `phase1_no_reset_trigger_snapshot_or_InSrank_log` and
  `ranking_of_no_reset_by_parity_log`.
- Did not produce `burmanConvergence_concrete_log` or
  `P_EM_solves_SSEM_log`. The remaining blocker is genuine in the current
  interface: `BurmanConvergence.ranking` is for arbitrary configurations, and
  the case where the initial/current configuration already contains
  `Resetting` agents but not a strong `rc = Rmax`, leader `.L` seed still
  routes through the old arbitrary all-Resetting normalization chain.

## No-Answer Theorems

- `SSEM.all_fresh_unique_from_log_seed_no_answer`:
  `SSExactMajority/Convergence/LogTreeReset.lean:4581`
- `SSEM.reset_snapshot_to_RankingEndpoint_log`:
  `SSExactMajority/Convergence/LogRegimeFinal.lean:66`
- `SSEM.step_reset_snapshot_to_RankingEndpoint_log`:
  `SSExactMajority/Convergence/LogRegimeFinal.lean:101`
- `SSEM.BadRankingStart_even_to_RankingEndpoint_log`:
  `SSExactMajority/Convergence/LogRegimeFinal.lean:573`
- `SSEM.BadRankingStart_odd_to_RankingEndpoint_log`:
  `SSExactMajority/Convergence/LogRegimeFinal.lean:866`
- `SSEM.ranking_of_no_reset_by_parity_log`:
  `SSExactMajority/Convergence/LogRegimeFinal.lean:1102`

## No-Answer Landed Hypotheses

- `all_fresh_unique_from_log_seed_no_answer`:
  `[Inhabited (Fin n x Fin n)]`, `hn : 0 < n`, `hDmax : 1 < Dmax`,
  `hn2 : 2 <= n`, seed role `Resetting`,
  `2 * Nat.clog 2 n + 2 <= seed.resetcount`, and seed leader `.L`.
- `reset_snapshot_to_RankingEndpoint_log` and
  `step_reset_snapshot_to_RankingEndpoint_log`:
  `[Inhabited (Fin n x Fin n)]`, `hn : 0 < n`, `hn4 : 4 <= n`,
  `hDmax1 : 1 < Dmax`, and
  `hRlog : 2 * Nat.clog 2 n + 2 <= Rmax`.
- `BadRankingStart_even_to_RankingEndpoint_log`,
  `BadRankingStart_odd_to_RankingEndpoint_log`, and
  `ranking_of_no_reset_by_parity_log`:
  the same `hn4`, `hDmax1`, and `hRlog` clog-level hypotheses only.

## No-Answer Blocker

The exact remaining consumers of the linear arbitrary-reset carrier are:

- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:2192`
  `reach_known_entry_from_any`, called by
  `ranking_field_proof` at line `2262`.
- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:2168`
  `resetting_exists_to_known_entry`, called when a Resetting agent already
  exists.
- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:2042`
  `partial_resetting_to_known_entry`, whose all-Resetting dispatch can return
  arbitrary all-Resetting states, not necessarily the strong fresh/unique
  endpoint.
- `SSExactMajority/Convergence/BurmanProof.lean:15115`
  `ranking_from_all_resetting`, with subcases including no leader and mixed
  low-resetcount leaders:
  `ranking_from_all_resetting_no_leader` at line `14611` and
  `ranking_from_all_resetting_zero_leader_mixed` at line `15037`.

Why this is not just a reset-snapshot rewire: the proven log endpoint needs a
seed with `leader = .L` and reset fuel at least `2 * clog2 n + 2`; the
arbitrary all-Resetting cases above may have no leader, non-unique leaders,
or only low resetcounts. The bad-ranking snapshot path does preserve
`rc = Rmax` and `leader = .L`; that path is now rerouted.

## No-Answer Verification

```bash
/data/home/xhuan5/.elan/bin/lake build SSExactMajority.Convergence.LogRegimeFinal
grep -nE '\bsorry\b|\baxiom\b' SSExactMajority/Convergence/LogTreeReset.lean SSExactMajority/Convergence/LogRegimeFinal.lean
```

Result: target build completed successfully. The grep returned no matches.
- coverage `∀ w, w ∈ pairEndpoints pairs`

Status note: Phase B/drain is fully discharged. The balanced-tree Phase A
doubling bookkeeping is isolated as the explicit `hBalancedTreeGrowth`
precondition; it is not eliminated in this file.

## Log-Tree Theorems

- `SSEM.rankDeltaOSSR_both_rc_pos_snd_delay_final`:
  `SSExactMajority/Convergence/LogTreeReset.lean:21`
- `SSEM.step_both_rc_pos_snd_delay_final`:
  `SSExactMajority/Convergence/LogTreeReset.lean:36`
- `SSEM.drain_pair_rc_with_both_delay`:
  `SSExactMajority/Convergence/LogTreeReset.lean:69`
- `SSEM.drain_pair_list_to_fresh_on_endpoints`:
  `SSExactMajority/Convergence/LogTreeReset.lean:188`
- `SSEM.all_fresh_from_log_seed`:
  `SSExactMajority/Convergence/LogTreeReset.lean:305`

## Log-Tree Verification

```bash
/data/home/xhuan5/.elan/bin/lake build SSExactMajority.Convergence.LogTreeReset
```

Result: build completed successfully. No `sorry`, `axiom`, or
`native_decide` in `SSExactMajority/Convergence/LogTreeReset.lean`.

## Phase-A Balanced Growth Result

- Discharged the balanced-doubling growth core in
  `SSExactMajority/Convergence/LogTreeReset.lean`.
- Added the cardinal-generation machinery: `highSet`, disjoint source/target
  pair selection, one-generation growth, and the logarithmic iteration.
- Proved `balanced_tree_growth` with the requested seed fuel
  `Nat.clog 2 n + 1`.
- Added an unconditional fresh-reset entry point. Exact landed preconditions:
  `2 ≤ n`, `1 < Dmax`, and seed fuel `Nat.clog 2 n + 2 ≤ R`.
  The extra fuel unit is used only for the odd-leftover drain: a partner whose
  old resetcount is already `0` is not refreshed by `processAgent` in the
  `rc = 1` case, so the leftover is first synchronized from fuel at least `2`
  into a positive equal-fuel pair and then drained by the proven pair drain.
- Kept the compatibility theorem
  `all_fresh_from_log_seed_via_balanced_growth`, which feeds the proven
  `balanced_tree_growth` into the older pair-list theorem when a disjoint
  covering pair list is supplied.

Theorems landed:

- `SSEM.balanced_tree_growth_card_iter`:
  `SSExactMajority/Convergence/LogTreeReset.lean:618`
- `SSEM.balanced_tree_growth`:
  `SSExactMajority/Convergence/LogTreeReset.lean:674`
  Preconditions: `0 < n`, `1 < Dmax`, seed `r` Resetting, and
  `Nat.clog 2 n + 1 ≤ (C r).1.resetcount`.
- `SSEM.balanced_tree_growth_floor`:
  `SSExactMajority/Convergence/LogTreeReset.lean:729`
  Preconditions: `0 < n`, `1 < Dmax`, `0 < d`, seed `r` Resetting, and
  `Nat.clog 2 n + d ≤ (C r).1.resetcount`.
- `SSEM.drain_all_floor_two_to_fresh`:
  `SSExactMajority/Convergence/LogTreeReset.lean:1118`
  Preconditions: `0 < n`, `2 ≤ n`, `1 < Dmax`, and all agents Resetting with
  resetcount at least `2`.
- `SSEM.all_fresh_from_log_seed_via_balanced_growth`:
  `SSExactMajority/Convergence/LogTreeReset.lean:1263`
  Preconditions: the old disjoint covering pair-list inputs, but no
  `hBalancedTreeGrowth` hypothesis.
- `SSEM.all_fresh_from_log_seed_unconditional`:
  `SSExactMajority/Convergence/LogTreeReset.lean:1286`
  Preconditions: `0 < n`, `2 ≤ n`, `1 < Dmax`, seed `r` Resetting, and
  `Nat.clog 2 n + 2 ≤ R ≤ (C r).1.resetcount`.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake build SSExactMajority.Convergence.LogTreeReset
```

Result: build completed successfully. Grep found no `sorry`, `axiom`, or
`native_decide` in `SSExactMajority/Convergence/LogTreeReset.lean`.

Fresh `#print axioms` for `balanced_tree_growth`,
`balanced_tree_growth_floor`, and `all_fresh_from_log_seed_unconditional`:
`[propext, Classical.choice, Quot.sound]`.

## Log-Regime Rethreading Audit

New file:

- `SSExactMajority/Convergence/LogRegimeConvergence.lean`

Compiled bridge/audit facts:

- `SSEM.log_seed_to_all_fresh`:
  `SSExactMajority/Convergence/LogRegimeConvergence.lean:18`
  Preconditions landed: `0 < n`, `2 <= n`, `1 < Dmax`,
  `Nat.clog 2 n + 2 <= Rmax`, and an explicit seed witness
  `Rmax <= resetcount`.
- `SSEM.all_resetting_of_all_fresh`:
  `SSExactMajority/Convergence/LogRegimeConvergence.lean:38`
- `SSEM.all_resetcount_zero_of_all_fresh`:
  `SSExactMajority/Convergence/LogRegimeConvergence.lean:46`
- `SSEM.all_delaytimer_eq_of_all_fresh`:
  `SSExactMajority/Convergence/LogRegimeConvergence.lean:54`
- `SSEM.fresh_uniform_unique_to_FreshRankingStart_resAns_noPhi`:
  `SSExactMajority/Convergence/LogRegimeConvergence.lean:64`
  Preconditions landed for the fresh-state Phase-A bridge:
  `4 <= n`, `0 < Rmax`, `0 < Dmax`, all agents fresh, uniform answer, and
  a unique leader.  This confirms that once the endpoint is truly dormant
  (zero resetcount + unique leader + uniform answer), the answer-preserving
  Phase-A bridge does not need `n <= Dmax`.

Blocked final theorem:

- `burmanConvergence_concrete_log`: not produced.
- `P_EM_solves_SSEM_log`: not produced.

Exact blocker:

1. `CorrectResetSeed` erases the log fuel needed by
   `all_fresh_from_log_seed_unconditional`.  Its definition only exposes
   `nonResettingCount C < resetcount`, not `resetcount = Rmax` or
   `Nat.clog 2 n + 2 <= resetcount`:
   `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:13787`.
   The existing seed-or-progress interfaces return only `CorrectResetSeed`,
   so the log theorem cannot be threaded through them without strengthening
   those interfaces:
   `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:15814`.
2. The current re-entry consumer still routes a correct seed through the
   positive-resetcount path and therefore requires `n <= Dmax`:
   `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:13666` and the
   call at `:13719`.  The real uses are the positive-resetcount delay budget
   `positiveRcExcept_card < delaytimer`:
   `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:6555` and
   `:6633`.
3. The available all-fresh theorem gives only role/resetcount/delaytimer.
   It does not give uniform answer or unique leader, both of which are needed
   by the zero-resetcount answer-preserving bridge:
   `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:7470`.
4. There is an independent ranking-side carrier unrelated to the fresh reset
   endpoint: `ranking_from_InSrank_by_parity` still requires `n <= Dmax` and
   `n <= Rmax`, and its bad-ranking handlers consume those bounds at
   `SSExactMajority/Convergence/BurmanProof.lean:12376` and `:13074`.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake build SSExactMajority.Convergence.LogRegimeConvergence
```

Result: build completed successfully. Grep found no `sorry`, `axiom`, or
`native_decide` in `SSExactMajority/Convergence/LogRegimeConvergence.lean`.

## Uniform Log-Tree Semantics and Partial Bridge

Spec file executed:

- `HANDOFF/uniform_spec.md`

Mechanism facts checked first:

1. Recruitment record update does not set `answer`: `propagateReset` only sets
   `role`, `resetcount`, and `delaytimer` on the recruited endpoint at
   `SSExactMajority/Protocol/RankDelta.lean:120-123`.  The local preservation
   theorem is `propagateReset_answer_preserved` at
   `SSExactMajority/Protocol/RankDelta.lean:165-168`.  In the full PEM
   transition, however, a newly-entering Resetting endpoint is then reset to
   `answer := .phi` by `transitionPEM_prePhase4` at
   `SSExactMajority/Protocol/Transition.lean:37-42`.
2. Answer spreading is between any two Resetting endpoints, not dormant-only:
   `transitionPEM_prePhase4` copies a non-phi answer into a phi Resetting peer
   at `SSExactMajority/Protocol/Transition.lean:49-55`.  It does not overwrite
   an endpoint that already has a non-phi answer.
3. Leader resolution is in `rankDeltaOSSR`: after `propagateReset`, if both
   resulting endpoints are Resetting leaders `.L`, the second endpoint is
   changed to `.F` at `SSExactMajority/Protocol/RankDelta.lean:196-202`.
   Recruitment itself inherits the recruited endpoint's old leader unless this
   `.L`/`.L` resolution fires.

Mechanism-level blocker for the bare seed target:

- From only the collision-style seeded agents, the protocol cannot force
  uniform answer over an arbitrary already-Resetting population.  The only
  answer-spreading rule copies a non-phi answer into `phi`
  (`Transition.lean:49-55`); it never overwrites a wrong non-phi Resetting
  answer.  Therefore the requested unconditional
  `all_fresh_uniform_from_log_seed` endpoint is not derivable from just the two
  seed agents without an additional invariant excluding wrong non-phi Resetting
  answers, or a stronger producer precondition.

Compiled bridge landed under the faithful invariant that every current
Resetting agent already carries the majority answer:

- `generation_pair_list_answer`:
  `SSExactMajority/Convergence/LogTreeReset.lean:719`
- `balanced_tree_generation_answer_root`:
  `SSExactMajority/Convergence/LogTreeReset.lean:1105`
- `balanced_tree_growth_floor_answer_leader`:
  `SSExactMajority/Convergence/LogTreeReset.lean:1639`
- `log_seed_uniform_leader_to_FreshRankingStart_resAns_noPhi`:
  `SSExactMajority/Convergence/LogRegimeConvergence.lean:44`

Exact preconditions for
`log_seed_uniform_leader_to_FreshRankingStart_resAns_noPhi`:

- `[Inhabited (Fin n × Fin n)]`
- `4 <= n`
- `1 < Dmax`
- `n <= Dmax`
- `0 < Rmax`
- a seed `r` with `(C r).1.role = .Resetting`
- `Nat.clog 2 n + 1 <= (C r).1.resetcount`
- `(C r).1.leader = .L`
- `m0 = majorityAnswer C`
- `forall w, (C w).1.role = .Resetting -> (C w).1.answer = majorityAnswer C`

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake build SSExactMajority.Convergence.LogRegimeConvergence
grep -n "sorry\|axiom\|native_decide" \
  SSExactMajority/Convergence/LogTreeReset.lean \
  SSExactMajority/Convergence/LogRegimeConvergence.lean
```

Result: build completed successfully.  The grep returned no matches.

## Eliminate Linear Dmax from Log Endgame

Spec file executed:

- `HANDOFF/eliminate_spec.md`

New / completed proof pieces:

- `leader_tournament_iter`:
  `SSExactMajority/Convergence/LogTreeReset.lean:1488`
- `drain_all_floor_two_to_fresh_uniform_unique`:
  `SSExactMajority/Convergence/LogTreeReset.lean:3466`
- `all_fresh_uniform_unique_from_log_seed`:
  `SSExactMajority/Convergence/LogTreeReset.lean:3571`
- `log_seed_uniform_leader_to_FreshRankingStart_resAns_noPhi_log`:
  `SSExactMajority/Convergence/LogRegimeConvergence.lean:166`

Exact fuel constant landed:

- `2 * Nat.clog 2 n + 2`

Breakdown:

- `Nat.clog 2 n` fuel spent by balanced-tree growth.
- `Nat.clog 2 n` fuel reserved for the fueled `.L`/`.L` leader tournament.
- `2` fuel reserved for the final mutual drain to fresh resetcount zero.

Final log theorem carrier status:

- The new final theorem
  `log_seed_uniform_leader_to_FreshRankingStart_resAns_noPhi_log` has no
  `n <= Dmax`, no `n <= Rmax`, and no `n <= Emax` hypothesis.
- Remaining parameter hypotheses are constant/clog-level:
  `[Inhabited (Fin n x Fin n)]`, `4 <= n`, `1 < Dmax`, `0 < Rmax`,
  seed role Resetting, seed fuel
  `2 * Nat.clog 2 n + 2 <= resetcount`, seed leader `.L`, and the faithful
  invariant that already-Resetting agents carry `majorityAnswer C`.
- The old compatibility theorem with `hDmax_n` remains in the file, but the
  new `_log` theorem routes through the fresh bridge
  `fresh_uniform_unique_to_FreshRankingStart_resAns_noPhi` and does not use
  the old positive-resetcount drain path.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake build SSExactMajority.Convergence.LogRegimeConvergence
/data/home/xhuan5/.elan/bin/lake env lean SSExactMajority/Convergence/LogTreeReset.lean
/data/home/xhuan5/.elan/bin/lake env lean SSExactMajority/Convergence/LogRegimeConvergence.lean
grep -nE "sorry|axiom|native_decide" \
  SSExactMajority/Convergence/LogTreeReset.lean \
  SSExactMajority/Convergence/LogRegimeConvergence.lean
```

Result: build completed successfully; both single-file Lean checks exited with
no output; forbidden-token grep returned no matches.

## Final Wire Attempt: Strong Re-entry Landed, Final Theorem Blocked

Spec file executed:

- `HANDOFF/finalwire_spec.md`

New file:

- `SSExactMajority/Convergence/LogRegimeFinal.lean`

Compiled pieces landed:

- `CorrectResetSeedStrong`:
  `SSExactMajority/Convergence/LogRegimeFinal.lean:10`
- `CorrectResetSeedStrong.toCorrectResetSeed`:
  `SSExactMajority/Convergence/LogRegimeFinal.lean:22`
- `correct_reset_seed_strong_to_InSswap_ResAns_phi_zero_log`:
  `SSExactMajority/Convergence/LogRegimeFinal.lean:36`
- `MedCorrectLiveProducesStrongSeedOrProgress`:
  `SSExactMajority/Convergence/LogRegimeFinal.lean:119`
- `ReservoirCaseProducesStrongSeedOrProgress`:
  `SSExactMajority/Convergence/LogRegimeFinal.lean:136`
- `med_correct_live_InSswap_to_reservoir_entry_from_strong_seed_and_reentry_log`:
  `SSExactMajority/Convergence/LogRegimeFinal.lean:157`
- `reservoir_reset_leaf_from_strong_seed_and_reentry_log`:
  `SSExactMajority/Convergence/LogRegimeFinal.lean:194`
- `hMedCorrectExit_from_log_reentry_and_strong_seed_prefixes`:
  `SSExactMajority/Convergence/LogRegimeFinal.lean:241`

What this proves:

- The re-entry consumer formerly using
  `correct_reset_seed_to_InSswap_ResAns_phi_zero` is now re-derived for a
  strong seed carrying exact `resetcount = Rmax`.
- The strong seed route calls the proven answer-faithful log bridge
  `log_seed_uniform_leader_to_FreshRankingStart_resAns_noPhi_log`
  (`SSExactMajority/Convergence/LogRegimeConvergence.lean:166`), then reuses
  the existing fresh-ranking-to-swap chain.
- The resulting re-entry hypotheses are clog/constant-level:
  `[Inhabited (Fin n x Fin n)]`, `4 <= n`, `1 < Dmax`, `0 < Rmax`,
  `2 * Nat.clog 2 n + 2 <= Rmax`, plus the two strengthened seed-prefix
  obligations.

STOP point:

- I did not produce `burmanConvergence_concrete_log` or
  `P_EM_solves_SSEM_log`.
- The remaining carrier is the ranking-side bad-ranking reset recovery, not
  the answer-faithful epidemic re-entry.
- The old reset recovery is `step_reset_snapshot_to_RankingEndpoint`
  (`SSExactMajority/Convergence/BurmanProof.lean:11529`), through
  `reset_snapshot_to_RankingEndpoint`
  (`SSExactMajority/Convergence/BurmanProof.lean:11468`). Its public snapshot
  hypothesis gives only `role = Resetting`, `resetcount = Rmax`, and
  `leader = .L` (`BurmanProof.lean:11534-11542`); it gives no answer
  invariant.
- The available `_log` bridge is answer-faithful and requires
  `forall w, role Resetting -> answer = majorityAnswer C`
  (`LogRegimeConvergence.lean:176-178`). Therefore it cannot discharge the
  ranking-side reset snapshot directly.
- The unconditional log endpoint
  `all_fresh_from_log_seed_unconditional`
  (`SSExactMajority/Convergence/LogTreeReset.lean:3761`) gives all fresh
  Resetting agents but does not give the unique leader needed by
  `IsDormantConfig`/`dormant_to_RankingEndpoint`
  (`SSExactMajority/Convergence/BurmanProof.lean:11368`).
- The unique-leader log endpoint currently available,
  `all_fresh_uniform_unique_from_log_seed`
  (`SSExactMajority/Convergence/LogTreeReset.lean:3571`), is also
  answer-coupled and cannot be used for the answer-agnostic ranking recovery.

Required missing layer for the final wire:

- A no-answer log reset recovery endpoint:
  growth preserving a root `.L`, fueled leader tournament, and final drain
  preserving unique leader, ending in all fresh Resetting + unique leader.
- Then reroute `reset_snapshot_to_RankingEndpoint`,
  `step_reset_snapshot_to_RankingEndpoint`, and the parity bad-ranking
  handlers through that endpoint before assembling the final convergence
  record.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake env lean SSExactMajority/Convergence/LogRegimeFinal.lean
/data/home/xhuan5/.elan/bin/lake build SSExactMajority.Convergence.LogRegimeFinal
grep -nE "sorry|axiom|native_decide" SSExactMajority/Convergence/LogRegimeFinal.lean
```

Result: both Lean checks completed successfully; the forbidden-token grep
returned no matches. The build output contains only pre-existing linter
warnings from imported files.

## No-Answer Final Status (supersedes previous STOP)

Spec file executed:

- `HANDOFF/noanswer_spec.md`

Landed no-answer endpoint and clog-level reset recovery:

- `SSEM.all_fresh_unique_from_log_seed_no_answer`
  (`SSExactMajority/Convergence/LogTreeReset.lean:4581`)
- `SSEM.reset_snapshot_to_RankingEndpoint_log`
  (`SSExactMajority/Convergence/LogRegimeFinal.lean:66`)
- `SSEM.step_reset_snapshot_to_RankingEndpoint_log`
  (`SSExactMajority/Convergence/LogRegimeFinal.lean:101`)
- `SSEM.BadRankingStart_even_to_RankingEndpoint_log`
  (`SSExactMajority/Convergence/LogRegimeFinal.lean:573`)
- `SSEM.BadRankingStart_odd_to_RankingEndpoint_log`
  (`SSExactMajority/Convergence/LogRegimeFinal.lean:866`)
- `SSEM.ranking_of_no_reset_by_parity_log`
  (`SSExactMajority/Convergence/LogRegimeFinal.lean:1102`)

Complete landed hypothesis list:

- For `all_fresh_unique_from_log_seed_no_answer`:
  `[Inhabited (Fin n x Fin n)]`, `hn : 0 < n`, `hDmax : 1 < Dmax`,
  `hn2 : 2 <= n`, seed role `Resetting`,
  `2 * Nat.clog 2 n + 2 <= seed.resetcount`, and seed leader `.L`.
- For `reset_snapshot_to_RankingEndpoint_log`,
  `step_reset_snapshot_to_RankingEndpoint_log`,
  `BadRankingStart_even_to_RankingEndpoint_log`,
  `BadRankingStart_odd_to_RankingEndpoint_log`, and
  `ranking_of_no_reset_by_parity_log`:
  `[Inhabited (Fin n x Fin n)]`, `hn : 0 < n`, `hn4 : 4 <= n`,
  `hDmax1 : 1 < Dmax`, and
  `hRlog : 2 * Nat.clog 2 n + 2 <= Rmax`.

Strong seed-prefix obligations:

- The bad-ranking snapshot path preserves the needed strong seed facts
  (`resetcount = Rmax`, `leader = .L`) and is now routed through
  `step_reset_snapshot_to_RankingEndpoint_log`.
- The fact is still lost in the arbitrary-resetting entry carrier used by the
  top-level convergence record:
  `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:2192`
  `reach_known_entry_from_any`, via
  `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:2168`
  `resetting_exists_to_known_entry` and
  `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:2042`
  `partial_resetting_to_known_entry`.
- The all-Resetting dispatch can enter
  `SSExactMajority/Convergence/BurmanProof.lean:15115`
  `ranking_from_all_resetting`, including the no-leader branch
  `SSExactMajority/Convergence/BurmanProof.lean:14611` and the mixed
  low-resetcount branch
  `SSExactMajority/Convergence/BurmanProof.lean:15037`.

Final assembly status:

- `burmanConvergence_concrete_log`: not produced.
- `P_EM_solves_SSEM_log`: not produced.
- Reason: `BurmanConvergence.ranking` is for arbitrary configurations. If an
  initial/current configuration already contains `Resetting` agents, the
  existing entry chain may normalize from arbitrary all-Resetting states with
  no leader, non-unique leaders, or low resetcounts. That is genuinely different
  from the bad-ranking snapshot and does not provide the strong seed
  precondition required by the clog-level endpoint.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake env lean SSExactMajority/Convergence/LogTreeReset.lean
/data/home/xhuan5/.elan/bin/lake env lean SSExactMajority/Convergence/LogRegimeFinal.lean
/data/home/xhuan5/.elan/bin/lake build SSExactMajority.Convergence.LogRegimeFinal
grep -nE '\bsorry\b|\baxiom\b' SSExactMajority/Convergence/LogTreeReset.lean SSExactMajority/Convergence/LogRegimeFinal.lean
```

Result: all target checks completed successfully; the forbidden-token grep
returned no matches. The build output contains only existing linter warnings.

## Latest: Endpoint Strong-Seed Time Windows

This is the endpoint-spec completion entry. Full details are in the
`Endpoint Strong-Seed Time Windows` section above.

- New file: `SSExactMajority/UpperBound/Time/LogWindows.lean`
- Final theorem:
  `SSEM.PEM_expectedParallelTime_On_faithful_log`
  at `SSExactMajority/UpperBound/Time/LogWindows.lean:2743`
- Final counter hypotheses: no `n <= Rmax`, no `n <= Emax`, no `n <= Dmax`.
  Only `hRlog : 2 * Nat.clog 2 n + 2 <= Rmax` and the genuine budget
  `d <= Dmax` inside `CRSReset12FaithfulStrong.wakeBudget_le_Dmax`.
- Verification:
  `/data/home/xhuan5/.elan/bin/lake env lean SSExactMajority/UpperBound/Time/LogWindows.lean --json`
  and
  `/data/home/xhuan5/.elan/bin/lake build SSExactMajority.UpperBound.Time.LogWindows`
  both completed successfully.
- Actual command-form scan for `sorry`, `axiom`, and `native_decide` in the
  touched source files is empty.

## Producer Spec Status

Spec file executed:

- `HANDOFF/producer_spec.md`

Landed strong producer layer:

- `SSEM.medCorrectLiveProducesStrongSeedOrProgress_holds`
  (`SSExactMajority/Convergence/LogRegimeFinal.lean:3179`)
- `SSEM.reservoirCaseProducesStrongSeedOrProgress_holds`
  (`SSExactMajority/Convergence/LogRegimeFinal.lean:3865`)

Seed witness tracking:

- All direct seed creation branches end at the reset step with
  `resetcount = Rmax` and `leader = .L`.
- Branches with timer descent/no-reset steps do those steps before seed
  creation, then tail-call the strong seed constructor. The final endpoint
  still has the fresh `Rmax` witness.
- No seed-producing schedule continues past seed creation while touching or
  decrementing the created seed. No `Rmax-k` shift is required.

Final theorems:

- `SSEM.burmanConvergence_concrete_log`
  (`SSExactMajority/Convergence/LogRegimeFinal.lean:4117`)
- `SSEM.P_EM_solves_SSEM_log`
  (`SSExactMajority/Convergence/LogRegimeFinal.lean:4134`)

Complete final hypothesis list:

- `[Inhabited (Fin n x Fin n)]`
- `hn : 0 < n`
- `hn4 : 4 <= n`
- `hDmax1 : 1 < Dmax`
- `hRlog : 2 * Nat.clog 2 n + 2 <= Rmax`

No `n <= Emax`, no `n <= Dmax`, no `n <= Rmax`, and no remaining strong
producer assumptions are needed by the final `P_EM_solves_SSEM_log`.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake env lean SSExactMajority/Convergence/LogRegimeFinal.lean
/data/home/xhuan5/.elan/bin/lake build SSExactMajority.Convergence.LogRegimeFinal
grep -nE '\bsorry\b|\baxiom\b|native_decide' SSExactMajority/Convergence/LogRegimeFinal.lean
```

Result: the target build completed successfully, and the forbidden-token grep
returned no matches.

## Time-Side Window Classification

Spec file executed:

- `HANDOFF/timeside_spec.md`

STOP status:

- No `SSExactMajority/UpperBound/Time/LogWindows.lean` was created.
- `PEM_expectedParallelTime_On_faithful_log` was not landed.
- Reason: there is a genuine-LARGE `hRmax : n <= Rmax` consumption in the
  probabilistic MAC-live/timer-drain window. The proof turns a one-step reset
  event, which resets only the selected pair, into the old `CorrectResetSeed`
  endpoint. That old endpoint requires
  `nonResettingCount C < (C r).1.resetcount`; immediately after a two-agent
  reset event the proof only has `nonResettingCount C <= n - 2` and
  `resetcount = Rmax`, so it needs `n - 2 < Rmax`. This is not an artifact at
  log-sized `Rmax`.

Classification table:

| File:line | Consumer | Hypothesis | Class | Reason |
| --- | --- | --- | --- | --- |
| `SSExactMajority/UpperBound/Time/GenericKeystone.lean:673` | `generic_MAClive_to_consensus_or_crs_window` | `hRmax` | genuine-LARGE | Routes to timer-drain and reset-trigger seed creation; old `CorrectResetSeed` needs `nonResettingCount < Rmax`. |
| `SSExactMajority/UpperBound/Time/GenericKeystone.lean:673` | same | `hEmax`, `hDmax` | artifact | Passed through this wrapper, but the real downstream uses in this chain are underscore/unused or structural transition parameters, not `n <= _`. |
| `SSExactMajority/UpperBound/Time/GenericKeystone.lean:723` | `generic_decision_before_timer_zero` | `hRmax`, `hEmax`, `hDmax` | artifact | Routes to the short35 tail theorem whose linear counter hypotheses are underscore/unused; the tail proof depends on the event-count bound and `35`, not `n <= Rmax/Emax/Dmax`. |
| `SSExactMajority/UpperBound/Time/GenericTrank.lean:630` | `generic_crs_of_InSswap_break_with_MedC` | `hRmax` | genuine-LARGE | Coupled CRS break proof constructs old `CorrectResetSeed`; bottom proofs use `nonResettingCount <= n - 2 < Rmax`. |
| `SSExactMajority/UpperBound/Time/GenericTrank.lean:713` | `generic_PEM_srank_or_timer_failure_prob_le_quarter_short35` | `hRmax`, `hEmax`, `hDmax` | artifact | Coupled theorem at `Time.lean:8584` names them `_hRmax/_hEmax/_hDmax`; tail theorem at `Time.lean:7259` has no counter lower-bound parameters. |
| `SSExactMajority/UpperBound/Time/GenericTrank.lean:1458` | `generic_decision_before_timer_zero` | `hRmax`, `hEmax`, `hDmax` | artifact | Only used through the short35 failure tail above. |
| `SSExactMajority/UpperBound/Time/GenericTrank.lean:1513` | `generic_timer_ge_two_descent_step` | `hRmax` | genuine-LARGE | In the `InSswap` break branch it calls `generic_crs_of_InSswap_break_with_MedC`, which needs the old CRS counting inequality. |
| `SSExactMajority/UpperBound/Time/GenericTrank.lean:1543` | `generic_PEM_expected_timer_drain_poly` | `hRmax` | genuine-LARGE | Uses `PEM_expected_timer_drain_poly`, whose descent witness calls the CRS break lemma. |
| `SSExactMajority/UpperBound/Time/GenericTrank.lean:1592` | `generic_timer_drain_window` | `hRmax` | genuine-LARGE | Markov window wrapper around the expected timer-drain theorem. |
| `SSExactMajority/UpperBound/Time/GenericTrank.lean:1614` | `generic_timer_drain_to_zero_productive` | `hRmax` | genuine-LARGE | Uses CRS break at `:1680` and `:1772`, and timer-one seed creation at `:1780`. |
| `SSExactMajority/UpperBound/Time/GenericTrank.lean:1868` | `generic_PEM_expected_reset_trigger_v2` | `hRmax` | genuine-LARGE | One-step reset-trigger branch at `:1943` calls `step_timer_zero_median_wrong_nonupper_creates_CorrectResetSeed`; same old CRS count. |
| `SSExactMajority/UpperBound/Time/GenericTrank.lean:1868` | same | `hEmax`, `hDmax` | artifact | The theorem binds them as `_hEmax/_hDmax`; no `n <= Emax/Dmax` counting use in this proof. |
| `SSExactMajority/UpperBound/Time/GenericTrank.lean:2147` | `generic_MAClive_to_consensus_or_crs` | `hRmax` | genuine-LARGE | Composes timer-drain-to-zero and reset-trigger-v2, both blocked by old CRS counting. |
| `SSExactMajority/UpperBound/Time/GenericTrank.lean:2147` | same | `hEmax`, `hDmax` | artifact | Passed only to the blocked sublemmas; no real linear `Emax/Dmax` consumption found. |
| `SSExactMajority/UpperBound/Time/GenericTrank.lean:2224` | `generic_MAClive_to_consensus_or_crs_window` | `hRmax` | genuine-LARGE | Markov window wrapper around `generic_MAClive_to_consensus_or_crs`. |
| `SSExactMajority/UpperBound/Time/GenericTrank.lean:2224` | same | `hEmax`, `hDmax` | artifact | Pass-through only. |
| `SSExactMajority/UpperBound/Time/GenericTrank.lean:2251` | `generic_swap_live_to_cons_or_crs_or_break` | `hRmax` | genuine-LARGE | Its live branches call `generic_timer_drain_window`; same old CRS endpoint. |
| `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:179` | `PEM_expectedParallelTime_On_faithful` | `hRmax` | genuine-LARGE | Passed to `PEM_expectedParallelTime_On`, which reaches the generic MAC-live window above. |
| `SSExactMajority/UpperBound/Time/OptimalWindowsFaithful.lean:179` | same | `hEmax`, `hDmax` | artifact for the linear `n <= _` assumptions | The faithful drain side already uses `d <= Dmax` through `CRSReset12Faithful.wakeBudget_le_Dmax`; the extra `n <= Dmax` and all of `n <= Emax` are not real counting needs in the traced window chain. |

Bottom counting sites for the genuine-LARGE `hRmax`:

- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:13787`:
  old `CorrectResetSeed` requires
  `nonResettingCount C < (C r).1.resetcount`.
- `SSExactMajority/UpperBound/Time/CRSEven.lean:71` and `:124`:
  even CRS constructors derive `nonResettingCount <= n - 2`, then use
  `n <= Rmax` to prove `nonResettingCount < Rmax`.
- `SSExactMajority/UpperBound/Time/CRSOdd.lean:53` and `:137`:
  odd CRS constructors use the same `n - 2 < Rmax` counting step.
- `SSExactMajority/UpperBound/Time/CRSEvenTimerPos.lean:10`:
  timer-one median/max reset constructors use the same two-reset-agent
  counting step at `:77`, `:118`, `:163`, and `:203`.
- `SSExactMajority/UpperBound/Time/HeavyProofs.lean:285`:
  timer-zero wrong-answer reset constructors use the same count at `:347`
  and `:390`.
- `SSExactMajority/UpperBound/Time/PolynomialBound.lean:50` and `:151`:
  timer-drain expected-time proof inherits the CRS break counting through
  `timer_ge_two_descent_step` and `PEM_expected_timer_drain_poly`.

Conclusion:

- `hEmax : n <= Emax` is artifact in the traced time-side window chain.
- `hDmax : n <= Dmax` is artifact as a linear assumption in this chain; the
  separate faithful drain budget `d <= Dmax` remains genuine-small-OK.
- `hRmax : n <= Rmax` is genuine-LARGE for the old `CorrectResetSeed`
  endpoint. Eliminating it requires changing the probabilistic renewal event
  from old `CorrectResetSeed` to a log-compatible strong/fresh reset endpoint,
  not merely weakening the existing hypotheses.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake build SSExactMajority.UpperBound.Time.GenericKeystone
```

Result: build completed successfully. Output contains existing linter warnings
only.

## Entry Spec Status

Spec file executed:

- `HANDOFF/entry_spec.md`

Mapped old `n <=` consumptions:

- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:2042-2154`
  (`partial_resetting_to_known_entry`): `n <= Dmax` is used only to get
  `1 < Dmax`; `n <= Rmax` is used in the seed escape through the old
  `all_resetting_from_seed_aux`; `n <= Emax` is pass-through.
- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:2168-2188`
  (`resetting_exists_to_known_entry`): all three bounds are pass-through to
  `partial_resetting_to_known_entry`.
- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:2192-2217`
  (`reach_known_entry_from_any`): the bounds are pass-through to
  `phase1_trigger_reset_or_InSrank` and the old resetting entry carrier.
- `SSExactMajority/Convergence/BurmanProof.lean:7253-7594`
  (`drain_positive_except_anchor_to_zero`,
  `drain_positive_except_anchor_to_all_zero`,
  `all_resetting_pos_with_leader_to_dormant`): `n <= Dmax` is consumed only
  by the anchor-budget proof at lines 7385, 7523, and 7590.
  The log entry proof avoids this path by pair-draining positive-resetcount
  agents and using the no-answer log reset endpoint for seed cases.
- No genuine statement-level need for `n <= Emax`, `n <= Dmax`, or
  `n <= Rmax` was found in the arbitrary-entry ranking stack.

Landed clog-level arbitrary-entry ranking stack in
`SSExactMajority/Convergence/LogRegimeFinal.lean`:

- `SSEM.ranking_from_all_resetting_log`
  (`SSExactMajority/Convergence/LogRegimeFinal.lean:1994`)
- `SSEM.partial_resetting_to_ranking_goal_log`
  (`SSExactMajority/Convergence/LogRegimeFinal.lean:2139`)
- `SSEM.resetting_exists_to_ranking_goal_log`
  (`SSExactMajority/Convergence/LogRegimeFinal.lean:2282`)
- `SSEM.ranking_field_proof_log`
  (`SSExactMajority/Convergence/LogRegimeFinal.lean:2305`)

Landed final assembly skeleton:

- `SSEM.burmanConvergence_concrete_log_with_strong_seed_prefixes`
  (`SSExactMajority/Convergence/LogRegimeFinal.lean:2570`)
- `SSEM.P_EM_solves_SSEM_log_with_strong_seed_prefixes`
  (`SSExactMajority/Convergence/LogRegimeFinal.lean:2654`)

Complete landed hypothesis list for the assembly skeleton:

- `[Inhabited (Fin n x Fin n)]`
- `hn : 0 < n`
- `hn4 : 4 <= n`
- `hDmax1 : 1 < Dmax`
- `hRlog : 2 * Nat.clog 2 n + 2 <= Rmax`
- `hEntrySeed :
  MedCorrectLiveProducesStrongSeedOrProgress Rmax Emax Dmax hn`
- `hLeafSeed :
  ReservoirCaseProducesStrongSeedOrProgress Rmax Emax Dmax hn`

Where the strong seed fact is still lost:

- The protocol-level collision facts expose exact strong seeds locally:
  `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:395`,
  `:646`, and `:741` give `resetcount = Rmax` and `leader = .L`.
- The public producer interface erases that exact fact:
  `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:15102`
  defines `MedCorrectLiveProducesCorrectSeedOrProgress` with only
  `CorrectResetSeed C'`; `:15224` proves `med_correct_live_seed_or_progress`
  with that weak result.
- The reset-leaf producer has the same erasure:
  `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:15814`
  defines `ReservoirCaseProducesCorrectSeedOrProgress` with only
  `CorrectResetSeed C'`; `:15832` proves
  `reservoir_case_seed_or_progress` with that weak result.
- The old re-entry consumers at
  `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:15776`
  and `:15864` then route weak `CorrectResetSeed` through the old
  `correct_reset_seed_to_InSswap_ResAns_phi_zero`, which is exactly the
  `n <= Dmax`/`n <= Rmax` path being replaced.

Final assembly status:

- `burmanConvergence_concrete_log`: not produced under the requested
  constants+clog-only hypothesis list.
- `P_EM_solves_SSEM_log`: not produced under the requested
  constants+clog-only hypothesis list.
- Reason: the arbitrary-entry ranking stack is now clog-only, but the
  answer-faithful epidemic/re-entry side still needs the two strong producer
  obligations above. Those obligations cannot be derived from the existing
  public producer theorems because they expose only weak `CorrectResetSeed`
  and drop the `resetcount = Rmax` witness. Discharging them requires
  strengthening/duplicating the seed-producing producer layer, not another
  entry-stack counting argument.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake env lean SSExactMajority/Convergence/LogRegimeFinal.lean
/data/home/xhuan5/.elan/bin/lake build SSExactMajority.Convergence.LogRegimeFinal
grep -nE '\bsorry\b|\baxiom\b|native_decide' SSExactMajority/Convergence/LogRegimeFinal.lean
```

Result: all target checks completed successfully; the forbidden-token grep
returned no matches. The build output contains only existing linter warnings.

## Trank Spec Status

Spec file executed:

- `HANDOFF/trank_spec.md`

Mechanism audit:

- `SSExactMajority/Protocol/Transition.lean:32-62`:
  `trank` enters `transitionPEM_prePhase4` only through the Settled median
  timer initialization `timer := 7 * (trank + 4)`.
- `SSExactMajority/Protocol/Transition.lean:98-124`:
  `transitionPEM_phase4` is parameterized only by `Rmax`; reset creation,
  resetcount, answer propagation, and delay/reset machinery do not mention
  `trank`.
- `SSExactMajority/Convergence/BurmanProof.lean:130`:
  the only explicit correctness-side timer-init lower-bound lemma found is
  `timer_init_ge_2`, proving the constant lower bound `2 <= 7*(trank+4)`.
- Searches over `LogTreeReset`, `LogRegimeConvergence`,
  `LogRegimeFinal`, `BurmanConvergenceFinal`, and `BurmanProof` found no
  correctness-side proof obligation of the form `timer >= f(n)` coming from
  `trank`. The ranking/swap/decision consumers use median timer lower bounds
  `2` and `1`.

Where the unification is blocked:

- `SSExactMajority/Convergence/LogRegimeFinal.lean:2337`:
  `ranking_field_proof_log` is stated only for
  `protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)`.
- `SSExactMajority/Convergence/LogRegimeFinal.lean:4015-4148`:
  the final log correctness assembly builds
  `BurmanConvergence Rmax Rmax ...` and
  `SolvesSSEM (protocolPEM n Rmax Rmax ...) n`; there is no generic
  `trank` variant to instantiate at `1`.
- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:13266-13666`:
  the fresh-start-to-ranking wrappers and heap-prefix recruit induction are
  also stated over `protocolPEM n Rmax Rmax ...`.
- `SSExactMajority/Convergence/LogRegimeFinal.lean:2448-2483`:
  the strong producer interfaces quantify `runPairs` over the coupled
  protocol, so the re-entry side cannot be reused directly for `trank = 1`.
- `SSExactMajority/UpperBound/Time/GenericTrank.lean:302`:
  existing `generic_step_eq_coupled_of_InSrank` transfers steps only once the
  configuration is already `InSrank`; it is sufficient for settled
  swap/decision segments but does not cover the reset/recruit/ranking entry
  stack where the public theorems are hardcoded.

Conclusion:

- I did not land `P_EM_solves_SSEM_log_trank1`.
- I found no genuine mechanism-level need for `timer >= f(n)` or
  `trank = Rmax`; the remaining gap is a proof-interface gap: the log
  correctness stack must expose generic/trank1 versions of the reset/recruit
  ranking entry and strong producer interfaces before the final
  `BurmanConvergence 1 Rmax ...` instance can be assembled without
  `sorry`/`axiom`.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake env lean SSExactMajority/Convergence/LogRegimeFinal.lean --json
```

Result: completed successfully; existing warnings only.
