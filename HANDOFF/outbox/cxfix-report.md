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
