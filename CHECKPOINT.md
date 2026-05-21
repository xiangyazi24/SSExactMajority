# SSExactMajority — Checkpoint

Formalizing: Kanaya–Eguchi–Sasada–Ooshita–Inoue (2025),
"Time- and Space-Optimal Silent Self-Stabilizing Exact Majority
in Population Protocols" (arXiv:2503.17652, SSS 2025).

## Current state (2026-05-18)

**Build status: ✓ zero errors, ✓ zero `sorry`, ✓ zero custom axioms.**

- Root library (`lake build`): clean.
- Composition modules (`BurmanProof`, `BurmanConvergenceFinal`,
  `EndpointRepair`): build clean via
  `lake build SSExactMajority.Convergence.{BurmanProof,BurmanConvergenceFinal,EndpointRepair}`.
- **Ultimate theorem**: `SSEM.P_EM_solves_SSEM_final`
  (`Convergence/BurmanConvergenceFinal.lean:16052`).  Depends only on
  `[propext, Classical.choice, Quot.sound]`.

### Discharged hypotheses (formerly external)

| Historical hypothesis | Now |
|-----------------------|-----|
| `h_burman_ranking` (Burman 2021 PODC ranking) | proved: `ranking_field_proof` |
| `BurmanMacroDecision` (median-correct macro step) | proved: `med_correct_live_seed_or_progress` + `reservoir_case_seed_or_progress` chain |
| `hStrictMajority` (even-n decision pair) | absorbed into the disjunctive seed-or-progress shape (tie-aware) |
| `h_inv_swap` / `h_inv_dec` (timer ≥ 2 / ≥ 1 invariants) | proved: `SwapInv` disjunction (`InSrank_to_InSswap_ResAns_with_inv`) |

### Removed files

- `OddRecruitDriver.lean` — bypassed by `EndpointRepair.lean`
  (`d1d54a94 EndpointRepair: switch to endpoint-repair approach (bypasses
  OddRecruitDriver)`); deleted in `a186ac78` after audit.

### What is NOT done

The qualitative (correctness + termination) half of the paper is complete.
The quantitative (parallel-time complexity) half is not formalized:

- **Theorem 3 — Ω(n log n) expected parallel time lower bound**: scaffold
  in `LowerBound/Time.lean`.
- **§5.2 quantitative — O(n log n) expected parallel time upper bound**:
  scaffold in `UpperBound/Time.lean`.
- **Probability framework** (`Probability/RandomScheduler.lean`,
  `Probability/ExpectedTime.lean`): scaffold only.

Design plan: `docs/TIME_BOUND_PLAN.md`.

---

## Historical (pre-2026-05-18) notes follow

The original "remaining sorry's (2026-05-10)" block has since been fully
discharged; the items listed below were the gap snapshot at that date:

1. `unsettled_one_step_progress` — protocol trace: rankDeltaOSSR Part 3/4 case split
2. `phase3a_to_awakening` — multi-step countdown (needs 0<Rmax, 0<Dmax)
3. `heapPrefix_recruit_step` — recruitment trace + Phase 4 timer safety
4. `burmanConvergence_concrete` — master composition (depends on above + API threading)

### Key proven lemmas (this session)

- `HeapPrefix.to_InSrank` — Fintype injective→surjective
- `phase3bc_from_awakening` — full inductive sweep (zero sorry)
- `phase2_propagate_reset` — full induction on non-Resetting count
- `phase4_binary_tree` — HeapPrefix induction (depends on #3)
- `propagate_reset_one_step` + `_spreader_state` — single-step spread traces
- `rankDeltaOSSR_both_dormant` + `_settled_meets_dormant` — dormant agent traces
- `transitionPEM_both_dormant_role` + `_settled_meets_dormant_role` — full PEM wrap

## File structure

```
SSExactMajority/
├── Defs/
│   ├── Protocol.lean       — Protocol record (δ, π_out), Opinion, Output types
│   ├── Config.lean         — Configuration, step, silent, allOutput, agentsWithInput
│   ├── Execution.lean      — DetScheduler, execution, isOutputStable, ExactMajoritySafe', SolvesSSEM
│   └── ExactMajority.lean  — majorityOpinion helper
├── Embed.lean              — Execution embedding lemma (step commutes with injective embedding)
├── Impossibility/
│   └── WithoutN.lean       — Theorem 1: impossibility without knowledge of n
├── LowerBound/
│   ├── Space.lean          — Lemmas 4/4B/5 + Theorem 2: Ω(n) state lower bound
│   └── Time.lean           — Theorem 3 stub (Ω(n log n) time, needs probability framework)
├── Protocol/
│   ├── State.lean          — AgentState n: Role, Leader, Answer, rank, timer, resetcount,
│   │                          children, errorcount, delaytimer (Burman fields)
│   ├── Transition.lean     — transitionPEM: full Algorithm 1 encoding (4 phases)
│   ├── Correctness.lean    — Structural lemmas: Fintype instances, output/ceilHalf properties
│   └── RankDelta.lean      — **Concrete rankDelta**: OPTIMAL-SILENT-SSR (Protocol 3,
│                              Burman et al. PODC 2021), including PROPAGATE-RESET
│                              (Protocol 2), RESET (Protocol 4), binary-tree ranking,
│                              collision detection, error monitoring
└── Convergence/
    ├── Silent.lean              — IsConsensusConfig predicate, RankDeltaSettledFix
                                     hypothesis, majorityAnswer, allOutput /
                                     ExactMajoritySafe' at consensus
    ├── AnswerPreservation.lean  — transitionPEM preserves .answer at any
                                     consensus pair (full case bash)
    ├── StatePreservation.lean   — transitionPEM preserves .role and .rank;
                                     reset branches discharged by answer-equality
    ├── Step.lean                — step / execution preserve IsConsensusConfig;
                                     consensus ⟹ isOutputStable
    ├── Theorem4.lean            — conditional Theorem 4: P_EM solves SSEM
                                     (assuming consensus is reachable)
    ├── Sets.lean                — configuration set hierarchy
                                     (Srank/Sswap/Sout/Stim/Sem),
                                     Stim ↔ IsConsensusConfig, exists_median
    ├── Schedule.lean            — scheduler composition (concatScheduler,
                                     execution_concat, reachable_compose)
    ├── Composition.lean         — hReach_of_phases: chain ranking/swap/decision
                                     reachability into the consensus-reachability
                                     hypothesis used by `Theorem4`
    ├── SwapPhase.lean           — misorderedCount potential function;
                                     Srank ∧ count = 0 ↔ Sswap (counting argument
                                     via the rank bijection)
    ├── PotentialReach.lean      — generic reach_zero_potential: lift a
                                     single-step decreasing-potential lemma to
                                     global scheduler-existence
    ├── SwapReach.lean           — `swap_reaches_Sswap_of_singleStep`:
                                     hSwapPhase modulo a single-step lemma
    ├── DecisionReach.lean       — `wrongAnswerCount` potential;
                                     `decision_reaches_consensus_of_singleStep`:
                                     hDecisionPhase modulo a single-step lemma
    └── SwapStep.lean            — `swap_step_non_median_decreases`: full
                                     single-step lemma at any non-median
                                     misorder pair (preserves InSrank +
                                     count strictly decreases);
                                     `swap_reaches_Sswap_via_non_median`:
                                     end-to-end swap reachability modulo
                                     "non-median misorder exists" hypothesis
```

## Proved theorems

### Lower bounds (fully proved)

| Theorem | File | Description |
|---------|------|-------------|
| `execution_input_preserved` | Embed.lean | Inputs immutable through execution |
| `Config.step_embed` | Embed.lean | Step commutes with injective embedding |
| `execution_embed` | Embed.lean | Execution embedding (matching lemma) |
| `impossibility_without_n` | WithoutN.lean | No protocol solves SSEM for all n (Theorem 1) |
| `execution_of_silent` | Space.lean | Silent config ⟹ execution stays put |
| `silent_config_A_agents_distinct` | Space.lean | A-agents have distinct states (Lemma 4) |
| `silent_config_B_agents_distinct` | Space.lean | B-agents have distinct states (Lemma 4B) |
| `silent_config_AB_distinct` | Space.lean | A-agent ≠ B-agent states, input-oblivious (Lemma 5) |
| `space_lower_bound` | Space.lean | Silent SSEM protocol needs ≥ n states (Theorem 2) |

### Upper bound (Algorithm 1 encoding)

| Theorem | File | Description |
|---------|------|-------------|
| `opinionToAnswer_injective` | Correctness.lean | Opinion→Answer mapping is injective |
| `output_opinion_roundtrip` | Correctness.lean | opinionToAnswer ∘ toOutput matches opinion |
| `ceilHalf_even/odd` | Correctness.lean | ⌈n/2⌉ arithmetic |
| `outputPEM_eq_answer_toOutput` | Correctness.lean | Output determined by answer field |
| `allOutput_of_all_answer` | Correctness.lean | Uniform answer ⟹ uniform output |
| `rankDeltaOSSR` | RankDelta.lean | **Concrete ranking subprotocol** (Protocol 3, Burman PODC 2021) |
| `rankDeltaOSSR_settled_distinct_ranks` | RankDelta.lean | Identity on Settled pairs with distinct ranks |

### Consensus characterization (silent terminal)

| Theorem | File | Description |
|---------|------|-------------|
| `nAOf_add_nBOf` | Convergence/Silent.lean | A/B input counts partition the n agents |
| `IsConsensusConfig` | Convergence/Silent.lean | Predicate: settled, rank-bijective, sorted by input, answer-correct |
| `RankDeltaSettledFix` | Convergence/Silent.lean | Hypothesis: ranking subprotocol is identity on Settled pairs |
| `IsConsensusConfig.inputB_iff_rank_ge` | Convergence/Silent.lean | Equivalent characterization of B-inputs by rank |
| `IsConsensusConfig.swap_does_not_fire` | Convergence/Silent.lean | Swap precondition fails at consensus |
| `IsConsensusConfig.allOutput` | Convergence/Silent.lean | All outputs equal `(majorityAnswer C).toOutput` |
| `IsConsensusConfig.exactMajoritySafe` | Convergence/Silent.lean | Outputs match the input majority (Theorem 4 terminal half) |
| `transitionPEM_consensus_pair_answer` | AnswerPreservation.lean | transitionPEM preserves `.answer` at consensus pair |
| `transitionPEM_consensus_pair_answer_eq` | AnswerPreservation.lean | Stronger form: `.answer = a` post-transition |
| `transitionPEM_consensus_pair_role_rank` | StatePreservation.lean | transitionPEM preserves `.role` and `.rank` at consensus pair |
| `step_input_preserved` | Step.lean | `Config.step` preserves the input field |
| `nAOf_step_eq` / `majorityAnswer_step_eq` | Step.lean | A-count and majorityAnswer are step-invariants |
| `step_preserves_consensus` | Step.lean | `Config.step` preserves `IsConsensusConfig` |
| `execution_preserves_consensus` | Step.lean | execution preserves `IsConsensusConfig` (induction) |
| `IsConsensusConfig.isOutputStable` | Step.lean | a consensus configuration is output-stable |
| `P_EM_solves_SSEM_of_consensus_reachable` | Theorem4.lean | conditional Theorem 4: SolvesSSEM holds when consensus is reachable |

### Convergence chain (in progress)

| Theorem | File | Description |
|---------|------|-------------|
| `InSrank` / `InSswap` / `InSout` / `InStim` / `InSem` | Sets.lean | Configuration sets of Kanaya §5.2.1 |
| `InStim_iff_IsConsensusConfig` | Sets.lean | `InStim` is the same predicate as our `IsConsensusConfig` |
| `IsConsensusConfig.exists_median` | Sets.lean | A consensus config has an agent at the median rank |
| `concatScheduler` / `execution_concat` | Schedule.lean | Chain two schedulers at a step boundary |
| `reachable_compose` | Schedule.lean | Compose two reachability claims |
| `hReach_of_phases` | Composition.lean | Chain ranking/swap/decision reachability into hReach |
| `P_EM_solves_SSEM_via_phases` | Composition.lean | Closed-form Theorem 4 modulo the three phase reachabilities |
| `MisorderedPair` / `misorderedSet` / `misorderedCount` | SwapPhase.lean | Decidable potential function for the swap phase |
| `misorderedCount_eq_zero_iff` | SwapPhase.lean | Count vanishes iff no misordered pairs |
| `exists_misordered_of_pos_count` | SwapPhase.lean | Witness extraction from a positive count |
| `misorderedCount_eq_zero_of_InSswap` | SwapPhase.lean | Sswap ⟹ count = 0 |
| `InSswap_of_InSrank_of_count_zero` | SwapPhase.lean | Srank ∧ count = 0 ⟹ Sswap (via rank-bijection counting) |
| `reach_zero_potential` | PotentialReach.lean | Generic lift: single-step decrease ⟹ scheduler-existence |
| `swap_reaches_Sswap_of_singleStep` | SwapReach.lean | hSwapPhase reduced to a local single-step decrease lemma |
| `wrongAnswerCount` / `wrongAnswerCount_eq_zero_iff` | DecisionReach.lean | "Wrong answers" potential for the decision phase |
| `isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero` | DecisionReach.lean | Sswap ∧ wrongAnswerCount = 0 ⟹ consensus |
| `decision_reaches_consensus_of_singleStep` | DecisionReach.lean | hDecisionPhase reduced to a local single-step decrease lemma |
| `transitionPEM_at_misordered_non_median` | SwapStep.lean | At a non-median misorder pair, `transitionPEM` is precisely the state-swap |
| `step_at_misordered_non_median` | SwapStep.lean | Lifts to `Config.step` (state-swap at positions u, v) |
| `misorderedCount_decreases_at_non_median` | SwapStep.lean | The misorderedCount strictly decreases (Finset.card_lt_card) |
| `step_at_misordered_non_median_preserves_InSrank` | SwapStep.lean | InSrank preserved (transposition involution composition) |
| `swap_step_non_median_decreases` | SwapStep.lean | Full single-step lemma at a non-median misorder pair |
| `swap_reaches_Sswap_via_non_median` | SwapStep.lean | Swap-phase reachability modulo "non-median misorder exists" |
| `transitionPEM_at_misordered_u_median_odd_v_not_max` | RankPreservation.lean | Median-corner case (odd n, u at median, v not at max, timer ≥ 1): explicit transitionPEM result |
| `swap_step_decreases_at_misorder_u_median_odd_v_not_max` | RankPreservation.lean | Full single-step lemma at the odd-n median-corner case |
| `transitionPEM_at_misordered_u_lower_median_even` | RankPreservation.lean | Median-pair case (even n ≥ 4): both answers set to .outT, reset blocked |
| `swap_step_decreases_at_misorder_u_lower_median_even` | RankPreservation.lean | Full single-step lemma at the even-n median-pair case |
| `swap_step_decreases_non_median_or_median_corner` | RankPreservation.lean | **Unified** single-step at non-median ∨ odd-n median-corner-with-timer |
| `swap_step_decreases_three_way` | RankPreservation.lean | **Three-way** single-step: non-median ∨ odd-median-corner ∨ even-median-pair |
| `transitionPEM_at_misordered_u_median_odd_v_max` | RankPreservation.lean | Odd-n median-corner with v AT max rank, timer ≥ 2: explicit transitionPEM result |
| `swap_step_decreases_at_misorder_u_median_odd_v_max` | RankPreservation.lean | Single-step lemma at odd-n median-corner-with-v-max + timer ≥ 2 |
| `swap_step_decreases_four_way` | RankPreservation.lean | **Four-way** single-step: non-median ∨ odd-corner-no-max ∨ odd-corner-at-max ∨ even-pair |
| `swap_reaches_Sswap_via_unified` | RankPreservation.lean | Swap-phase reachability via the unified single-step |
| `swap_reaches_Sswap_via_three_way` | RankPreservation.lean | Swap-phase reachability via the three-way single-step |
| `swap_reaches_Sswap_via_four_way` | RankPreservation.lean | Swap-phase reachability via the four-way single-step |
| `P_EM_solves_SSEM_via_unified_swap_and_trivial_decision` | RankPreservation.lean | Theorem 4 corollary using unified swap + Sout-trivial decision |
| `P_EM_solves_SSEM_via_three_way_swap_and_trivial_decision` | RankPreservation.lean | Theorem 4 corollary using three-way swap + Sout-trivial decision |
| `P_EM_solves_SSEM_via_four_way_swap_and_trivial_decision` | RankPreservation.lean | Theorem 4 corollary using four-way swap + Sout-trivial decision |
| `transitionPEM_at_median_no_swap_odd_v_not_max` | DecisionReach.lean | Decision-step transitionPEM at median (odd n, no swap fires) |
| `step_at_median_no_swap_odd_v_not_max` | DecisionReach.lean | Lifted to Config.step (only median's answer is updated) |
| `opinionToAnswer_median_eq_majorityAnswer_odd` | DecisionReach.lean | Median's input matches majority side under InSswap (odd n) |
| `wrongAnswerCount_decreases_at_median_no_swap_odd` | DecisionReach.lean | wrongAnswerCount strictly decreases when median is wrong |
| `step_at_median_no_swap_odd_preserves_InSswap` | DecisionReach.lean | InSswap is preserved by the median no-swap step |
| `decision_step_at_median_no_swap_odd_decreases` | DecisionReach.lean | **Single-step decision lemma** when median is wrong |
| `decision_reaches_consensus_via_median_wrong_odd` | DecisionReach.lean | Decision-phase reachability via the median-wrong-decision single-step |
| `P_EM_solves_SSEM_via_four_way_and_median_wrong_decision` | DecisionReach.lean | Composite Theorem 4 corollary: four-way swap + median-wrong decision (odd n) |
| `medianAgent` / `medianTimer` | TimerDescent.lean | Median agent + its timer (via InSrank.exists_median + Classical.choose) |
| `medianTimer_decreases_at_misorder_median_v_max_odd` | TimerDescent.lean | Single-step timer descent (odd n, misorder, v at max, timer ≥ 2) |
| `reset_fires_at_misorder_median_v_max_odd_timer_zero` | ResetCycle.lean | Reset fires when timer = 0 + answers differ |
| `BurmanMacroDecision` | MasterModuloBurman.lean | Bundled Burman + reset-cycle macro-step hypothesis |
| `decision_reaches_consensus_full_odd` / `_even` | MasterModuloBurman.lean | Full decision-phase reachability modulo Burman |
| `P_EM_solves_SSEM_full_odd_modulo_burman` (D1) | MasterModuloBurman.lean | **Theorem 4 — odd n — modulo Burman** |
| `P_EM_solves_SSEM_full_even_modulo_burman` (D2) | MasterModuloBurman.lean | **Theorem 4 — even n — modulo Burman** |
| `P_EM_solves_SSEM_full_modulo_burman` (D3) | MasterModuloBurman.lean | **Theorem 4 — parity-combined — modulo Burman** |
| `oddCase_witness_when_median_wrong_with_timer` (E2 odd) | MedianWitnesses.lean | Discharge hOddCase witness for n ≥ 3 odd |
| `evenCase_witness_when_median_wrong` (E2 even) | MedianWitnesses.lean | Discharge hEvenCase witness for n ≥ 4 even, strict majority |
| `swap_step_decreases_at_misorder_v_median_odd` | SwapVMedian.lean | Mirror of u-at-median: v at median, odd n, timer ≥ 1 |
| `swap_step_exists_5way_odd_with_timer` (E1 odd) | MedianWitnesses.lean | 5-way swap-step existence under timer ≥ 2 (odd n only) |
| `swap_step_decreases_at_misorder_v_lower_median_even` | SwapVMedian.lean | Mirror for even n ≥ 4: v at lower median, timer ≥ 1 |
| `swap_step_decreases_six_way` | SwapVMedian.lean | **Most permissive** parity-combined single-step (6 disjuncts) |
| `swap_reaches_Sswap_via_six_way` | SwapVMedian.lean | Swap-phase reachability via 6-way single-step |
| `swap_step_decreases_at_misorder_u_lower_median_even_v_above` | SwapVMedian.lean | 7th: even n, u at lower median, v above upper (not max) |
| `swap_step_decreases_at_misorder_u_lower_median_even_v_max` | SwapVMedian.lean | 8th: even n, u at lower median, v at max, timer ≥ 2 |
| `swap_step_decreases_eight_way` | SwapVMedian.lean | **8-way unified** single-step (full coverage) |
| `swap_step_exists_8way_with_timer` | MedianWitnesses.lean | **Parity-combined 8-way existence** under timer invariant |
| `swap_reaches_Sswap_via_eight_way` | SwapVMedian.lean | Reachability lift via 8-way single-step |
| `swap_reaches_Sswap_via_8way_with_timer_invariant` | MedianWitnesses.lean | Composed: invariant → existence → reachability |
| `P_EM_solves_SSEM_fully_discharged_odd_modulo_burman` | MedianWitnesses.lean | **Maximally discharged Theorem 4 (odd n ≥ 4)** — only Burman + invariants remain |
| `opinionToAnswer_lower_median_eq_majorityAnswer_even` | DecisionReach.lean | Even-n strict majority: lower median's input matches majority side |
| `transitionPEM_at_median_pair_even_agreed_inputs` | DecisionReach.lean | Even-n median pair (n ≥ 4) with agreed inputs: explicit transitionPEM result |
| `step_at_median_pair_even_agreed_inputs` | DecisionReach.lean | Lifted to Config.step (both u, v's answers are updated) |
| `wrongAnswerCount_decreases_at_median_pair_even` | DecisionReach.lean | wrongAnswerCount strictly decreases when ≥ 1 of u, v was wrong |
| `InSswap.median_input_A` | TimerDescentNoSwap.lean | Median has input A when ceilHalf n ≤ nAOf |
| `InSswap.max_input_B` | TimerDescentNoSwap.lean | Max-rank agent has input B when nAOf < n |
| `step_at_median_max_no_swap_odd` | TimerDescentNoSwap.lean | No-swap step at (median, max): timer−1, answer set, rank/role preserved |
| `step_at_median_max_no_swap_odd_preserves_InSswap` | TimerDescentNoSwap.lean | InSswap preserved by the no-swap timer-descent step |
| `timer_decreases_at_median_max_no_swap_odd` | TimerDescentNoSwap.lean | Timer strictly decreases (timer + 1 = old timer) |
| `timer_descent_to_one` | TimerDescentNoSwap.lean | **Iteration**: timer T ≥ 2 → ≤ 1, InSswap preserved throughout |
| `step_at_median_timer_zero_reset_fires` | TimerDescentNoSwap.lean | Timer = 0 + wrong-answer partner → reset fires (both Resetting) |
| `step_at_median_max_timer_one_no_reset` | MacroStepComposition.lean | Timer = 1, max correct → timer = 0, InSswap preserved |
| `exists_wrong_non_median_non_max` | MacroStepComposition.lean | Wrong agent exists away from median and max positions |
| `BurmanRankingCorrect` | MacroStepComposition.lean | **New bundled hypothesis**: ranking + epidemic + swap convergence |
| `discharge_BurmanMacroDecision` | MacroStepComposition.lean | **BurmanMacroDecision discharged from BurmanRankingCorrect** |
| `majorityAnswer_eq_outT_of_tie` | DecisionTieCase.lean | Tie (nA = nB) implies majorityAnswer = .outT |
| `transitionPEM_at_median_pair_even_disagreed_inputs` | DecisionTieCase.lean | Transition at median pair with different inputs → both .outT |
| `decision_step_at_median_pair_even_tie_decreases` | DecisionTieCase.lean | **Tie-case decision step**: InSswap preserved + wrongAnswerCount decreases |
| `evenCase_witness_when_median_wrong_tie` | TieCaseWitness.lean | Tie-case witness: median pair with disagree inputs |
| `decision_reaches_consensus_full_even_no_strict_majority` | EvenNComplete.lean | Even-n decision phase WITHOUT hStrictMajority |
| `P_EM_solves_SSEM_no_strict_majority` | EvenNComplete.lean | **Master theorem without hStrictMajority** |
| `h_inv_dec_of_h_inv_swap` | EvenNComplete.lean | h_inv_dec follows from h_inv_swap (InSswap ⊆ InSrank) |
| `P_EM_solves_SSEM_ultimate` | EvenNComplete.lean | **ULTIMATE: 3 external hypotheses only** |
| `BurmanConvergence` | BurmanProperties.lean | Combined Burman hypothesis (ranking + timer + epidemic) |
| `P_EM_solves_SSEM_from_BurmanConvergence` | BurmanProperties.lean | Master theorem from BurmanConvergence + h_inv_swap |
| `P_EM_solves_SSEM_from_single_hypothesis` | BurmanProperties.lean | Master theorem from single `ProtocolConvergence` |
| `rankDeltaStable_satisfies_fix` | RankDelta.lean | Concrete `rankDeltaStable` satisfies `RankDeltaSettledFix` |
| `P_EM_solves_SSEM_concrete` | BurmanProperties.lean | **Concrete Theorem 4**: P_EM with `rankDeltaStable` solves SSEM (1 hypothesis) |

## Key design decisions

- `Protocol Q X Y` has δ : (Q×X)×(Q×X) → Q×Q and π_out : Q×X → Y
- `Config Q X n = Fin n → Q × X` (agents indexed by Fin n)
- `SolvesSSEM P n` quantifies over all initial configs, existentially over schedulers
- Theorem 2 requires input-oblivious hypothesis (matching paper's standard PP model)
- Theorem 2 takes an explicit balanced silent safe config as input
- Ranking subprotocol is a function parameter `rankDelta`, not an axiom
- `AgentState n` uses ℕ for timer/resetcount (unbounded but protocol-bounded in practice)
- Full convergence proof (Theorem 4: P_EM solves SSEM) is future work — requires ranking subprotocol convergence + 4-phase case analysis

## Decision-step single-step coverage

The single-step decision lemma `decision_step_at_median_no_swap_odd_decreases`
covers the case where:
  * `n` is odd,
  * `μ` is at the median rank,
  * `(C μ).1.answer ≠ majorityAnswer C` (median is currently wrong),
  * `v` is non-median, non-max, with `rank_v < rank_μ`,
  * `(C μ).1.timer ≥ 1`.

This handles "wrongAnswerCount > 0 because the median is wrong".  The
remaining gap is "wrongAnswerCount > 0 with median correct + some
non-median wrong" — fixing that agent requires propagation through
reset cycle, which transiently leaves `InSswap` (Resetting role) and
needs the macro-step + Burman re-settle machinery.

## Swap-step single-step coverage matrix

The four-way unified swap-step `swap_step_decreases_four_way` covers:

| Case | Conditions | Status |
|------|------------|--------|
| (i) Non-median | u, v both not at median rank | ✓ unconditional |
| (ii) Odd n, u at median, v not at max | `n % 2 = 1`, `u.timer ≥ 1` | ✓ |
| (iii) Odd n, u at median, v AT max | `n % 2 = 1`, `u.timer ≥ 2` | ✓ |
| (iv) Even n median pair | `n % 2 = 0`, u at lower median, v at upper, `n ≥ 4` | ✓ |
| (v) Odd n, u at median, `u.timer = 0` | reset CAN fire → breaks InSrank | ✗ macro-step |
| (vi) Even n = 2 | timer-dec modifies b₁.timer | edge case, skipped |

The remaining gaps (v), (vi) require the macro-step machinery (reset cycle
through `Resetting` role + Burman re-settle) — same machinery needed for
Theorem 4's `hDecisionPhase`.

## What's left (next milestone)

`Composition.lean` now provides `P_EM_solves_SSEM_via_phases`, which
takes three phase-reachability hypotheses instead of a single
consensus-reachability one:

  * `hRankPhase`     — every initial configuration eventually reaches
                       an `Srank` configuration.
  * `hSwapPhase`     — every `Srank` configuration eventually reaches
                       an `Sswap` configuration.
  * `hDecisionPhase` — every `Sswap` configuration eventually reaches
                       a consensus configuration (`InStim`).

`PotentialReach.lean` reduces `hSwapPhase` and `hDecisionPhase` further,
to single local single-step-decreases-potential hypotheses:

  * **`hSwapPhase`** ← `swap_reaches_Sswap_of_singleStep` modulo:

    > For every `InSrank C` with `0 < misorderedCount C`, there exist
    > agents `u, v` such that `C.step P u v` is still in `InSrank` and
    > has strictly smaller `misorderedCount`.

    Discharging this requires showing the swap step preserves
    Settled-rank-bijection while not triggering propagation reset.

  * **`hDecisionPhase`** ← `decision_reaches_consensus_of_singleStep`
    modulo:

    > For every `InSswap C` with `0 < wrongAnswerCount C`, there exist
    > agents `u, v` such that `C.step P u v` is still in `InSswap` and
    > has strictly smaller `wrongAnswerCount`.

    Discharging this requires the Propagate-Reset cycle analysis from
    Kanaya §5.2.1 Lemma 11.

  * **`hRankPhase`** — Burman et al.'s Optimal-Silent-SSR (PODC 2021).
    The concrete `rankDeltaOSSR` (Protocol 3) is now defined in
    `Protocol/RankDelta.lean`, implementing the full binary-tree ranking
    with collision detection, PROPAGATE-RESET, and error monitoring.
    `rankDeltaOSSR_settled_distinct_ranks` proves it is identity on
    Settled pairs with distinct ranks (the weaker form of
    `RankDeltaSettledFix` — the current abstract hypothesis requires
    identity on ALL Settled pairs, but the concrete protocol resets on
    same-rank collisions; a future refactor will weaken the hypothesis).

## Gap analysis — ONE remaining hypothesis

The master theorem `P_EM_solves_SSEM_concrete` takes a SINGLE
external hypothesis:

```
ProtocolConvergence trank Rmax (rankDeltaStable Rmax Emax Dmax hn)
```

which bundles:
  * `BurmanConvergence.ranking` — from any initial config, ranking
    converges to InSrank with timer ≥ 2 at median
  * `BurmanConvergence.epidemic` — correct answer spreads to all agents
  * `timer_inv` — timer ≥ 2 at median in all InSrank configs

This corresponds to Burman et al. (PODC 2021) Theorem 4.2 + timer
initialization properties. All other hypotheses have been formally
discharged.

### What's fully proved (zero sorry, zero axiom)

  * Impossibility without n (Theorem 1)
  * Space lower bound Ω(n) (Theorem 2)
  * Protocol encoding (Algorithm 1, 4 phases)
  * Concrete ranking subprotocol (Protocol 3, Burman)
  * Consensus preservation (output-stable at consensus)
  * Swap-phase convergence (8-way single step)
  * Decision-phase convergence (odd/even, tie/strict-majority)
  * Macro-step discharge from BurmanRankingCorrect
  * Phase composition (ranking → swap → decision → consensus)
  * Concrete protocol instantiation with `rankDeltaStable`

### 2026-05-15 — Uniform-origin non-circular reservoir-cycle factorisation

New green (axioms = [propext, Classical.choice, Quot.sound]; no sorry/axiom),
in `Convergence/BurmanConvergenceFinal.lean`:

  * `majorityAnswer_const_runPairs_execution` — runPairs+execution
    majorityAnswer constancy (re-export).
  * `reservoir_median_wrong_drive` — packages the proven non-circular
    `median_wrong_only_drive_to_consensus` strong recursion: from InSswap
    + live median timer, drives wrongAnswerCount→0 along the median-wrong
    arm; only the non-circular median-correct leaf is abstracted.
  * `uniform_to_InSswap_or_consensus` — all-Resetting+uniform ⇒
    (consensus) ∨ (InSswap with live median timer), via the PROVEN
    `ranking_from_all_resetting` + PROVEN
    `swap_reaches_Sswap_from_timer_bound_with_timer`. Fully unconditional.
  * `uniform_reaches_consensus_modulo_median_correct_leaf` /
    `all_resetting_uniform_reaches_consensus_noncircular` — THE target at
    the exact requested signature (NO γ₁/t₁, NO circular `hcons`), modulo
    a single NON-circular median-correct reservoir leaf `hMedCorrectExit`
    (asserts nothing about the goal config; no epidemic / Burman* /
    answer-stability / "∃ schedule reaching consensus" content).

Remaining irreducible point: the median-correct phi-renormalizer leaf =
the documented answer self-stabilization (epidemic) open core; assuming
it directly would be the banned circular `hAnsStable`/epidemic. The
ranking/swap entry and the entire median-wrong recursion are now closed
non-circularly.

### 2026-05-16 — `cycle_macro_discharge` timer-free bug fix (3rd over-strong-false-statement bug)

Diagnosed + fixed the third over-strong-false-statement formalization bug
of the project (after `partial_resetting` and the epidemic-signature):
`cycle_macro_discharge` carried a universal hypothesis
`hTimerLive : ∀ D, InSswap D → ∀ μ@median → 1 ≤ (D μ).1.timer`.

This universal is FALSE: `InSswap` (= `InSrank` + input-by-rank-sorted)
has NO timer constraint, so a stale `InSswap` config can have median
timer 0 — the exact counterexample that exposed the epidemic-signature
bug. The old proof applied `hTimerLive C hSswap` to every internal
`InSswap` config, so it could never be discharged; it blocked the whole
`hMacro` slot of `all_resetting_uniform_consensus_final`.

Fix (mirrors the epidemic-signature fix — remove the false universal,
case-split timer locally):

  * REMOVED the `hTimerLive` hypothesis from `cycle_macro_discharge`.
  * CASE 2 (median wrong): local `by_cases` on
    `∀μ@median → 1 ≤ (C μ).1.timer`.
      – 2a (true, derived locally — not assumed everywhere): one green
        `median_wrong_step_resAns_decrease` step, strictly drops
        `phiCount`.
      – 2b (some median timer = 0): a `timer = 0`-compatible reset path —
        folded into the now timer-free reset leaf via its second
        disjunct.
  * CASE 3 (median correct): folded into the reset leaf via its first
    disjunct.
  * `hResetLeaf` generalised to be **timer-free**: it accepts the
    disjunction `(median-correct) ∨ (∃ median μ, timer μ = 0)` — the two
    `timer = 0`-compatible reset paths — and carries NO universal
    timer-live hypothesis.

Build: green, no NEW sorry, no regression. The dual picture is now
encoded correctly: `1 ≤ timer@median` is needed ONLY in the
median-wrong-decision sub-case (derived locally), and `timer = 0` is
required (good) for the reset path. The single remaining `sorry`
(line ~6512, the `hMedCorrectExit` leaf with no `ResAns`/no tie-freeness)
is the documented genuine open core (even-n timer descent + `ResAns`
overlay through the answer-opaque ranking machinery + BFS-recruit /
dormant-wake structural witnesses + tie sub-case), unchanged.

## 2026-05-16 — hMedCorrectExit closure architecture (non-circularity resolved)

Build GREEN, 1 sorry: `hMedCorrectExit` (BurmanConvergenceFinal.lean:6509).
hTimerLive bug (3rd over-strong artifact) fixed + build errors repaired
(dup `settledCount` → reuse BurmanProof's; stray `split_ifs` removed).

NON-CIRCULAR route confirmed (NOT the `_to_RankingEndpoint` family —
`ranking_goal_of_RankingEndpoint` only re-states RankingEndpoint, no drive
to consensus, so that path loops back through the epidemic):

  D (InSswap, median-correct, ∃wrong, median timer≥1)
  → drain median timer ≥1→0  [G1: primitive exists,
      `no_reset_even_lower_max_timer_one_step_InSswap` (BurmanProof:692):
      InSswap-preserving, timer 1→0, answer unchanged]
  → `trigger_correct_reset_from_InSrank` (needs nAOf≠nBOf, wrong v off
      ranks {ceilHalf, n, n/2+1})  → seed
  → `all_resetting_from_seed_answer_aux` (GREEN) → ALL-Resetting & UNIFORM
      (every answer = majorityAnswer)
  → `all_resetting_uniform_consensus_final_noPhaseA_noRecruit`
      [hSelect←`exists_answer_safe_misordered_pair` GREEN;
       hMacro←`cycle_macro_discharge` GREEN (needs hNoTie);
       hTree/hFreshSafe = G4 open structural witnesses]
  → consensus → splice prefix.

WHY non-circular: UNIFORM ⇒ wrongAnswerCount=0 ⇒ the median-correct
recursion in cycle_potential/median_wrong_drive is VACUOUS (never re-enters
hMedCorrectExit). The uniform invariant collapses the recursion — this is
the whole point of the kernel's design.

OPEN GAPS: G1 timer-drain assembly (primitive exists, need even/odd glue +
InSswap+median-correct preservation); G2 tie sub-case (nAOf=nBOf, n even,
majorityAnswer=.outT — trigger_correct_reset & cycle_macro_discharge both
need nAOf≠nBOf; median-WRONG tie is already handled GREEN by
`median_wrong_decision_step`/`evenCase_witness_when_median_wrong_tie`, so
only median-CORRECT-tie is the burden; resolve: either tie-route w/o reset
or strengthen leaf w/ nAOf≠nBOf threaded from master call sites — note
SolvesSSEM has NO global no-tie, .outT is a real output); G3 wrong-agent
rank side-conditions; G4 hTree (BFS-recruit answer overlay) + hFreshSafe
(dormant-wake both-Settled-free+ResAns).

GPT-5.5 Pro blueprint requested (channel exact-mj, pipe) — pending.

### 2026-05-16b — tie sub-case is mathematically distinct (not a removable hyp)

`trigger_correct_reset_from_InSrank` uses `hne:nAOf≠nBOf` ONLY (even branch)
to prove `opinionToAnswer (C μ).2 = majorityAnswer C` via
`opinionToAnswer_lower_median_eq_majorityAnswer_even`. In a TIE majorityAnswer
= .outT but the median's INPUT opinion is .A/.B (∈{.outA,.outB}) ≠ .outT —
so `hμ_correct` is genuinely FALSE in a tie. The reset-trigger route is NOT
salvageable for ties by weakening a hypothesis; .outT is produced by the
median DECIDE recognising the boundary (`phase4_decide_even_boundary_tie_
writes_outT`, GREEN), not copied from any agent's input.

⇒ hMedCorrectExit needs TWO routes:
  • non-tie (nAOf≠nBOf): drain→trigger_correct_reset→seed→
    all_resetting_from_seed_answer_aux→UNIFORM→consensus_final.
  • tie (nAOf=nBOf, even, majorityAnswer=.outT, median already .outT):
    decide+propagate .outT from the correct median to wrong agents,
    decreasing wrongAnswerCount → consensus. (This is the answer-epidemic;
    the genuine open core. `decision_step_at_median_pair_even_tie_decreases`
    + `step_at_median_pair_even_disagreed_inputs` are the GREEN tie decide
    primitives to build on; median-WRONG-tie is already fully closed.)

Once UNIFORM (all=.outT or all=majority) is reached, wrongAnswerCount=0 ⇒
0<phiCount is false ⇒ cycle_macro_discharge's hNoTie need is VACUOUS — so
the only nAOf≠nBOf dependency is the seed-production step itself.

G1 timer-drain: even primitive `no_reset_even_lower_max_timer_one_step_
InSswap` (BurmanProof:692) GREEN. NO odd-n analog by name — odd-n median
timer handling differs (odd n ⇒ nAOf≠nBOf automatically; check
`oddCase_witness_when_median_wrong_with_timer` path / whether odd-n
median-correct even needs a drain).

GENUINE HARD CORE = the answer-epidemic: "propagate correct median answer
to a wrong/phi agent under InSswap+median-correct, decreasing
wrongAnswerCount, preserving InSswap+median-correct". Needed for the tie
route directly; the non-tie route routes around it via reset+uniform.

### 2026-05-16c — PROTOCOL MECHANICS: no Settled answer-epidemic ⇒ reset is the only route

Read Protocol/Transition.lean 32-106. KEY FACTS:
• phase4_propagate (81-95): acts ONLY when one of the pair is THE median
  (rank+1=ceilHalf n). If neither is median ⇒ IDENTITY. When median b₀,
  timer=0 ∧ b₀.answer≠b₁.answer ⇒ BOTH→Resetting, b₁:=b₀.answer. Else id.
  ⇒ NO answer spreading among Settled agents.
• Only answer-epidemic = transitionPEM_prePhase4 49-56: among BOTH-Resetting
  pairs, phi adopts partner's non-phi answer. (= all_resetting_from_seed_*)
• phase4_decide: odd n ⇒ median.answer := opinionToAnswer(its input).
  even n ⇒ ONLY the (n/2,n/2+1) median PAIR writes; inputs disagree⇒.outT;
  any other pair ⇒ IDENTITY.

CONSEQUENCE: there is NO "propagate correct answer to wrong Settled agent"
step. hMedCorrectExit's ONLY route is reset→all-Resetting→seed-epidemic→
uniform→re-rank→consensus. The feared "answer-epidemic overlay" does NOT
exist to build — good, the route is the reset one, uniformly tie & non-tie.

TIE NOW WELL-SCOPED: pair lower-median μ (μ.answer=majorityAnswer=.outT by
the median-correct HYPOTHESIS) with a wrong non-median v that is NOT the
upper-median (v.rank+1≠n/2+1). Then phase4_decide is IDENTITY on (μ,v)
(even branch needs the n/2 & n/2+1 pair; v≠upper ⇒ else-id) so μ.answer
survives = correct. With μ.timer drained to 0 and μ.answer≠v.answer,
phase4_propagate fires: μ stays Resetting w/ .outT, v:=μ.answer=.outT.
SEED carries majorityAnswer. ⇒ a TIE-VARIANT of
trigger_correct_reset_from_InSrank is provable using the median-correct
ANSWER hyp + decide-identity, NOT "median input=majority" (which is the
only place the original needs nAOf≠nBOf, lines ~1295-1301). This is a
SMALL structured modification of the existing even branch, NOT a new
epidemic. Downstream (all_resetting_from_seed_answer_aux → uniform →
all_resetting_uniform_consensus_final[+hTree/hFreshSafe]) is GREEN/exists.

OPEN, now well-scoped: (a) even-n-tie trigger variant lemma; (b) G1 timer
drain to median-timer-0 (even primitive no_reset_even_lower_max_timer_one_
step_InSswap @BurmanProof:692; odd via InSrank_timer_*_to_RankingEndpoint
family); (c) G3 pick wrong non-median, non-upper-median v (∃ by counting:
0<wrongAnswerCount, median-correct ⇒ ≥1 wrong non-median; if all wrong
ones sit at excluded ranks, one InSswap-preserving relocation step);
(d) G4 hTree/hFreshSafe for the kernel (uniformity NOT carried by
uniform_to_InSswap_or_consensus per a78… probe, so kernel IS needed).

### 2026-05-16d — bricks committed; refined drain; G4 is the heavy core

COMMITTED GREEN (each builds exit 0, only the lone hMedCorrectExit sorry):
• exists_wrong_nonmedian_of_med_correct (52e3f5cd) — ResAns-free selector.
• trigger_correct_reset_from_InSrank_even (84593f1e) — TIE reset trigger,
  faithful extraction of the proven even branch minus hne/hμ_correct
  (those are odd-branch-only). The conceptually-hardest piece, DONE.

REFINED TIMER-DRAIN (brick 2): case on RankingEndpoint D
(=InSrank ∧ (∀median timer≥2 ∨ consensus); D not consensus since
wrongAnswerCount>0):
• ¬RankingEndpoint D ⇒ BadRankingStart D ⇒
  `BadRankingStart.exists_median_timer_lt_two` (BurmanProof:11904) gives a
  median with timer<2; with the leaf's timer≥1 ⇒ that median has timer
  EXACTLY 1 ⇒ only a single 1→0 step
  (`no_reset_even_lower_max_timer_one_step_InSswap` BurmanProof:692, even;
  odd analog needed). NO arbitrary descent.
• RankingEndpoint D (all median timer≥2): drain via max-rank partner
  (`InSrank.exists_max_rank` BurmanProof:11926, GREEN). Each (μ,max) step
  decrements μ.timer; while result≥1 NO reset regardless of answers
  (Transition.lean:84-88). Recurse on timer value to 1, then the 1→0
  endgame. EDGE: if the only wrong agent sits at max-rank, the clean
  drain partner (answer=μ.answer) may not exist; either relocate via one
  InSswap step or add a max-rank seed trigger variant (mirror the GREEN
  `InSrank_timer_one_max_*_to_RankingEndpoint` family but with the
  trigger_correct_reset SEED conclusion).

G4 (the heavy core, no collapse): phaseA_discharge(4743)/
recruit_selector_discharge(4812) are GREEN but only REDUCE hPhaseA/hRecruit
to hFreshSafe / hTree, which must still be CONSTRUCTED:
• hFreshSafe: a concrete dormant→awakening→fresh schedule L for an
  all-Resetting config + the per-prefix-step not-both-Settled property
  (the not-both-Settled per-step certificates already exist GREEN at
  BurmanConvergenceFinal:4636-4721; assemble them along the proven
  dormant→awakening→fresh sweep from BurmanProof phase3bc_from_awakening
  9985 / ranking_from_all_resetting* 13664/13731).
• hTree: BFS-recruit pair selector for ¬InSrank configs (exact shape at
  4814-4852) from rankDeltaOSSR_recruits 85 / heapPrefix_recruit_step
  10939 / phase4_binary_tree 11225 + rankDeltaOSSR_answer_preserved.
Role-structural only (no answer/epidemic) — repackaging the proven
answer-opaque ranking machinery into the kernel's witness shapes. This is
the genuine multi-hour remainder (project docs: ~ resetFuel-normalizer
scale).

ASSEMBLY: exists_wrong_nonmedian → (refine off max/upper or relocate) →
drain median timer→0 → by_cases nAOf=nBOf: tie→trigger_correct_reset_
from_InSrank_even, non-tie→trigger_correct_reset_from_InSrank → seed →
all_resetting_from_seed_answer_aux → all-Resetting+UNIFORM →
all_resetting_uniform_consensus_final_noPhaseA_noRecruit (hTree/hFreshSafe
from G4; hSelect←exists_answer_safe_misordered_pair; hMacro←
cycle_macro_discharge w/ hNoTie from the non-tie by_cases / vacuous post-
uniform) → consensus → splice runPairs/execution prefixes.

### 2026-05-16e — 4TH OVER-STRONG BUG FOUND: hTree is FALSE as stated

InSrank C := (∀v role=.Settled) ∧ ranks_injective (Sets.lean:34-36).
`hTree` (recruit_selector_discharge input, BurmanConvergenceFinal:4814):
  ∀ D, ¬InSrank D → ∃ p child, p≠child ∧ (D p).role=.Settled ∧
        (D child).role=.Unsettled ∧ … (binary-tree recruit data)
COUNTEREXAMPLE (n=4): every agent .Settled, all rank 0 ⇒ ranks not
injective ⇒ ¬InSrank D, but ZERO .Unsettled agents ⇒ the ∃child with
role=.Unsettled is UNSATISFIABLE. So hTree is FALSE universally.
⇒ 4th instance of the project's confirmed over-strong-lemma pattern
(cf. partial_resetting, epidemic-signature, hTimerLive). Methodology
("Proof Stuck = Bug": 证不过去先查定义") validated a 4th time.

WHY only false in general: hTree is consumed by recruit_selector_discharge
→ hRecruit, applied (all_resetting_uniform_to_InSswap_ResAns:4364) ONLY to
`FreshRankingStart`-derived configs in the binary-tree recruit loop.
FreshRankingStart = one Settled root (rank 0) + REST Unsettled; the recruit
loop turns Unsettled→Settled one at a time, so a ¬InSrank config IN THE
LOOP always has ≥1 Unsettled agent. The over-strength is only for arbitrary
¬InSrank D outside that invariant.

FIX (same shape as bugs #1-3 — weaken the universal, thread the real
precondition from the call site): add to hTree a hypothesis that holds
throughout the recruit loop. Minimal: `(∃ u, (D u).1.role = .Unsettled)`
(recruit-frontier non-emptiness), OR the stronger FreshRankingStart-derived
binary-tree-partial invariant. Then thread it through
recruit_selector_discharge → all_resetting_uniform_to_InSswap_ResAns →
all_resetting_uniform_to_fresh_start_ResAns → all_resetting_uniform_
consensus_final[_noPhaseA_noRecruit], discharging it from FreshRankingStart
(root Settled + rest Unsettled ⇒ ∃ Unsettled while ¬InSrank) preserved by
the recruit step until InSrank. Construct the (now-true) weakened hTree
from rankDeltaOSSR_recruits(BurmanProof:85)/heapPrefix_recruit_step(10939)/
phase4_binary_tree(11225)+rankDeltaOSSR_answer_preserved + the
FreshRankingStart binary-tree frontier.

This REPLACES the earlier "G4 = construct a hard witness" framing: hTree
cannot be constructed as-stated (it is false); it must first be WEAKENED.
This is the genuine remaining structural work, now correctly diagnosed.

SUBAGENT NOTE: background subagents are NOT progressing in this env
(afd0a56e313fee9f0 transcript frozen 141 bytes @09:34, no edits/builds in
10+min). All real progress has been direct-main-thread (bricks #1,#3
committed green). Continue DIRECT; do not re-delegate.

### 2026-05-16f — exact hTree weaken-and-thread refactor plan

Committed brick: `freshRankingStart_exists_unsettled` (1dccbdac) —
FreshRankingStart ∧ n≥2 ⇒ ∃ Unsettled. GREEN.

hRecruit consumption chain (verified by reading 4189-4249):
  all_resetting_uniform_consensus_final
   → all_resetting_uniform_to_InSswap_ResAns (hRecruit slot)
   → fresh_start_ResAns_to_InSrank_safe (4238, applies hRecruit in a
     recursion from `hFresh : FreshRankingStart C`)
   → recruit_selector_discharge (produces hRecruit from hTree)

KEY STRUCTURAL FACT: the binary-tree recruit step assigns `child` the
FRESH rank 2*p.rank+p.children+1 which `hfree` guarantees was previously
unoccupied ⇒ ranks stay INJECTIVE throughout the recruit loop. Hence
in-loop  ¬InSrank D ⟺ ¬(allSettled) ⟺ (∃ u, role=.Unsettled).
So the over-strong `hTree`/`hRecruit` are TRUE precisely on the
rank-injective (FreshRankingStart-derived) configs the loop visits.

REFACTOR (minimal weakening + thread):
1. Weaken `hTree` antecedent (recruit_selector_discharge:4814) and the
   `hRecruit` antecedent (4189-4191): add `(∃ u, (D u).1.role=.Unsettled)`
   (equivalently carry `Function.Injective rank` and derive ∃Unsettled
   from ¬InSrank). Pick the ∃Unsettled form — smallest surface.
2. `recruit_selector_discharge`: pass the new hyp through hTree D call.
3. `fresh_start_ResAns_to_InSrank_safe` (the recursion): add the loop
   invariant `RanksInjective D` (preserved by the fresh-rank recruit
   step; hfree ⇒ new rank distinct from all existing). At each ¬InSrank
   step derive ∃Unsettled (¬allSettled, since injective) to feed
   hRecruit. Base: FreshRankingStart ⇒ injective (root rank0 unique;
   Unsettled agents' ranks — need their ranks distinct; FreshRankingStart
   only constrains root; the recruit step is what builds injectivity, so
   the invariant is "ranks of Settled agents injective" + Unsettled
   untouched until recruited — inspect fresh_start_ResAns_to_InSrank_safe
   actual recursion measure/IH before finalizing the invariant).
4. all_resetting_uniform_to_InSswap_ResAns / _final: hRecruitWeak slot;
   discharge ∃Unsettled at the top from hFresh via
   freshRankingStart_exists_unsettled, thread the injectivity invariant.
5. recruit_selector_discharge's now-true weakened hTree: construct from
   rankDeltaOSSR_recruits(BurmanProof:85)/heapPrefix_recruit_step(10939)/
   phase4_binary_tree(11225)+rankDeltaOSSR_answer_preserved restricted to
   ∃Unsettled configs.

NEXT BRICK: read fresh_start_ResAns_to_InSrank_safe's recursion (grep it)
to pin the exact loop invariant, then weaken recruit_selector_discharge +
hRecruit signature and rebuild.

Remaining after hTree: brick#2 timer-drain, hFreshSafe, final assembly.
Genuine multi-hour grind; subagents non-functional here — direct only.

### 2026-05-16g — exact recursion invariant J (refactor fully specified)

Read fresh_start_ResAns_to_InSrank_safe (4109-4174). Its inner recursion
`suffices h : ∀ k C, ResAns m₀ C → unrecruitedTargetRankCount C ≤ k → …`
carries ONLY ResAns + measure; it DISCARDS FreshRankingStart (`_hFresh`
unused, 4143). That is exactly why hRecruit/hTree are stated over-strong.

EXACT FIX — thread invariant
  J C := (∀ w, (C w).1.role ≠ .Resetting)
         ∧ Function.Injective (fun v : {v // (C v).1.role = .Settled} =>
                                 (C v.1).1.rank)        -- Settled-ranks inj
through the `h` recursion (add `J C →` to its antecedent):
• FreshRankingStart ⇒ J  (root the only Settled ⇒ Settled-rank-inj
  trivial; all others Unsettled ⇒ no Resetting). New helper.
• recruit step `C.step P p child` preserves J: child→Settled at the
  FRESH rank 2*p.rank+p.children+1 (hfree ⇒ unused ⇒ Settled-ranks stay
  injective); p & others unchanged; recruit never creates Resetting.
  New helper (use rankDeltaOSSR recruit role/rank facts).
• J ∧ ¬InSrank ⇒ ∃ u, role=.Unsettled: InSrank=allSettled∧allRanksInj.
  Under J, Settled-ranks injective; if allSettled then allRanksInj ⇒
  InSrank — contradiction ⇒ ¬allSettled ⇒ ∃ non-Settled; J's
  no-Resetting ⇒ that agent is Unsettled. New helper.
Then weaken hRecruit (4112-4125) & hTree (4814-4846): add hypothesis
`(∃ u, (D u).1.role = .Unsettled)`. recruit_selector_discharge passes it
to hTree. fresh_start_ResAns_to_InSrank_safe derives it from J at each
¬InSrank step. Thread the (now-weaker) hRecruit slot up through
all_resetting_uniform_to_InSswap_ResAns (4189) and
all_resetting_uniform_consensus_final[_noPhaseA_noRecruit]; discharge the
top-level via hFresh ⇒ J (and freshRankingStart_exists_unsettled).
Finally CONSTRUCT the weakened (now-true) hTree from
rankDeltaOSSR_recruits/heapPrefix_recruit_step/phase4_binary_tree +
rankDeltaOSSR_answer_preserved, given ∃Unsettled.

Refactor is now FULLY specified mechanically. Execution = ~6-9 helper/
weakened lemmas, each ~10min build. Plus brick#2 timer-drain, hFreshSafe,
final hMedCorrectExit assembly. Direct main-thread only (subagents dead).

### 2026-05-16h — MAJOR: proven answer-opaque ranking driver bypasses hTree

DISCOVERY (validated methodology, "证不过去先查定义"): BurmanProof.lean
already contains the proven GREEN answer-OPAQUE ranking drivers:
• `phase4_binary_tree` (11225): HeapPrefix-seed → ∃L, HeapPrefix n
  (=InSrank via HeapPrefix.to_InSrank 10258) via the `grow` recursion
  that calls `heapPrefix_recruit_step` (10939) each step. GREEN.
• `phase34_rerank` (11300): IsDormantConfig → ∃L, InSrank ∧
  (median timer≥2 ∨ consensus). Composes phase3a_to_awakening +
  phase3bc_from_awakening + phase4_binary_tree. GREEN.
• `FreshRankingStart.to_heapPrefix_one` (10208): FreshRankingStart →
  HeapPrefix C 1.  ⇒ FreshRankingStart → ∃L InSrank, GREEN, answer-opaque.

KEY: the recruit step (heapPrefix_recruit_step ⇒ transitionPEM_recruit)
is ANSWER-INERT on the fresh non-median rank
(`rankDeltaOSSR_answer_preserved`). So ResAns m₀ rides through the ENTIRE
phase4_binary_tree drive for free. ⇒ the over-strong hTree/hRecruit (bug
#4) AND the 20-commit weakened-J cascade (recruit_selector_discharge_weak
… _noPhaseA_noRecruit_weak) are UNNECESSARY: there is a proven
answer-opaque FreshRankingStart→InSrank driver, and ResAns is preserved
because recruit is answer-inert.

LESSON: should have grepped BurmanProof for an existing
FreshRankingStart→InSrank driver BEFORE building the elaborate weakened
cascade. The J-cascade commits are valid green lemmas (not harmful) but
superseded by the proven-machinery route.

CORRECT REMAINING PATH (dramatically simplified):
• `fresh_start_ResAns_to_InSrank_safe` replacement: FreshRankingStart C →
  ResAns m₀ C → ∃L, InSrank(runPairs C L) ∧ ResAns m₀ ∧ majorityAnswer
  preserved — via phase4_binary_tree (proven, gives the schedule L) +
  ResAns preservation along L (every step is a recruit ⇒ not-both-Settled
  ⇒ runPairs_preserves_ResAns_of_steps_not_both_settled, OR per-step
  answer-inertness rankDeltaOSSR_answer_preserved). NO hTree/hRecruit.
• Then InSrank+ResAns → InSswap via InSrank_ResAns_safe_to_InSswap_ResAns
  (hSelect ← exists_answer_safe_misordered_pair, GREEN).
• Or even simpler: closure needs all-Resetting+UNIFORM → consensus.
  all_resetting_from_seed_answer_aux gives all-Resetting+UNIFORM(=m₀).
  phase34_rerank drives dormant/all-Resetting → InSrank+(timer≥2 ∨ cons).
  Check whether UNIFORM survives phase34_rerank (recruit answer-inert;
  awakening/dormant phases need ResAns-preservation check). If UNIFORM
  preserved to InSswap ⇒ wrongAnswerCount=0 ⇒ consensus directly via
  isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero.

NEXT: verify ResAns/uniform preservation through phase34_rerank's
phase3a/3bc (awakening/seed) — those may touch answers. If preserved,
the closure collapses to: trigger→seed→all_resetting_from_seed_answer_aux
→ phase34_rerank → InSswap-uniform → wrongAnswerCount=0 → consensus.
Brick #2 timer-drain + tie-trigger (committed) + final assembly remain.

### 2026-05-16i — exact recipe: rankDeltaOSSR_answer_preserved is UNCONDITIONAL

`rankDeltaOSSR_answer_preserved` (RankDelta.lean:276), GREEN:
  ∀ s t, (rankDeltaOSSR (s,t)).1.answer = s.answer
       ∧ (rankDeltaOSSR (s,t)).2.answer = t.answer   -- UNCONDITIONAL
So EVERY rankDeltaOSSR step preserves both answers. transitionPEM =
prePhase4(rankDeltaOSSR) then phase4(only if both Settled). For a recruit
step (parent Settled, child Unsettled):
• not both Settled ⇒ phase4 is identity (transitionPEM_phase4_of_not_
  both_settled);
• no agent ENTERS Resetting (recruit: child Unsettled→Settled, parent
  stays Settled) ⇒ prePhase4 phi-wipe (Transition.lean:37-48) does NOT
  fire ⇒ prePhase4 output answers = rankDeltaOSSR answers = inputs.
⇒ a recruit step preserves BOTH agents' .answer exactly. Hence ResAns m₀
and majorityAnswer ride FREE through the whole heap-recruit drive.

EXACT REMAINING RECIPE (supersedes the J-cascade):
`phase4_binary_tree_ResAns`: FreshRankingStart C → ResAns m₀ C → ∃L,
  InSrank(runPairs C L) ∧ (median timer≥2 ∨ consensus) ∧
  ResAns m₀(runPairs C L) ∧ majorityAnswer(runPairs C L)=majorityAnswer C.
Proof = COPY phase4_binary_tree (BurmanProof:11225), add `ResAns m₀ C₀`
(and a majorityAnswer-eq carry) to the `grow` invariant. Per step:
heapPrefix_recruit_step gives (parent,child) [parent Settled via
HeapPrefix hUnique/hRoles; child Unsettled]; prove the single
runPairs[(parent,child)] step preserves every answer via:
  - phase4 identity (not both Settled: child Unsettled),
  - prePhase4 no-wipe (no Resetting entry on a recruit),
  - rankDeltaOSSR_answer_preserved.
⇒ ResAns m₀ + majorityAnswer carried; recurse. (HeapPrefix is the
invariant heapPrefix_recruit_step needs — already threaded by the proven
grow; just piggyback ResAns/maj on it.)

Then: `fresh_start_ResAns_to_InSrank_safe` replacement =
phase4_binary_tree_ResAns + InSrank_ResAns_safe_to_InSswap_ResAns
(hSelect←exists_answer_safe_misordered_pair). NO hTree/hRecruit/hTreeW;
the 7 weakened-J cascade commits are superseded (valid green lemmas, but
the proven-machinery route is the real one).

CLOSURE = trigger reset (non-tie: trigger_correct_reset_from_InSrank;
tie: trigger_correct_reset_from_InSrank_even [committed]) → seed →
all_resetting_from_seed_answer_aux → all-Resetting+UNIFORM → (need a
FreshRankingStart from all-Resetting: phase3a_to_awakening +
phase3bc_from_awakening, GREEN, answer-preserving by the same
rankDeltaOSSR_answer_preserved argument since those are also rankDeltaOSSR
steps with no phase4) → phase4_binary_tree_ResAns → InSrank+UNIFORM →
swap → InSswap+UNIFORM ⇒ wrongAnswerCount=0 ⇒
isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero → consensus →
splice prefixes. + brick#2 timer-drain for the trigger's timer=0.

NOTE: phase3a/3bc/swap are ALSO rankDeltaOSSR steps; check each for
prePhase4 Resetting-entry (the reset/awakening phases DO move agents in/
out of Resetting → prePhase4 MAY phi-wipe). all_resetting_from_seed_
answer_aux already handles the reset-phase answer spread to UNIFORM; the
post-FreshRankingStart recruit drive is the clean answer-inert part.

### 2026-05-16j — exact per-step ingredients located (turn-key)

Per-step recruit answer-preservation ingredients (all GREEN, BurmanProof):
• `rankDeltaOSSR_answer_preserved` (RankDelta.lean:276) — UNCONDITIONAL
  ∀ s t, rankDeltaOSSR preserves both .answer.
• `prePhase4_recruit_ba_answer_preserved` (BurmanProof:10528) — prePhase4
  preserves answers on a recruit (a Unsettled, b Settled).
• `transitionPEM_recruit_ba_answer_inert_of_no_median` (BurmanProof:10562)
  — full transitionPEM answer-inert for recruit, with no-median/lower/
  upper side-conditions (conservative version).
KEY: in phase4_binary_tree's grow, EVERY step is (Settled parent,
UNSETTLED child) ⇒ input pair is NOT both-Settled ⇒
`transitionPEM_phase4_of_not_both_settled` ⇒ phase4 = identity that step
UNCONDITIONALLY (no median side-conditions needed for the answer claim).
prePhase4 has no answer-wipe unless an agent ENTERS Resetting (recruit:
none do). ⇒ recruit step preserves both answers unconditionally; the
no-median hyps in 10562 are only needed for its timer/other claims, not
the answer part. So per-step ResAns/maj preservation is clean.

TURN-KEY for phase4_binary_tree_ResAns (put in BurmanConvergenceFinal,
leave BurmanProof 0-sorry):
1. helper `recruit_step_answers_eq`: a Unsettled, b Settled ⇒
   transitionPEM step preserves both .answer. Proof: phase4 identity
   (transitionPEM_phase4_of_not_both_settled, child Unsettled) +
   prePhase4_recruit_ba_answer_preserved + rankDeltaOSSR_answer_preserved.
   ⇒ runPairs[(parent,child)] step: ∀w, answer unchanged.
2. `phase4_binary_tree_ResAns`: copy phase4_binary_tree (BurmanProof:
   11225) verbatim; in `grow` add invariant `(∀ w, (C₀ w).1.answer =
   (C w).1.answer)` (answers-equal-to-original) — or directly ResAns m₀
   ∧ majorityAnswer C₀ = majorityAnswer C. After heapPrefix_recruit_step
   gives (parent,child) [parent Settled from HeapPrefix hUnique, child
   Unsettled from hExistsUnsettled-style], apply helper #1 to carry
   answers; recurse. heapPrefix_recruit_step already preserves HeapPrefix
   + timer; just piggyback the answer invariant.
3. Replace fresh_start_ResAns_to_InSrank_safe usage:
   phase4_binary_tree_ResAns then InSrank_ResAns_safe_to_InSswap_ResAns
   (hSelect ← exists_answer_safe_misordered_pair).

REMAINING (multi-session-scale execution, fully specified):
phase4_binary_tree_ResAns (+helper) ; all-Resetting→FreshRankingStart
answer-carry (phase3a_to_awakening + phase3bc_from_awakening — these MOVE
agents in/out Resetting so prePhase4 MAY phi-wipe; all_resetting_from_
seed_answer_aux already gives all-Resetting+UNIFORM, so the post-seed
dormant→awakening→fresh part must be shown answer=majorityAnswer-stable
OR routed so UNIFORM is re-established at FreshRankingStart) ; brick#2
median-timer-drain to 0 (no_reset_even_lower_max_timer_one_step_InSswap
@BurmanProof:692 + the BadRankingStart.exists_median_timer_lt_two
refinement) ; final hMedCorrectExit assembly (exists_wrong_nonmedian →
rank refine → drain → by_cases tie → trigger_correct_reset_from_InSrank
[non-tie] / _even [tie, committed] → all_resetting_from_seed_answer_aux →
phase4_binary_tree_ResAns → InSswap+UNIFORM → wrongAnswerCount=0 →
isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero → splice).
All blockers diagnosed; no unsolved math; ~10min/build, many lemmas.

### 2026-05-16k — CORRECTION: ResAns does NOT ride free (16h/16i overclaimed)

VERIFY-BEFORE-CLAIM correction. Re-read prePhase4_recruit_ba_answer
_preserved (BurmanProof:10528) + its companion comment (10554-10561):
after prePhase4 the recruited child is .Settled, so on a recruit step
BOTH agents are Settled at the phase4 input ⇒ transitionPEM_phase4
FIRES (NOT identity). phase4_decide writes .answer AT MEDIAN RANKS.
⇒ a recruit step is answer-inert ONLY when neither agent lands at a
median/lower/upper rank (exactly the side-conditions of
transitionPEM_recruit_ba_answer_inert_of_no_median, BurmanProof:10562).

Therefore the 2026-05-16h/16i claim "rankDeltaOSSR_answer_preserved is
unconditional ⇒ ResAns rides FREE through phase4_binary_tree" is
OVERCLAIMED and WRONG at median-recruit steps: when the median agent is
recruited, phase4_decide writes opinionToAnswer(its input), which equals
m₀ only under median-input-correctness — precisely the reservoir-overlay
fact that is FALSE in a tie (the genuine hard core; the crux of the tie
sub-case). rankDeltaOSSR_answer_preserved is about the rankDelta layer
only; the full transitionPEM step is NOT answer-inert at median recruits.

CONSEQUENCE: phase4_binary_tree is answer-OPAQUE (gives InSrank, no ResAns
guarantee). The real ResAns overlay requires per-median-recruit-step
answer-correctness = exactly what the kernel's PairResAnsSafe / hSelect /
the hTree(W) machinery encodes. The weakened-J cascade (commits 52e3f5cd
… a53e1741) was addressing the REAL difficulty; it is NOT superseded.
The genuine remaining core is the hTreeW WITNESS construction: a recruit
selector whose chosen pair is PairResAnsSafe (median-recruit writes m₀),
which under ResAns m₀ + the reservoir structure holds at NON-tie; the tie
sub-case (median decide writes .outT) needs the tie-decide machinery
(phase4_decide_even_boundary_tie_writes_outT, majorityAnswer_eq_outT_of
_tie) — analogous to the committed tie-trigger.

STATUS: methodology cuts both ways — caught my own overclaim by
re-reading the proven lemma's actual semantics. The hard core stands:
construct hTreeW with PairResAnsSafe at median recruits. The J-cascade
green commits remain valid and ARE the right scaffold; the missing piece
is the genuine recruit-selector witness (reservoir overlay), the
documented ~resetFuel-scale multi-session core. No shortcut exists.

### 2026-05-16l — sharp characterization of the genuine hard core

hTree/hTreeW's hans1/hans2 (recruit_selector_discharge input, lines
~4983-4988 / hTreeW copies) demand STRICT answer-inertness:
  transition.1.answer = (D p).1.answer ∧ transition.2.answer =
  (D child).1.answer.
recruit_selector_discharge builds PairResAnsSafe from these by
`rw [hans1]; exact hRes p`. But (per 2026-05-16k) a recruit step has
both agents Settled post-prePhase4 ⇒ phase4 fires ⇒ phase4_decide writes
opinionToAnswer(input) AT MEDIAN RANKS ≠ old answer. So hans1/hans2 are
UNSATISFIABLE for a recruit whose pair lands at a median rank — yet the
median rank MUST eventually be filled by the BFS heap recruit. Hence the
strict-inertness hTree route inherently covers only NON-median recruits;
the median recruit's PairResAnsSafe (answer ∈ {m₀,.phi}) must be
established from MEDIAN-INPUT-CORRECTNESS (decide writes
opinionToAnswer(median input) = majorityAnswer = m₀ under the sorted
reservoir structure) — NOT from strict inertness. This is precisely the
reservoir overlay, and it is FALSE in a tie (median input ≠ .outT),
needing the tie-decide machinery (phase4_decide_even_boundary_tie_writes
_outT, majorityAnswer_eq_outT_of_tie) — the same crux as the committed
tie-trigger.

⇒ THE GENUINE HARD CORE (no shortcut; all apparent ones verified
illusory): construct the recruit-selector witness so that
  • non-median recruits: strict answer-inertness (off-median decide
    identity) — provable via transitionPEM_recruit_ba_answer_inert_of_no
    _median (BurmanProof:10562) given the no-median rank conditions;
  • the median recruit: PairResAnsSafe via median-input-correctness
    (non-tie) / tie-decide-writes-.outT (tie), threading the reservoir
    invariant ResAns m₀ + the InSrank-sorted input structure.
This is the documented ~resetFuel-scale multi-session reservoir overlay.
The committed J-cascade is the right scaffold; this witness is the
missing genuine-hard piece. The tie sub-case mirrors the (committed)
trigger_correct_reset_from_InSrank_even tie analysis.

SESSION HONEST SUMMARY (24+ commits): 3rd bug fixed+green; all 4
over-strong bugs diagnosed; tie-trigger + ResAns-free selector green;
full weakened-J scaffold green; a tempting bypass explored AND honestly
retracted via verify-before-claim; the exact genuine hard core sharply
characterized and fully persisted. The single sorry is the genuine
multi-session reservoir-overlay core of a published theorem — every
blocker diagnosed, correct scaffold committed, no shortcut (verified),
recipe persisted for continuation.

### 2026-05-16m — TERMINAL finding: ranking is input-opaque

rankDeltaOSSR recruit (RankDelta.lean:209-218): recruited agent gets
rank := 2*parent.rank+parent.children+1 — PURELY STRUCTURAL, does NOT
read input opinion. ⇒ which agent occupies the median rank during the
binary-tree ranking is determined by recruit ORDER, not by input. ⇒ when
the median-rank agent recruits (phase4 fires, both Settled),
phase4_decide writes its .answer := opinionToAnswer(its arbitrary input)
≠ m₀ in general. ⇒ ResAns m₀ is provably NOT an invariant of the ranking
phase. The answer is necessarily garbage-during-ranking and only
re-established AFTER swap (inputs rank-sorted) + decide + propagate.

CONSEQUENCE: the kernel's design of threading ResAns m₀ via
PairResAnsSafe THROUGH each recruit (recruit_selector_discharge/hTree/the
J-cascade) rests on a premise (recruit preserves the reservoir) that is
FALSE at the median recruit. Either (i) the recruit selector must avoid
ever pairing the median-rank agent until inputs are effectively sorted
(not possible in a pure binary-tree recruit — median rank is interior),
or (ii) the genuine proof tracks answers as UNCONSTRAINED during ranking
and re-establishes ResAns/consensus only in the post-InSswap decide+
propagate epidemic. (ii) is the actual Kanaya et al. self-stabilization
mechanism: rank first (answer-opaque), THEN the sorted median decides and
the answer epidemic propagates m₀. The hMedCorrectExit leaf's real
content is this post-swap answer epidemic — which is exactly the
"answer-and-timer overlay" the project always flagged as the
~resetFuel-scale multi-session core, NOT a recruit-time invariant.

This is the rigorous terminus of single-session analysis: the genuine
remaining proof is the post-InSswap answer epidemic (median decides m₀
from sorted input; propagate spreads it; conflicts reset), a multi-
session formalization with no recruit-time shortcut (every apparent one
verified illusory across 16h–16m). All 4 over-strong bugs diagnosed; the
correct scaffolding committed green (25+ commits); the exact genuine core
and the precise reason it is multi-session are fully characterized and
persisted. No fabrication, no axiom escape, no false shortcut taken.

### 2026-05-16n — GPT github-access analysis CONFIRMS structure; exact target named

GPT-5.5 read the actual pushed code (commit 365c146e) and independently
confirmed:
• ResAns is NOT reachable at the line-~7575 hMedCorrectExit scope.
  BurmanConvergence.epidemic's input is only
  `h_correct : ∃ w, (C₀ w).1.answer = majorityAnswer C₀` (ONE agent),
  not ResAns. InSrank+timer give no reservoir info.
• Threading ResAns INTO hMedCorrectExit fails: epidemic_timer_branch_to_
  consensus calls the leaf on internally-produced (median-wrong-recursion)
  configs, and there is no ResAns E₁ at the call site to initialise it.
• Therefore the SMALLEST missing lemma is a ResAns-ENTRY bridge:

  theorem med_correct_live_InSswap_to_reservoir_entry
      {Rmax Emax Dmax}{hn:0<n}(hn4:4≤n)
      {D}(hSswap:InSswap D)
      (hTimer:∀μ, rank+1=ceilHalf n → 1≤timer)
      (hWrong:0<wrongAnswerCount D)
      (hMedCorrect:∀μ, rank+1=ceilHalf n → answer=majorityAnswer D) :
      ∃ γ t, let C:=execution P D γ t; InSswap C ∧ ResAns (majorityAnswer C) C

  Then hMedCorrectExit is a SINGLE-SESSION wrapper:
  obtain ⟨γ₀,t₀,hEntry⟩ := med_correct_live_InSswap_to_reservoir_entry …;
  hMacro := cycle_macro_discharge hn4 ?hNoTie ?hResetLeaf;
  cycle_potential_reaches_consensus hMacro C hEntry.1 hEntry.2;
  splice schedules. (GPT gave exact code.)
  NOTE: cycle_macro_discharge STILL needs ?hResetLeaf — the genuine
  reservoir-reset core (same shape as the leaf). So the wrapper relocates
  but does not eliminate the hard core; hResetLeaf must also be proven.

ASSEMBLABLE FROM GREEN (odd-n; odd ⇒ nAOf≠nBOf, no tie):
TimerDescentNoSwap.lean has the drain infra GPT pointed to:
• InSswap.median_input_A (23) / max_input_B (31)
• step_at_median_max_no_swap_odd (54) — single timer−1 step, needs
  timer≥2, μ.input=.A, max-rank partner v; preserves InSswap/rank/role,
  v & others unchanged, μ.answer:=opinionToAnswer(.A).
• timer_descent_to_one (231) — drives median timer ≥2 → ≤1, InSswap +
  ranks + μ.input=.A preserved.
• step_at_median_timer_zero_reset_fires (309) — at median timer=0 + w
  non-max non-median + w.answer≠opinionToAnswer(μ.input): step (μ,w)
  makes μ,w Resetting, w.answer:=opinionToAnswer(μ.input)=m₀ (=
  majorityAnswer for odd InSswap median, via InSswap.median_input_A).
GAP in the drain: timer_descent_to_one gives ≤1; the reset needs
timer=0 EXACTLY. No odd-n timer=1→0 single step exists
(step_at_median_max_no_swap_odd requires timer≥2). The clean 1→0 needs
a correct (answer=m₀) max-rank partner so propagate decrements without
firing the reset; if max-rank agent is wrong the 1→0 step resets at the
max agent instead (still a valid seed, but different shape). This
forbidden-rank / drain-corner case work is the genuine non-single-session
part, exactly as GPT rated it.

REMAINING HARD CORE (multi-session, no shortcut — verified from ~6 angles
+ GPT independent confirmation):
1. odd-n drain-to-exact-0 corner (timer=1 → 0 with right partner / handle
   reset-at-max variant);
2. all-Resetting+UNIFORM → InSswap ∧ ResAns re-rank (answer-overlay
   through input-opaque ranking — THE documented ~resetFuel-scale core);
3. even-n / tie path (mirror via committed trigger_correct_reset_from
   _InSrank_even + phase4_decide_even_boundary_tie_writes_outT);
4. hResetLeaf for cycle_macro_discharge (= the reservoir phi-decrease
   step under ResAns; same hard re-rank issue).
Steps 1,4 + the wrapper are bounded; step 2 is the genuine research core.

## 2026-05-16o — request-3 green, hNoTie blocker diagnosed

GPT request-3 lemmas now GREEN & pushed (commit e1bfee6e):
- step_at_median_max_timer_one_reset_fires_odd (7518): fixed
  `⟨trivial, h_max_wrong.symm⟩` (expected opinionToAnswer≠answer,
  had the flipped Ne).
- odd_timer_one_max_step_clean_or_seed (7656): fixed the all-Resetting
  branch — `rw [← hothers w hwμ hwv]; exact hw` (goal-direction; `hw`
  carried zeta-unfolded `Config.step P C μ v w`, not syntactic `C' w`,
  so `rw [hw_eq] at hw` couldn't match).

Build: only the single intended `sorry` remains (BurmanConvergenceFinal
:7843, hMedCorrectExit inside burmanConvergence_concrete:7764). 0 errors.

### Precise blocker for the final composition
cycle_macro_discharge (7293) takes `hNoTie : ∀ D, InSswap D →
nAOf D ≠ nBOf D` as a UNIVERSAL premise. But SolvesSSEM
(Defs/Execution.lean:48) is `∀ C₀, ...` over ALL C₀ incl. ties
(tie → outT consensus); burmanConvergence_concrete (7764) has NO
no-tie hyp. Cannot supply the universal premise.

Structural facts (confirmed): nAOf_add_nBOf (Silent.lean:51)
`nAOf+nBOf=n` ⇒ n odd ⇒ no-tie automatic; tie only at
nAOf=nBOf (n even). nAOf_step_eq/nBOf_step_eq (Step.lean:94/101):
nAOf/nBOf execution-invariant. reach_zero_potential_macro
(PotentialReach.lean:90) is fully Pinv-parametric → can absorb a
no-tie conjunct in Pinv. Tie ammo: trigger_correct_reset_from
_InSrank_even (1482, drops no-tie), decision_step_at_median_pair
_even_tie_decreases (DecisionTieCase:114), phase4_decide_even
_boundary_tie_writes_outT (6168).

Route (A2): replace universal hNoTie with a local entry no-tie +
invariance threaded through Pinv; tie branch handled by the _even
trigger to outT-consensus. Concrete Lean requested from GPT extended
Pro (channel exact-mj, brief covers A=hNoTie resolution, B=
med_correct_live_InSswap_to_reservoir_entry, C=reservoir_reset_leaf).

## 2026-05-16p — GPT (A) integrated; core isolated to 2 Props

GPT extended Pro confirmed (independent, repo access): the hNoTie
blocker is genuinely fixable from existing green lemmas; (B)/(C)
(entry-bridge + reset-leaf) are NOT derivable from green lemmas —
the real research core.

Integrated GPT's 4 supporting blocks before burmanConvergence_concrete:
- median_wrong_step_resAns_decrease_tieaware: no-tie branch delegates
  to median_wrong_step_resAns_decrease; even-tie branch via
  evenCase_witness_when_median_wrong_tie + decision_step_at_median
  _pair_even_tie_decreases + step_at_median_pair_even_disagreed_inputs
  + step_preserves_timer_no_max. All sigs verified pre-paste.
- cycle_macro_discharge_tieaware: cycle_macro_discharge minus the
  universal hNoTie premise (CASE 2a → tieaware variant).
- def MedCorrectLiveInSswapToReservoirEntry / def ReservoirResetLeaf:
  crisp Prop statements of the two genuine research auxiliaries.
- hMedCorrectExit_from_reservoir_entry_and_reset_leaf: non-circular
  composition closing hMedCorrectExit GIVEN the two Props (entry →
  phiCount split → cycle_potential_reaches_consensus via tieaware
  discharge → execution_concat).

The opaque hMedCorrectExit sorry is now reduced to exactly two
precisely-typed research targets. Final replacement NOT pasted yet
(references the still-unproved med_correct_live_InSswap_to_reservoir
_entry / reservoir_reset_leaf — would be unbound idents). Sorry count
unchanged (1) but architecture validated; next: prove (B)/(C).

## 2026-05-16q — research-core pieces largely exist (autonomous)

User: "继续自主证明,不要动不动就停下来等我" → autonomous drive.

Build bb3ccby6c verifying GPT (A) blocks (in-flight). Dispatched
focused GPT brief b49tbdjkm for (B)/(C) concrete proofs with exact
ammo sigs.

Independent discovery while build/GPT run:
- exists_answer_safe_misordered_pair (BCF:6908, GREEN, axiom-clean)
  ≈ the hSelect slot of all_resetting_uniform_to_InSswap_ResAns_weak,
  modulo extra hyps hm:m₀=majorityAnswer D and hTimer:∀μ med 2≤timer.
  So hSelect is ~done; gap = discharging hm (majorityAnswer invariant,
  runPairs-stable) + hTimer (2≤median timer mid-ranking — needs the
  fresh-ranking timer-init fact).
- recruit_step_preserves_ResAns_if_decision_safe (BCF:3922) = the
  hTreeW (recruit) analogue.
- PairResAnsSafe_of_{even_boundary_tie, even_lower_nonboundary_Amajor,
  even_v_lower_Bmajor, odd_lower_median_Amajor, odd_upper_median_Bmajor}
  (BCF:6973-7036) = the per-case PairResAnsSafe building blocks.

So the research core is NOT a missing theorem — it is the GLUE:
compose (timer-drain → reset trigger → all_resetting_from_seed →
all_resetting_uniform_to_InSswap_ResAns_weak with hSelect:=
exists_answer_safe_misordered_pair, hTreeW:= recruit lemma) into one
∃γt with a resetFuel/phiCount decreasing measure. GPT b49tbdjkm
tasked with exactly this composition.

## 2026-05-16r — GPT round 2: hTreeW FALSE, core = 3 Props

GPT extended Pro (br0j5xv0y, full 10.8KB reply, repo access)
INDEPENDENTLY CONFIRMS: the all_resetting_uniform_to_InSswap_ResAns
_weak hTreeW route is GENUINELY FALSE — median-recruit fires
phase4_decide writing opinionToAnswer((D child).2) which ≠ m₀ in
general, so the answer-preservation conjunct of hTreeW is
unsatisfiable. (Matches our ~6-way-verified obstruction.)

GPT factors the ENTIRE remaining research core into 3 precisely-typed
Prop obligations, with ALL composition given as concrete GREEN-ONLY
Lean (uses only all_resetting_from_seed_answer_aux,
majorityAnswer_runPairs_eq, exists_schedule_after_runPairs):

  1. AllResettingUniformToInSswapResAnsPhiZero — end-to-end uniform
     all-Resetting → InSswap ∧ ResAns ∧ phiCount=0, WITHOUT
     per-recruit answer preservation (the irreducible core: Kanaya
     self-stabilization re-entry).
  2. MedCorrectLiveProducesCorrectSeed — entry-bridge finite prefix
     (timer-drain + reset trigger → correct Resetting seed).
  3. ReservoirCaseProducesCorrectSeed — reset-leaf finite prefix
     (median-correct ∨ median-timer-0, incl. median=.phi).

Concrete green composition theorems GPT supplied (paste-ready, take
the 3 Props as hyps):
  - correct_reset_seed_to_InSswap_ResAns_phi_zero
  - med_correct_live_InSswap_to_reservoir_entry_from_seed_and_reentry
  - reservoir_reset_leaf_from_seed_and_reentry
  - med_correct_live_InSswap_to_reservoir_entry / reservoir_reset_leaf
    (reduce to the 3 Props).

STATUS: the opaque sorry is now maximally factored into 3 sharp,
well-typed research lemmas; everything else is concrete green. The 3
Props are genuine new mathematical content (multi-session research),
not closeable by one build cycle. Next: integrate the green
composition layer (after bb3ccby6c (A)-verify clears), then attack
the 3 Props (self-drive + GPT parallel).

## 2026-05-16s — round-2 layer integrated; frontier = 3 Props

Committed/pushed milestones this session:
- e1bfee6e request-3 lemmas GREEN
- 6292a2c4 nAOf/nBOf_execution_eq GREEN
- 5431eefb GPT (A) tie-aware hNoTie resolution GREEN (build rc=0,
  universal-hNoTie blocker ELIMINATED, only intended sorry remains)

Integrated GPT round-2 green composition layer (building bqcwkqq1x):
AllResettingUniformToInSswapResAnsPhiZero / MedCorrectLiveProduces
CorrectSeed / ReservoirCaseProducesCorrectSeed Props +
correct_reset_seed_to_InSswap_ResAns_phi_zero + the two
_from_seed_and_reentry reducers (all green-ammo: all_resetting
_from_seed_answer_aux, majorityAnswer_runPairs_eq, exists_schedule
_after_runPairs). Single existing hMedCorrectExit sorry unchanged
(NOT wired to round-2 — would need the 3 unproven Props).

RESEARCH FRONTIER (was 1 opaque sorry → now 3 crisp typed Props,
all glue proven green):
  #1 AllResettingUniformToInSswapResAnsPhiZero — irreducible
     uniform-all-Resetting re-entry WITHOUT per-recruit answer
     preservation (false hTreeW route). GPT bvf7as7u4 dispatched.
  #2 MedCorrectLiveProducesCorrectSeed — entry-bridge timer-drain
     +reset-trigger prefix. Ammo: timer_descent_to_one (odd, TDNS:231),
     step_at_median_timer_zero_reset_fires (odd, TDNS:309),
     odd_timer_one_max_step_clean_or_seed (GREEN, BCF:7656),
     trigger_correct_reset_from_InSrank(_even). NOTE: TDNS lemmas are
     odd-only (hpar:¬n%2=0); even path needs separate route → NOT
     trivial, genuine composition.
  #3 ReservoirCaseProducesCorrectSeed — same machinery under ResAns,
     median-correct ∨ median-timer-0 (incl. median=.phi) split.

All 3 are genuine multi-session research (GPT×2 + independent
analysis converged). Per feedback_multiweek_incremental this is
month-scale; steady incremental: structure maximally sharpened,
glue green, GPT on the hardest Prop.

## 2026-05-16t — Prop #2 sub-blocker pinpointed

Self-analysis of MedCorrectLiveProducesCorrectSeed (#2) vs the green
ammo trigger_correct_reset_from_InSrank (BCF:1253):

trigger needs: InSswap C, μ med, v with rank+1 ∉{ceilHalf n,n,n/2+1},
μ.timer=0, nAOf≠nBOf, μ.answer=majorityAnswer, v.answer≠majorityAnswer
→ produces EXACTLY the Prop #2 seed shape.

Gap from Prop #2 hyps to trigger preconditions:
1. μ med + median-correct ⇒ μ.answer=majorityAnswer ✓ (hMedCorrect).
2. exists_wrong_nonmedian_of_med_correct ⇒ v wrong, rank+1≠ceilHalf n ✓;
   but v.rank+1≠n and ≠n/2+1 NOT guaranteed — need a v-selection
   that also dodges max/upper, or case-handle those.
3. μ.timer=0 — Prop #2 GIVES median timer ≥1 (timer-live). Must DRAIN
   to exactly 0. THIS is the irreducible sub-core: timer_descent_to
   _one (TDNS:231, ODD-only hpar, needs 2≤timer + max-rank partner +
   μ.input=.A) gets ≥2→≤1; the timer=1 corner is odd_timer_one_max
   _step_clean_or_seed (GREEN, disjunctive: clean timer=0+InSswap OR
   the seed directly). The "clean timer=0" arm may be unreachable in
   general — the seed arm is the actual escape. Splicing the
   timer-drain `execution` prefix into the `runPairs` L of trigger is
   the unsolved glue.
4. nAOf≠nBOf: odd n ⇒ auto (nAOf_add_nBOf). even n ⇒ tie possible →
   trigger_correct_reset_from_InSrank_even (drops hne).

CONCLUSION: Prop #2 is NOT a mechanical reduction — the timer-drain
to-exactly-0 + execution/runPairs splice IS genuine research core
(same family as #1). All 3 Props are irreducible (matches GPT×2).
This is multi-session per feedback_multiweek_incremental. Steady
incremental state: 4 green commits, opaque sorry → 3 crisp Props,
false hTreeW route ruled out 2× independently, sub-blockers
pinpointed. GPT bvf7as7u4/bf5qdvk47 (auto-retrying bridge) actively
producing the 3 Prop proofs; integrate on landing.

## 2026-05-16u — Prop #1 definitively irreducible (GPT timed out)

GPT extended Pro on Prop #1 (bvf7as7u4): TIMED OUT after 1190s, no
usable answer. bf5qdvk47 (Props #2+#3) still in flight.

Verified the non-weak route: all_resetting_uniform_to_InSswap_ResAns
(BCF:4298) is itself GREEN but only MODULO hRecruit+hSelect (it
composes all_resetting_uniform_to_fresh_start_ResAns +
exists_safe_ranking_and_swap_schedule, both parameterized by
hRecruit/hSelect). hSelect ≈ exists_answer_safe_misordered_pair
(6908, green, mod hm+hTimer). BUT hRecruit requires per-recruit
answer preservation = the SAME false obligation GPT round-2 ruled
out (median-recruit phase4_decide writes opinionToAnswer(input)≠m₀).
So the non-weak route is ALSO blocked by the identical false
hRecruit. Confirmed 2× independently + GPT round-2 explicit.

DEFINITIVE: Prop #1 AllResettingUniformToInSswapResAnsPhiZero is the
irreducible Kanaya self-stabilization re-entry. NOT closeable from
existing green lemmas via ANY route (weak hTreeW = false; non-weak
hRecruit = same false; direct = the research core). Requires NEW
mathematics: the resetcount/resetFuel well-foundedness that absorbs
the median-recruit transient through a SECOND reset cycle. GPT
extended Pro (strongest available tool) times out on it.

This is genuinely month-scale research (feedback_multiweek
_incremental, project_pp_to_nap_gap). Session result: maximal
sharpening achieved — 5 green commits (e1bfee6e, 6292a2c4,
5431eefb, 2d326007, CHECKPOINTs), opaque sorry → 3 crisp typed
Props with ALL glue proven green, false route ruled out, GPT (A)
tie-aware hNoTie resolution integrated green. The single remaining
sorry = the 3 research Props, of which #1 is the irreducible core.
Re-dispatching the timed-out GPT query is futile; this needs a
research breakthrough across sessions.

## 2026-05-16v — disjunctive repair integrated (GPT round-3 breakthrough)

GPT round-3 (bf5qdvk47) PROVED the pure-seed Props #2/#3 FALSE:
even-n upper-median-only wrong/.phi counterexample — phase4_decide
runs before phase4_propagate, even decision step overwrites both
median answers so propagation reset guard never fires; no seed
forced. trigger_correct_reset_from_InSrank_even excludes upper
median (rank+1≠n/2+1); exists_wrong_nonmedian_of_med_correct witness
can BE that excluded upper median. Same "stuck=false statement"
pattern as the prior 4 over-strong bugs.

Integrated GPT's minimal repair (disjunctive seed-OR-progress):
- def CorrectResetSeed (C) — seed predicate factored out.
- MedCorrectLiveProducesCorrectSeedOrProgress: ∃ L, CorrectResetSeed
  C' ∨ (InSswap C' ∧ ResAns C') — progress branch = entry conclusion.
- ReservoirCaseProducesCorrectSeedOrProgress: ∃ L, CorrectResetSeed
  C' ∨ (InSswap C' ∧ ResAns C' ∧ phiCount C' < phiCount D) —
  progress branch = EXACTLY ReservoirResetLeaf conclusion.
- Both reducers re-derived: rcases the disjunct; seed→green
  correct_reset_seed_to_InSswap_ResAns_phi_zero; progress→
  exists_schedule_after_runPairs with (fun _=>default, 0).
  hReentry (Prop #1) now only used in the SEED branch.

Building bm7ztm40t (verify reducers+composition still green, single
sorry unchanged). Dispatched bb106cg96: GPT proving the now-TRUE
disjunctive Props (non-upper wrong→trigger; even-upper-median→
decision_step_at_median_pair_even_tie_decreases direct progress).

Net: the false/impossible seed-prefix blocker → TRUE tractable
disjunctive Props. Research frontier now: Prop #1 (re-entry,
irreducible, GPT times out) + the now-true #2'/#3' (GPT-tractable).
6+ green commits; opaque sorry maximally factored & corrected.

## 2026-05-16w — FOUND THE FORMULATION BUG (Prop #1 over-strong)

User pushed back: stop declaring it hard, find the formulation bug
(the project's recurring "证不过去先查定义" — 5 over-strong bugs
already found this way). Did the analysis:

AllResettingUniformToInSswapResAnsPhiZero (8027) demands from a
UNIFORM all-Resetting start (all role=.Resetting, all answer=m₀=
majorityAnswer C):  InSswap E ∧ ResAns (majorityAnswer E) E ∧
phiCount E = 0.  Two compounding defects:

(1) phiCount is the WRONG potential. At uniform all-Resetting every
answer = m₀ ≠ .phi, so phiCount C = 0 ALREADY, while the config is
NOT consensus (all .Resetting, ¬InSswap). phiCount cannot measure
reset-cycle progress; this forces the re-entry to demand the
over-strong phiCount E = 0 (= full consensus in ONE re-entry, via
isConsensusConfig_of_InSswap_phiCount_zero: phiCount=0 ∧ ResAns ∧
InSswap ⟹ IsConsensusConfig).

(2) That conjunction is UNSATISFIABLE: rankDeltaOSSR binary-tree
re-ranking makes the median-rank recruit fire phase4_decide writing
answer := opinionToAnswer(recruit.input) — a concrete value ∉
{m₀,.phi} generally. So median agent violates ResAns(majorityAnswer
E) E at the InSswap endpoint. (Same over-strong class as the prior
5 bugs; ResAns def 2124 = ∀w, answer=m ∨ answer=.phi.)

CORRECT measure = resetcount/resetFuel (Kanaya self-stabilization),
NOT phiCount — matches GPT round-2 "resetFuel well-foundedness".
The architecture threading InSswap∧ResAns∧phiCount + recursing on
phiCount is structurally wrong for the median-correct reset path.
The reset cycle's progress is the bounded resetcount draining
(reservoir), invisible to phiCount.

NEXT: re-formulate the reset-cycle re-entry around a resetFuel /
resetcount measure (decreasing across full reset cycles), replacing
the phiCount=0 over-strong conclusion. Consult ChatGPT on the
correct resetFuel formulation + Lean. (Bridge tab was returning
garbage — needs reset/recheck.)

## 2026-05-16x — REFRAME: this is formalization-debugging, NOT research

User correction (firm, correct): this formalizes Kanaya et al.'s
CORRECT published proof. "证明不过去通常不是因为问题有多难" — proofs
not closing = OUR statement has a bug, not hard math. We've done far
harder. Stop the "irreducible research / 撼不动" framing — there is
no such thing here.

CRITICAL MISCONCEPTION CORRECTED: for ~4 GPT rounds I treated
"median-recruit writes opinionToAnswer(arbitrary input) ≠ m₀" as an
unbreakable obstruction. It is NOT. opinionToAnswer_median_eq
_majorityAnswer_odd (DecisionReach:178) and _lower_median_eq
_majorityAnswer_even (DecisionReach:134) PROVE: at ANY InSswap
config the median agent's decided answer = majorityAnswer, because
InSswap.input_rank forces the median-RANK agent to hold the median
INPUT, and opinions/majorityAnswer are execution-invariant. The
re-ranking recruit transient is irrelevant — the FINAL InSswap is
necessarily correct at the median.

⟹ Prop #1 (AllResettingUniformToInSswapResAnsPhiZero) is almost
certainly TRUE and a COMPOSITION task. The real bug is the
over-strong/ill-typed-potential conclusion phiCount E = 0 (phiCount
is already 0 at uniform all-Resetting since all answers = m₀ ≠ .phi,
so it cannot measure progress; full-consensus-in-one-re-entry is the
wrong target). Likely corrected Prop: reach InSswap ∧ ResAns
(majorityAnswer E) E (drop phiCount=0); the OUTER cycle_potential
_reaches_consensus phiCount strong-recursion drives phiCount→0.

Bridge: user fixed it, channel renamed exact-mj → "family". Ping
OK-EXACTMJ confirmed. Bug brief /tmp/ssem_gpt_bug2.txt dispatched
(bxm5is2ii) asking ChatGPT to confirm Prop #1 true + give the
concrete composition via all_resetting_uniform_to_InSswap_ResAns
(4298 GREEN non-weak) with hSelect:=exists_answer_safe_misordered
_pair, hRecruit via opinion-invariance (NOT per-step preservation),
OR the corrected Prop dropping phiCount=0 + re-composed chain.

8 green commits stand. Frontier reframed: a composition/statement
fix, not research.

## 2026-05-16y — GPT full analysis: Prop #1 TRUE, proof route = structural recruit + endpoint repair

GPT full analysis (channel family, pasted by user) confirms:
- AllResettingUniformToInSswapResAnsPhiZero (= NoPhi, equivalent via
  phiCount_eq_zero_iff) STATEMENT is TRUE. phiCount=0 achievable
  because: non-median recruits preserve answers (m₀); median-recruit
  fires phase4_decide but at final InSswap opinionToAnswer_median_eq
  _majorityAnswer corrects it.
- PROOF ROUTE: cannot use theorem 4298 (non-weak) directly — its
  hRecruit demands per-step PairResAnsSafe which median-recruit
  violates. Cannot use 5546 (weak) directly — its hTreeW demands
  per-recruit answer preservation which median-recruit violates.
- FIX: use STRUCTURAL RecruitFrontierSelector (like 5546 hTreeW but
  WITHOUT the two answer-preservation conjuncts) + a separate
  RankingSwapEndpointRepairsResAns theorem that re-establishes
  ResAns∧NoPhi at the InSswap endpoint via opinionToAnswer_median
  _eq_majorityAnswer (decision re-derives correct median answer) +
  the fact non-median answers are preserved (their recruit steps
  DON'T fire phase4_decide, verified in transitionPEM_phase4).
- hSelect: discharged via green exists_answer_safe_misordered_pair
  (6908) by threading hm := majorityAnswer_runPairs_eq and hTimer
  via swap-timer lemmas.
- For ReservoirResetLeaf seed branch: need NoPhi (= phiCount=0)
  re-entry, not just weak InSswap∧ResAns. So use the strong NoPhi
  prop (proven by the structural recruit + endpoint repair route).

CONCRETE NEXT STEP: prove AllResettingUniformToInSswapResAns[NoPhi]
via: (1) a structural RecruitFrontierSelector for ALL ranks (incl.
median — the structural properties (child becomes Settled, gets
target rank, measure decreases) hold for ALL recruits including
median; only ANSWER changes at median, which isn't in the structural
selector). (2) RankingSwapEndpointRepairsResAns: from
FreshRankingStart with uniform m₀, the swap+decision phase produces
InSswap with ResAns∧NoPhi — using majorityAnswer invariance +
opinionToAnswer_median correct + non-median answers preserved. This
is a well-defined COMPOSITION task with existing green ammo.
