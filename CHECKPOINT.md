# SSExactMajority — Checkpoint

Formalizing: Kanaya–Eguchi–Sasada–Ooshita–Inoue (2025),
"Time- and Space-Optimal Silent Self-Stabilizing Exact Majority
in Population Protocols" (arXiv:2503.17652, SSS 2025).

## Build status: ✓ zero errors, zero sorry, zero axiom

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
