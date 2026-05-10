# SSExactMajority — Lean 4 Formalization

A Lean 4 / Mathlib formalization of the population-protocol results in:

> **Time- and Space-Optimal Silent Self-Stabilizing Exact Majority in
> Population Protocols.**
> Daiki Kanaya, Daiki Eguchi, Hayato Sasada, Fukuhito Ooshita, Michiko Inoue.
> arXiv:2503.17652, SSS 2025.

## Status

- **Build**: clean (`lake build`).
- **Axioms**: all theorems depend only on `propext`, `Classical.choice`,
  `Quot.sound` (verified via `lake env lean SSExactMajority/AxiomCheck.lean`).
- **No `sorry` and no extra axioms** anywhere in the source.

## Mapping to paper

| Paper | Statement | Lean theorem | File |
|-------|-----------|---------------|------|
| Theorem 1 | No protocol solves SSEM for all n without knowing n | `impossibility_without_n` | `Impossibility/WithoutN.lean` |
| Theorem 2 | Silent SSEM protocol needs ≥ n states | `space_lower_bound` | `LowerBound/Space.lean` |
| Lemma 4 | A-agents have distinct states under silence | `silent_config_A_agents_distinct` | `LowerBound/Space.lean` |
| Lemma 4B | B-agents have distinct states under silence | `silent_config_B_agents_distinct` | `LowerBound/Space.lean` |
| Lemma 5 | A-agent ≠ B-agent states (input-oblivious) | `silent_config_AB_distinct` | `LowerBound/Space.lean` |
| Theorem 3 | Ω(n log n) parallel time lower bound | (stub) | `LowerBound/Time.lean` |
| Algorithm 1 | P_EM transition function | `transitionPEM` | `Protocol/Transition.lean` |
| §5.1 / §5.2 | Convergence of P_EM (qualitative) | `P_EM_solves_SSEM_full_modulo_burman` | `Convergence/MasterModuloBurman.lean` |
| §5.1 / §5.2 | Maximally discharged form | `P_EM_solves_SSEM_fully_discharged_modulo_burman` | `Convergence/MedianWitnesses.lean` |
| §5.2 quantitative | O(n log n) parallel time bound | (out of scope) | — |

## Convergence chain (qualitative)

The proof of `Theorem 4` factors through the configuration-set hierarchy
of Kanaya §5.2.1:

```
  Init  ⟹  InSrank  ⟹  InSswap  ⟹  IsConsensusConfig
        (ranking)   (swap)       (decision)
```

Each phase is given a deterministic-scheduler reachability hypothesis,
which is then reduced to a local single-step decreasing-potential lemma
via `PotentialReach`.  The unified single-step lemma covers eight
sub-cases by misorder pair structure (see CHECKPOINT.md "Swap-step
single-step coverage matrix").

## Residual gaps

The maximally discharged Theorem 4 (`P_EM_solves_SSEM_fully_discharged_modulo_burman`)
takes the following parameters as external assumptions:

1. **Burman 2021 PODC ranking convergence** (`h_burman_ranking`) — a
   separate paper's main result; treated as an axiom-free hypothesis.
2. **`BurmanMacroDecision`** — the macro-step trajectory through the
   reset cycle when the median is correct but some non-median agent is
   wrong.  Captures Phase A+B+C of the macro-step plan as a single
   bundled hypothesis.
3. **Strict majority** (`hStrictMajority`) — needed for even-n decision
   pair to write the correct majority answer.
4. **Two structural timer invariants** (`h_inv_swap`, `h_inv_dec`) —
   intermediate states in the reachability chain have median timer
   bounded below appropriately.

See `WORK_LOG.md` for the deferred work needed to discharge each.

## Files

```
SSExactMajority/
├── Defs/                       — Protocol, Config, Execution, ExactMajority
├── Embed.lean                  — Execution embedding lemma
├── Impossibility/WithoutN.lean — Theorem 1
├── LowerBound/
│   ├── Space.lean              — Theorem 2 + Lemmas 4, 4B, 5
│   └── Time.lean               — Theorem 3 stub
├── Protocol/
│   ├── State.lean              — AgentState (Role, Leader, Answer, rank, timer, …)
│   ├── Transition.lean         — Algorithm 1 encoding
│   └── Correctness.lean        — Structural lemmas
└── Convergence/
    ├── Silent.lean             — IsConsensusConfig, majorityAnswer
    ├── AnswerPreservation.lean — Answer preserved at consensus
    ├── StatePreservation.lean  — Role/rank preserved at consensus
    ├── Step.lean               — Step preserves consensus
    ├── Theorem4.lean           — Conditional Theorem 4 (early form)
    ├── Sets.lean               — Srank/Sswap/Sout/Stim/Sem
    ├── Schedule.lean           — Scheduler composition
    ├── Composition.lean        — Phase reachability composition
    ├── SwapPhase.lean          — misorderedCount potential
    ├── PotentialReach.lean     — Generic potential-reach lift
    ├── SwapReach.lean          — hSwapPhase via single-step
    ├── DecisionReach.lean      — hDecisionPhase via single-step (incl. odd/even median lemmas)
    ├── SwapStep.lean           — Non-median swap-step single-step
    ├── TrivialBase.lean        — Base case
    ├── NonMedianExistence.lean — Non-median misorder existence helpers
    ├── SwapStepTimer.lean      — Timer-positive swap-step
    ├── Final.lean              — Master statements (early forms)
    ├── RankPreservation.lean   — 8-way swap-step coverage (u-at-median cases)
    ├── TimerDescent.lean       — medianTimer + descent at v-at-max
    ├── ResetCycle.lean         — Reset firing at timer = 0
    ├── MasterModuloBurman.lean — Theorem 4 modulo Burman (D1/D2/D3)
    ├── MedianWitnesses.lean    — E1/E2 witnesses + fully-discharged Theorem 4
    └── SwapVMedian.lean        — v-at-median + 8-way unified swap-step
```

## CHECKPOINT.md

See `CHECKPOINT.md` for the complete list of proved theorems with one-line
descriptions.  See `WORK_LOG.md` for deferred items and structural notes.
