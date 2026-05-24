# SSExactMajority — Lean 4 Formalization

A Lean 4 / Mathlib formalization of the population-protocol results in:

> **Time- and Space-Optimal Silent Self-Stabilizing Exact Majority in
> Population Protocols.**
> Daiki Kanaya, Daiki Eguchi, Hayato Sasada, Fukuhito Ooshita, Michiko Inoue.
> arXiv:2503.17652, SSS 2025.

The convergence proof uses the OPTIMAL-SILENT-SSR ranking subprotocol of

> **Burman, Doty, Nowak, Severson, Xu.**
> *Self-stabilizing population protocols with global knowledge.*
> PODC 2021.

which is formalized here as well.

## Status (2026-05-18)

- **Build**: clean (`lake build` for the root library + `lake build
  SSExactMajority.Convergence.BurmanConvergenceFinal
  SSExactMajority.Convergence.EndpointRepair` for the composition modules).
- **`sorry`**: zero in the entire source tree.
- **Custom axioms**: zero. Every theorem depends only on
  `[propext, Classical.choice, Quot.sound]` — verified via
  `#print axioms SSEM.P_EM_solves_SSEM_final` and
  `SSExactMajority/AxiomCheck.lean`.
- **Ultimate theorem**: `SSEM.P_EM_solves_SSEM_final` — for every `n ≥ 4`
  the concrete protocol `protocolPEM n n n (rankDeltaOSSR n Emax Dmax hn)`
  solves SSEM. **No external hypotheses.**

## What is done

| Paper | Statement | Lean theorem | File |
|-------|-----------|---------------|------|
| Theorem 1 | Impossibility without knowing `n` | `impossibility_without_n` | `Impossibility/WithoutN.lean` |
| Theorem 2 | Silent SSEM protocol needs ≥ `n` states | `space_lower_bound` | `LowerBound/Space.lean` |
| Lemma 4 | A-agents have distinct states under silence | `silent_config_A_agents_distinct` | `LowerBound/Space.lean` |
| Lemma 4B | B-agents have distinct states under silence | `silent_config_B_agents_distinct` | `LowerBound/Space.lean` |
| Lemma 5 | A-agent ≠ B-agent states | `silent_config_AB_distinct` | `LowerBound/Space.lean` |
| Algorithm 1 | P_EM transition function | `transitionPEM` | `Protocol/Transition.lean` |
| §5.1 / §5.2 (qualitative) | Concrete-protocol convergence | **`P_EM_solves_SSEM_final`** | `Convergence/BurmanConvergenceFinal.lean` |
| Burman §3 (ranking) | OPTIMAL-SILENT-SSR converges (deterministic) | `ranking_field_proof` | `Convergence/BurmanConvergenceFinal.lean` |

`P_EM_solves_SSEM_final` is built unconditionally on:

- `ranking_field_proof` — Burman 2021 ranking convergence (was a hypothesis
  in the historical `P_EM_solves_SSEM_fully_discharged_modulo_burman`; now a
  proved theorem).
- `burmanConvergence_concrete` — full `BurmanConvergence` instance composing
  ranking + epidemic + decision.
- `epidemic_timer_branch_to_consensus` — median-correct / reservoir
  case-split via the disjunctive seed-or-progress lemmas.

The four historical "residual gaps" (`h_burman_ranking`, `BurmanMacroDecision`,
`hStrictMajority`, `h_inv_swap` / `h_inv_dec`) are all discharged inside
`P_EM_solves_SSEM_final`'s call chain.

## What is NOT done — the "time-optimal" half

The paper's title claims **time- AND space-optimal**.  Only the **space**
side is formalized.  The **time** side requires a probability framework not
yet in this project.

| Paper | Statement | Status |
|-------|-----------|--------|
| Theorem 3 | Any silent SSEM protocol requires Ω(n log n) expected parallel time | **scaffold only** (`LowerBound/Time.lean`) |
| §5.2 quantitative | P_EM converges in O(n log n) expected parallel time | **scaffold only** (`UpperBound/Time.lean`) |

The deterministic existential convergence proved in `P_EM_solves_SSEM_final`
states "there exists a scheduler reaching consensus" — it says nothing about
the *expected time* under the uniform-random pair-selection scheduler used
to measure parallel time in the population-protocol model.

The skeleton for the missing pieces is in:

- `Probability/RandomScheduler.lean` — uniform random pair selection
- `Probability/ExpectedTime.lean` — expected hitting time on configurations
- `LowerBound/Time.lean` — `Theorem 3` statement
- `UpperBound/Time.lean` — P_EM upper bound statement
- `docs/TIME_BOUND_PLAN.md` — design notes for the probability layer

## Convergence chain (qualitative)

```
  Init  ⟹  InSrank  ⟹  InSswap  ⟹  IsConsensusConfig
        (ranking)   (swap)       (decision)
```

- Phase A (ranking): `ranking_field_proof`
- Phase B (swap): `swap_reaches_Sswap_from_timer_bound_with_timer`
- Phase C (decision): disjunctive seed-or-progress core of
  `BurmanConvergenceFinal.lean`
- Reset-cycle re-entry from wrong-answer configurations: strong recursion on
  `phiCount` (`cycle_potential_reaches_consensus`)

## Files

```
SSExactMajority/
├── Defs/                       — Protocol, Config, Execution, ExactMajority
├── Embed.lean                  — Execution embedding lemma
├── Impossibility/WithoutN.lean — Theorem 1
├── LowerBound/
│   ├── Space.lean              — Theorem 2 + Lemmas 4, 4B, 5
│   └── Time.lean               — Theorem 3 (scaffold)
├── UpperBound/
│   └── Time.lean               — §5.2 quantitative (scaffold)
├── Probability/
│   ├── RandomScheduler.lean    — Uniform pair-selection model (scaffold)
│   └── ExpectedTime.lean       — Expected parallel time (scaffold)
├── Protocol/
│   ├── State.lean              — AgentState (Role, Leader, Answer, rank,
│   │                              timer, resetcount, children, errorcount,
│   │                              delaytimer — Burman fields)
│   ├── Transition.lean         — Algorithm 1 (4 phases)
│   ├── Correctness.lean        — Structural lemmas
│   └── RankDelta.lean          — OPTIMAL-SILENT-SSR concrete protocol
│                                 (rankDeltaOSSR), Burman 2021 Protocols 2/3/4
└── Convergence/
    ├── Silent.lean             — IsConsensusConfig, majorityAnswer
    ├── AnswerPreservation.lean — Answer preserved at consensus
    ├── StatePreservation.lean  — Role/rank preserved at consensus
    ├── Step.lean               — Step preserves consensus
    ├── Theorem4.lean           — Conditional Theorem 4 (historical)
    ├── Sets.lean               — Srank/Sswap/Sout/Stim/Sem
    ├── Schedule.lean           — Scheduler composition
    ├── Composition.lean        — Phase reachability composition
    ├── SwapPhase.lean          — misorderedCount potential
    ├── PotentialReach.lean     — Generic potential-reach lift
    ├── SwapReach.lean          — hSwapPhase via single-step
    ├── DecisionReach.lean      — hDecisionPhase + odd/even median lemmas
    ├── SwapStep.lean           — Non-median swap-step single-step
    ├── TrivialBase.lean        — Base case
    ├── NonMedianExistence.lean — Non-median misorder existence helpers
    ├── SwapStepTimer.lean      — Timer-positive swap-step
    ├── Final.lean              — Master statements (historical)
    ├── RankPreservation.lean   — 8-way swap-step coverage (u-at-median)
    ├── TimerDescent.lean       — medianTimer + descent at v-at-max
    ├── ResetCycle.lean         — Reset firing at timer = 0
    ├── MasterModuloBurman.lean — Theorem 4 modulo Burman (historical)
    ├── MedianWitnesses.lean    — E1/E2 witnesses + fully-discharged
    │                              Theorem 4 (historical)
    ├── SwapVMedian.lean        — v-at-median + 8-way unified swap-step
    ├── EvenNComplete.lean      — Even-n completion
    ├── MacroStepComposition.lean — Macro-step plumbing
    ├── DecisionTieCase.lean    — Even-tie direct progress
    ├── TimerDescentNoSwap.lean — Odd timer ≥ 2 → ≤ 1
    ├── BurmanProperties.lean   — Structural lemmas for Burman fields
    ├── BurmanProof.lean        — Burman 2021 ranking-convergence machinery
    ├── BurmanConvergenceFinal.lean
    │                            — Composition layer:
    │                              `ranking_field_proof`,
    │                              `burmanConvergence_concrete`,
    │                              `P_EM_solves_SSEM_final`
    └── EndpointRepair.lean     — Even-n endpoint-repair recruit lemma
```

## Reproducing the build

```bash
# Root library (everything Theorem 2 etc. need):
lake build

# Composition modules (`P_EM_solves_SSEM_final` lives here):
lake build SSExactMajority.Convergence.BurmanProof \
           SSExactMajority.Convergence.BurmanConvergenceFinal \
           SSExactMajority.Convergence.EndpointRepair

# Print axioms of the ultimate theorem:
lake env lean SSExactMajority/Convergence/BurmanConvergenceFinal.lean | \
  grep "P_EM_solves_SSEM_final"
```

A clean full build on uisai1 (32 cores, 251 GB RAM) takes ~5 minutes.

## Documents

- `CHECKPOINT.md` — historical theorem inventory; the "Current state
  (2026-05-18)" section at top is the live status.
- `WORK_LOG.md` — session-by-session work log.
- `UNDERSTANDING.md` — working context; "Current state" section at top.
- `docs/TIME_BOUND_PLAN.md` — design plan for the unfinished time-bound half.
