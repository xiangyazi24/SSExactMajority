# Epidemic Field — Strategy & Reconnaissance

Status: LAST remaining sorry. `burmanConvergence_concrete.epidemic`
(BurmanConvergenceFinal.lean ~line 1356). All ranking sorries CLOSED
(commit 7d03f6cf).

## Goal (from BurmanProperties.lean:60-68)

```
epidemic : ∀ C₀, (∃ w, (C₀ w).1.answer = majorityAnswer C₀) →
  ∃ γ t, InSswap (execution P C₀ γ t) ∧
    (∀ w, (execution P C₀ γ t w).1.answer = majorityAnswer C₀) ∧
    (∀ μ at median, 1 ≤ (execution P C₀ γ t μ).1.timer)
```

## Mechanism (Protocol/Transition.lean)

1. **Wipe-on-entry** (transitionPEM_prePhase4 L37-42): an agent NEWLY
   entering Resetting gets `answer := .phi`. Already-Resetting agents
   keep their answer. This is the crux subtlety — the correct-answer
   holder can be wiped if it enters Resetting from non-Resetting.

2. **Phi-spread** (transitionPEM_prePhase4 L49-56): when BOTH agents
   Resetting, if exactly one is `.phi`, it copies the other's answer.
   This is the epidemic propagation.

3. **Decision write** (phase4_decide L65-78): median agent(s) write
   `opinionToAnswer x` — re-derives the answer from the opinion
   distribution after re-ranking.

## Reusable building blocks (verified present, 0 sorry)

- `majorityAnswer_step_eq` / `majorityAnswer_execution_eq`
  (Step.lean:109,173) — majorityAnswer is invariant. KEY.
- `step_preserves_consensus` / `execution_preserves_consensus`
  (Step.lean:117,159).
- `transitionPEM_consensus_pair_answer{,_eq}`
  (AnswerPreservation.lean:254,356).
- `swap_reaches_Sswap_from_timer_bound_with_timer`
  (SwapFromRanking.lean:497) — InSrank + timer≥2@median → InSswap +
  timer≥1@median. Does NOT track answers.
- `InSrank_reaches_RankingEndpoint_or_InSswap` (BurmanProof.lean:11627).
- Normalizer (now CLOSED): `partial_resetting_to_known_entry`,
  `all_resetting_from_seed_aux`, `reach_known_entry_from_any`,
  `ranking_field_proof` — can drive ANY config to InSrank (or the
  6-way KnownRankingEntry).

## Gap

No composed "answer becomes correct everywhere" theorem exists.
FORMALIZATION_GAPS.md §3c marks epidemic "Not started". The
opinion field `(C w).2` is the ground truth; `majorityAnswer` is
defined from opinion counts and is execution-invariant. The decision
phase re-derives `answer` from opinion at the median. So the real
content is:

> After re-ranking to InSrank, run the swap+decision phases; the
> median decision writes `opinionToAnswer` which equals
> `majorityAnswer C₀` (because opinion counts are invariant), and
> the swap phase spreads it. The "∃ correct answer" hypothesis is
> actually used to rule out the tie/outT branch.

## Candidate proof skeleton

1. From C₀, `ranking_field_proof` → ∃ γ₁ t₁, InSrank C₁ ∧
   (timer≥2@median ∨ consensus).
2. If consensus: `execution_preserves_consensus` +
   `IsConsensusConfig.allAnswerCorrect` → all answers already
   = majorityAnswer; need InSswap too (consensus ⊂ InSswap? check
   `InSswap_of_...`). majorityAnswer invariant closes the answer goal.
3. Else timer≥2@median: `swap_reaches_Sswap_from_timer_bound_with_timer`
   → InSswap + timer≥1@median. Then need: at InSswap reached this
   way, all answers = majorityAnswer. This is the missing lemma —
   likely provable from the decision-phase median-write +
   opinion-invariance + the ∃-correct hypothesis ruling out tie.

The missing piece is step 3's "all answers correct at the swap
endpoint". Investigate `DecisionReach.lean`
(`opinionToAnswer_*_eq_majorityAnswer_*`) and the InSswap→endpoint
chain in BurmanProof.lean:11886+.

## Confirmed decomposition (ChatGPT recon 067a35d4)

No existing endpoint lemma in BurmanProof. AnswerPreservation.lean is
preservation (consensus single-step), NOT propagation. Epidemic splits
into 3 lemmas, composed for the field:

1. `correct_answer_spreads_to_all_resetting_answers` — ∃ correct
   answer → drive to all-Resetting + all-answers-correct. **Hardest,
   genuinely new.** Likely route: NOT "preserve answer through reset"
   but "reset wipes to phi → re-rank → decision re-derives
   majorityAnswer from the execution-invariant opinion field."
2. `all_resetting_all_answers_to_RankingEndpoint_all_answers` — all-R
   + all-correct → re-rank to RankingEndpoint, answers preserved.
3. `RankingEndpoint_all_answers_to_epidemic_endpoint` — RankingEndpoint
   + all-correct → InSswap + all-correct + timer≥1@median. Needs an
   InSout-preservation-through-swap lemma (gap: AnswerPreservation only
   covers consensus pairs; raw-consensus timer=0 sub-case is delicate).

`RankingEndpoint C = InSrank C ∧ (timer≥2@median ∨ IsConsensusConfig C)`
(BurmanProof.lean:137).

## ★ BUG FOUND (2026-05-15) — same class as partial_resetting

`BurmanConvergence.epidemic` (BurmanProperties.lean:60-68) signature is
**FALSE** as stated, not missing a helper. ChatGPT counterexample
(verified against Transition.lean):

> Take C with `InSswap C`, `∀ w, answer = majorityAnswer C` (all
> correct), but median `timer = 0`. Satisfies the hypothesis
> `∃ w, answer = majorityAnswer` (trivially, all correct). But the
> conclusion demands reaching `∀ μ@median, 1 ≤ timer`.

No recovery mechanism: `phase4_propagate` only does `timer := timer-1`
(Nat, 0-1=0), never increases; reset fires only on
`timer=0 ∧ answer-mismatch`, but all answers equal → no reset → no
re-rank → no timer re-init (`transitionPEM_prePhase4` timer-init only
on non-Settled→Settled role change, which `rankDeltaOSSR_satisfies_fix`
prevents in a stable InSswap). Verified Transition.lean L43-48, L83-95.

Diagnosis: **formalization-introduced over-strong signature**, NOT a
paper bug. Kanaya et al. claim eventual all-correct consensus; the
unconditional `timer≥1@median` is a formalization-internal shape that
is unneeded once consensus holds. Exactly the partial_resetting
pattern (over-strong statement, false, fix by weakening to a disjunct).

### Fix options

A. **Disjunct weakening** (mirrors `ranking` field L56-59): conclude
   `... ∧ ((∀μ@median, 1≤timer) ∨ IsConsensusConfig (exec))`. Consumer
   `P_EM_solves_SSEM_from_BurmanConvergence_only` already has the
   ranking-consensus short-circuit precedent (BurmanProperties.lean:263
   `· exact ⟨γ₁,t₁,hCons⟩`). Cost: refactor
   `discharge_BurmanMacroDecisionWithTimer` + its consumer.

B. **Hypothesis strengthening**: the consumer (BurmanProperties.lean:
   212-218) calls hBMDT only on C that ALREADY has
   `hC_timer: ∀μ@median 1≤timer` (part of DecInv) AND
   `0<wrongAnswerCount` (not consensus). So the bad C₀ never arises in
   real usage. Add `(∀μ@median, 1≤timer C₀)` as an epidemic hypothesis;
   thread `hC_timer` at the call site. Then timer≥1 is maintained
   through decision steps via `step_preserves_timer_no_max` (already
   used at L236,245,255). `burmanRankingCorrect` (L87) discards timer
   so is unaffected by adding the hypothesis only if it can supply it —
   needs check (its caller `discharge_BurmanMacroDecision` may lack a
   timer guarantee).

Option A is cleaner / precedented. Option B is smaller blast radius if
burmanRankingCorrect's path can supply the timer hyp.

## ★★ CONCRETE PATH for the timer-branch gap (2026-05-15)

The epidemic field is now structured (BurmanConvergenceFinal.lean):
**consensus branch FULLY PROVEN**; only the timer-branch sorry remains.
Digging into the transition mechanism makes that gap a *concrete
extension of the already-proven normalizer*, NOT a research black-box:

1. `RankDelta.lean` has **zero** `.answer` references ⇒ `rankDeltaOSSR`
   (the ranking subprotocol) never touches `.answer`. Ranking preserves
   answers.
2. `phase4_propagate` L86-87 / L92-93: on a median-mismatch reset, the
   partner **copies the median's answer** (`b₁ with answer := b₀.answer`)
   and BOTH become Resetting. So a reset triggered by a *correct* median
   carries the correct answer into the Resetting phase.
3. `transitionPEM_prePhase4` L49-56: while BOTH agents Resetting, a
   `.phi` agent copies the other's non-`.phi` answer. Wipe-on-entry
   (L37-42) sets newly-Resetting agents to `.phi`. ⇒ during an
   all-Resetting propagation, a single correct (non-phi) Resetting agent
   **spreads the correct answer to every phi agent**.
4. `phase4_decide` writes the median `opinionToAnswer x = majorityAnswer`
   (proven: `opinionToAnswer_*_eq_majorityAnswer_*`).

So the self-stabilization cycle is concrete:
[InSswap, median correct, some wrong] → mismatch reset (answer-copy,
step 2) → drive to all-Resetting reusing **`all_resetting_from_seed_aux`**
(PROVEN) while the phi-spread (step 3) carries the correct answer to all
→ re-rank reusing **`ranking_field_proof` / `reach_known_entry_from_any`**
(PROVEN, answer-preserving by step 1) → `InSswap ∧ all-correct` =
`IsConsensusConfig`. Done.

### Needed new lemmas (answer-tracking overlays on proven structure)

- **A** `reset_fires_answer_copy`: one step at a median-mismatch pair →
  both `.Resetting`, both carry the (correct) median answer. Mechanism:
  `phase4_propagate` L85-93. Single-step trace lemma.
- **B** `all_resetting_from_seed_answer`: answer-tracking twin of
  `all_resetting_from_seed_aux` — same induction, plus the invariant
  "the seed (and every Resetting agent reached) holds `majorityAnswer`",
  using the phi-spread (step 3) at each propagate-reset step.
- **C** `rerank_preserves_all_correct`: thread `∀w answer=majorityAnswer`
  through `reach_known_entry_from_any` + ranking. Uses step 1 (rankDelta
  answer-inert) + step 4 (decide writes majorityAnswer at median) +
  `majorityAnswer_execution_eq` (invariance).

This is substantial but tractable: it overlays an answer invariant on
the *already-closed* normalizer/ranking proofs rather than inventing a
new potential. Estimated: comparable to the normalizer (which is done).

## Consumers of BurmanConvergence.epidemic (refactor surface)

- BurmanProperties.lean:87 `burmanRankingCorrect` — discards timer
  (`⟨_,_,hSwap,hAnswers,_⟩`). Disjunct-safe ✓.
- MacroStepComposition.lean:272 `discharge_BurmanMacroDecisionWithTimer`
  — forwards `h_timer` to output `BurmanMacroDecisionWithTimer` (which
  requires timer). Needs handling under either option.
- BurmanProperties.lean:198/218 — the master decision loop; consensus
  short-circuit precedent at L263.

## ★★★ PRECISE BLOCKER (2026-05-15, verified by exhaustive recon)

A/B/C are GREEN (committed): `trigger_correct_reset_from_InSrank`,
`all_resetting_from_seed_answer_aux`, `rankDeltaOSSR_answer_preserved`
(+ propagateReset/processAgent/resetOSSR answer-preservation),
`transitionPEM_prePhase4_propagate_answer`, `propagate_reset_step_answer_trace`,
`majorityAnswer_ne_phi`. Consensus branch of epidemic field PROVEN.

The "once all-correct-uniform, no mismatch ⇒ re-rank preserves correctness"
idea is **FALSE**. Reason (Transition.lean L65-78): `phase4_decide`
writes `opinionToAnswer (median-rank agent's opinion)` for ANY
both-`.Settled` pair with one at median rank — gated ONLY on both-Settled,
NOT on sortedness or current correctness. During a re-rank the config is
generally NOT rank-sorted, so the median-rank agent may hold the minority
opinion and `phase4_decide` writes `opinionToAnswer(minority) ≠
majorityAnswer`, destroying `InSout`. (`transitionPEM_phase4_of_not_both_settled`
gives phase4=id only while NOT both-Settled, i.e. only in the all-Resetting
regime — but re-rank necessarily settles agents to reach InSrank.)

Therefore closing the timer-branch requires threading an answer-correctness
invariant through the answer-OPAQUE settling/decide phase of the proven
ranking machinery — i.e. an answer overlay re-derivation of that machinery,
estimated comparable to the (now-closed) `resetFuel` normalizer. The proven
ranking endpoints (`RankingEndpoint`, `ranking_from_*`) never expose a
strictly-decreasing answer measure or that the consensus disjunct (not
timer≥2) is reached, so no short outer recursion exists.

Clean endpoint available for the FINAL leg once all-correct InSswap is
reached: `decision_reaches_consensus_when_Sout` (InSswap ∧ InSout →
consensus), `isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero`,
`step_preserves_consensus` (consensus is step-stable). The remaining work
is purely the answer-overlay through settling.

Nature: this is the machine-checked formalization of Kanaya et al. 2025's
answer self-stabilization — a PUBLISHED theorem; the contribution is the
Lean formalization (CPP/ITP-class), NOT new mathematics. The two
formalization bugs (partial_resetting, epidemic-signature) are over-strong
intermediate-lemma artifacts of formalization, not paper errors.

## ★★★★ 2026-05-16 — Epidemic timer-branch ISOLATED to minimal leaf

The epidemic field's timer-branch is now **fully wired and proven down to
a single minimal non-circular leaf**.  New GREEN, axiom-clean
(`[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**) theorem in
`BurmanConvergenceFinal.lean` (placed after `cycle_macro_discharge`):

  * `epidemic_timer_branch_to_consensus` — from `InSrank C₁` + `2 ≤
    timer@median` (the timer disjunct of `ranking_field_proof`), drives to
    `IsConsensusConfig` via the PROVEN `swap_reaches_Sswap_from_timer_
    bound_with_timer` (InSrank+timer≥2 → InSswap+timer≥1) composed with
    the PROVEN non-circular `median_wrong_only_drive_to_consensus` strong
    recursion.  Its **only** hypothesis is the reservoir median-correct
    leaf `hMedCorrectExit` (no reference to `C₁`/epidemic goal/this
    theorem — non-circular by construction).

The `burmanConvergence_concrete.epidemic` field was restructured: a shared
`hclose` helper turns any reached `IsConsensusConfig` into all three field
conjuncts (`InSswap`, all-answers-correct, `∨ IsConsensusConfig` via
`InStim_iff_IsConsensusConfig` + `majorityAnswer_execution_eq`).  Both the
consensus disjunct (already proven) and the timer disjunct route through
`hclose`.  The timer disjunct calls `epidemic_timer_branch_to_consensus`;
the **single remaining `sorry`** in the entire codebase is now exactly the
`hMedCorrectExit` leaf supplied at that one call site (line ~6158):

```
∀ k D, InSswap D → (1 ≤ timer@median) → 0 < wrongAnswerCount D →
  (∀μ@median, answer = majorityAnswer D) → wrongAnswerCount D ≤ k →
  ∃ γ t, IsConsensusConfig (execution P D γ t)
```

This is the precise, minimal, non-circular shape of the documented open
core (the answer-and-timer overlay re-derivation of the recruit/swap
kernel): the median-correct reservoir renormalizer.  Everything around it
— ranking entry, swap reachability, median-wrong recursion, consensus
closing — is proven axiom-clean.  `#print axioms` profiles:
`epidemic_timer_branch_to_consensus`, `median_wrong_only_drive_to_
consensus`, `swap_reaches_Sswap_from_timer_bound_with_timer`,
`exists_answer_safe_misordered_pair` = `[propext, Classical.choice,
Quot.sound]`; `burmanConvergence_concrete` / `P_EM_solves_SSEM_final` =
`[propext, sorryAx, Classical.choice, Quot.sound]` (the lone `sorryAx`
from the single isolated leaf).  Full `lake build` green, 903 jobs.

### What remains to close the leaf (the genuine open core)

`hMedCorrectExit` must be discharged via reset → all-Resetting-uniform →
the kernel `all_resetting_uniform_consensus_final` (which terminates
internally via `cycle_potential_reaches_consensus`' phiCount strong
recursion — NON-circular, no call back to epidemic).  The kernel's slot
discharges exist (`recruit_selector_discharge`, `phaseA_discharge`,
`exists_answer_safe_misordered_pair`, `cycle_macro_discharge`); the
residual is the structural witnesses `hTree` (BFS-recruit schedule with
the `PairResAnsSafe` answer overlay), `hFreshSafe` (dormant-wake schedule
with the both-`Settled`-free + `ResAns` invariant), and the median-timer
threaded ≥2 through the swap recursion (TASK 1a — `hTimerLive` is provably
false universally for stale `InSswap`, so must be carried along the
schedule from the recruit-phase `timer_init_ge_2`).  These are the
answer-and-timer overlay re-derivation of the proven (answer-opaque)
`phase4_binary_tree` / `phase3bc_from_awakening` ranking machinery,
estimated comparable to the closed `resetFuel` normalizer.
