# SSExactMajority — UNDERSTANDING.md

Last updated: 2026-05-18

## Project Goal

Lean 4 + Mathlib formalization of Kanaya et al. 2025 self-stabilizing
exact majority population protocol.  Ultimate theorem:
`SSEM.P_EM_solves_SSEM_final` (`Convergence/BurmanConvergenceFinal.lean:16052`).

## Current state (2026-05-18) — qualitative half DONE

- `P_EM_solves_SSEM_final` is unconditional for `n ≥ 4`.  No external
  hypotheses; axioms `[propext, Classical.choice, Quot.sound]`.
- **0 `sorry`** in any source file (comment-stripping scan + clean
  `lake build` confirmed on uisai1).
- Burman 2021 ranking is now a *proved theorem* (`ranking_field_proof`),
  not a hypothesis.
- The final `hMedCorrectExit` sorry referenced below (line ~9360 of
  earlier revisions) was discharged via
  `hMedCorrectExit_from_reentry_and_seed_prefixes` +
  `med_correct_live_seed_or_progress` +
  `reservoir_case_seed_or_progress`.
- `OddRecruitDriver.lean` removed (`a186ac78`) — bypassed by
  `EndpointRepair.lean`.

## What is left (the time-optimal half of the paper title)

Paper title: "**Time- and Space-Optimal** Silent Self-Stabilizing Exact
Majority".  We have proved correctness, termination, and the space lower
bound (Theorem 2).  Time-side claims are not formalized:

| Item | File | State |
|------|------|-------|
| Probability framework | `Probability/RandomScheduler.lean`, `Probability/ExpectedTime.lean` | scaffold only |
| Theorem 3 (Ω(n log n) lower) | `LowerBound/Time.lean` | scaffold only |
| §5.2 (O(n log n) upper for P_EM) | `UpperBound/Time.lean` | scaffold only |

Design plan, proof strategy, and dispatched sub-tasks for codex / ChatGPT
collab are in `docs/TIME_BOUND_PLAN.md`.

---

## Historical session notes (kept for context)

The sections below are the working notes from the qualitative phase.  All
gaps they describe have since been closed (`P_EM_solves_SSEM_final` is
unconditional).  Reading them helps anyone resuming the qualitative work
to understand how the architecture got to its current shape.

**Historical "Single remaining `sorry`" snapshot (pre-2026-05-18):**
line ~9360, `have hMedCorrectExit : ... := by sorry` inside `theorem
burmanConvergence_concrete` (the `epidemic` field).

Historical type of that sorry:
```
∀ k D, InSswap D → (∀μ median, 1≤timer) → 0<wrongAnswerCount D →
  (∀μ median, answer=majorityAnswer D) → wrongAnswerCount D ≤ k →
  ∃ γ t, IsConsensusConfig (execution P D γ t)
```

## Architecture (all green, 8+ commits this session)

The sorry is consumed by `epidemic_timer_branch_to_consensus` and reduced via:
1. `hMedCorrectExit_from_reservoir_entry_and_reset_leaf` — takes `hEntry` + `hLeaf`, produces the sorry's type.
2. `cycle_macro_discharge_tieaware` — tie-aware (no universal hNoTie), handles median-wrong + median-timer-0 branches internally.
3. `cycle_potential_reaches_consensus` — strong recursion on `phiCount` via `reach_zero_potential_macro`.

The sorry reduces to **three Prop obligations** (all `def`s in the file, all green reducers proven):

### Prop #1: `AllResettingUniformToInSswapResAnsPhiZero` (line ~8027)
From uniform all-Resetting (∀w role=.Resetting, ∀w answer=m₀=majorityAnswer) → ∃ γ t, InSswap E ∧ ResAns (majorityAnswer E) E ∧ phiCount E = 0.

### Props #2'/#3': Disjunctive seed-OR-progress (lines ~8110, ~8164)
- `MedCorrectLiveProducesCorrectSeedOrProgress`
- `ReservoirCaseProducesCorrectSeedOrProgress`

Both: from appropriate hypotheses → ∃ L, `CorrectResetSeed C'` ∨ `(InSswap C' ∧ ResAns C' [∧ phiCount C' < phiCount D])`.

## Key Findings This Session

### Finding 1: Props #2/#3 were over-strong (FALSE) — FIXED
The original pure-seed Props were false: even-n upper-median-only wrong/phi counterexample. The even lower/upper median decision step overwrites both answers (no reset fires). `trigger_correct_reset_from_InSrank_even` explicitly excludes upper median (rank+1≠n/2+1). Fixed to disjunctive seed-OR-progress shape (commit `e670e276`, green).

### Finding 2: Prop #1's `phiCount=0` — over-strong CONCLUSION but TRUE statement
`phiCount` is already 0 at uniform all-Resetting (all answers = m₀ ≠ .phi), so it can't measure reset-cycle progress. BUT the statement IS true (not false) because at the final InSswap all answers ARE correct (= m₀, no .phi):
- Non-median answers: preserved through ranking (non-median recruits don't fire phase4_decide).
- Median answer: `opinionToAnswer_median_eq_majorityAnswer_odd` (DecisionReach:178) / `_even` (134) proves at ANY InSswap the median decision = majorityAnswer (InSswap.input_rank forces median-RANK agent to hold median INPUT; opinions invariant).

### Finding 3: The PROOF ROUTE for Prop #1
**Cannot** use `all_resetting_uniform_to_InSswap_ResAns` (BCF:4298, green non-weak) directly — its `hRecruit` demands per-step `PairResAnsSafe` which the median-recruit violates (phase4_decide writes opinionToAnswer(input) mid-ranking).

**Cannot** use `all_resetting_uniform_to_InSswap_ResAns_weak` (BCF:5546) directly — its `hTreeW` demands per-recruit answer-preservation (`transitionPEM.2.answer = (D child).answer`) which the median-recruit violates.

**CORRECT route:** 
1. **Structural `RecruitFrontierSelector`** — same as 5546's hTreeW but DROP the two answer-preservation conjuncts. Structural properties (child becomes Settled, gets target rank, p keeps rank, measure decreases) hold for ALL recruits INCLUDING median.
2. **`RankingSwapEndpointRepairsResAns`** — separate theorem: from FreshRankingStart with uniform m₀, the full ranking+swap phase produces InSswap with ResAns ∧ NoPhi. Uses: (a) opinionToAnswer_median_eq_majorityAnswer (median correct at InSswap); (b) non-median answers preserved (their recruit steps don't fire phase4_decide); (c) no phi introduced (phi-wipe only on Resetting→non-Resetting entry, not relevant here).
3. `hSelect` discharged via green `exists_answer_safe_misordered_pair` (BCF:6908) by threading `hm := majorityAnswer_runPairs_eq` + `hTimer` via swap-timer lemmas.

### Finding 4: "median-recruit writes wrong answer" was a MISCONCEPTION
For ~4 GPT rounds this was treated as an unbreakable obstruction. It's not — it's a TRANSIENT. The final InSswap necessarily has the median correct (opinionToAnswer lemmas). The per-step hRecruit/hTreeW answer-preservation is the wrong proof approach; the RIGHT approach is structural-recruit + endpoint-repair.

### Finding 5 (2026-05-17): Per-step PairResAnsSafe at median is FALSE
`odd_median_recruit_PairResAnsSafe_of_majority_child` is FALSE as stated. Counterexample:
- m₀ = .outA, parent opinion = .B (minority), child opinion = .A (majority)
- After recruit: parent.rank < child.rank (always). `phase4_swap` fires (x₀=.B, x₁=.A)
- Swap moves child state to position 0, but `phase4_decide` uses ORIGINAL x₀ (parent's .B)
- Writes `opinionToAnswer .B = .outB` to median agent → .outB ∉ {.outA, .phi}

This is a **formulation issue**, not a paper bug. The paper argues convergence probabilistically.
The non-median case `odd_nonmedian_recruit_PairResAnsSafe` IS true and now proven sorry-free.

### Finding 6 (2026-05-17): Majority-parent fixes the median case
The median PairResAnsSafe is FALSE only when the parent has minority opinion (swap fires, decide uses wrong x₀). When BOTH parent AND child have majority opinion, swap never fires (x₀ = x₁ = majority, swap needs x₀=.B ∧ x₁=.A = different types). Without swap, decide writes opinionToAnswer(child_majority) = m₀. PairResAnsSafe holds.

**Strategy:** construct the ranking schedule so the parent-of-median rank is filled by a majority-opinion agent. The counting argument works: at the time of recruiting the parent-of-median (small rank, recruited early), most agents are still Unsettled and majority-opinion agents outnumber minority (> n/2). So a majority agent is always available.

### Finding 7 (2026-05-17): Endpoint repair is viable — no propagate fires during ranking/swap

Key realization: from FreshRankingStart, during ranking (Phase B) and swap (Phase C):
- **No agent enters Resetting** (no collisions from FreshRankingStart, error monitoring doesn't trigger in the schedule, propagate doesn't fire because timer stays ≫ 0)
- **phi guard never fires** (requires Resetting entry)
- **phase4_decide only modifies ceilHalf-rank agent** (non-median agents' answers preserved)
- **phase4_propagate doesn't fire** (timer initialized to 7*(Rmax+4) ≫ 0, decremented at most O(n) times during swap, stays > 0)

Therefore at InSswap reached from all-Resetting uniform m₀:
- Non-median answers: preserved from FreshRankingStart = m₀
- Median answer: opinionToAnswer(median_input) = majorityAnswer = m₀ (proven lemma)
- All answers = m₀ → ResAns + phiCount = 0 → IsConsensusConfig

**Problem with formalization:** `ranking_field_proof` is a black box — can't track answers through it. Need EITHER:
(a) Custom ranking induction with answer tracking (the `hRecruit` approach), OR
(b) Prove the endpoint property directly from structural properties of the protocol

### Finding 8 (2026-05-17): Architecture for closing the final sorry

**Dependency chain:**
```
BCF:8309 (hMedCorrectExit)
  ← timer drain + propagate trigger (green machinery)
  ← all_resetting_from_seed_answer_aux (green)
  ← AllResettingUniformToInSswapResAnsPhiZero
     ← phaseA_discharge (green, needs hFreshSafe)
     ← custom ranking with ResAns tracking (NEW — the core gap)
     ← swap phase + endpoint repair (green)
```

**Core gap:** `fresh_start_ResAns_to_InSrank_safe` needs universal `hRecruit` which is FALSE for odd n (Finding 5). Need custom induction with invariant:
```
medianRankFilled D ∨ (∃ majority Unsettled agent ∧ parent-of-median has majority opinion)
```

**Priority selector:** at each step:
1. If median filled → non-median recruit (PairResAnsSafe, proven)
2. If ≥ 2 majority Unsettled AND parent-of-median being filled → choose majority child
3. If exactly 1 majority Unsettled AND median ready → fill median NOW
4. Otherwise → non-median with minority child (save majority for median)

Estimated: ~325 lines of new Lean 4 code. All using existing green machinery.

### Finding 9 (2026-05-17): OddRecruitDriver green inventory
- `majorityCountOfAnswer`, `majorityAgentsOfAnswer`: new defs for counting
- `exists_unsettled_majority_child_of_settled_lt_majority`: sorry-free counting lemma
- `odd_nonmedian_recruit_PairResAnsSafe`: fully proven (phase4 identity when neither at ceilHalf)
- `phase4_nonmedian_answer_eq`: helper (decide/propagate identity → swap preserves answers)
- `odd_exists_answer_safe_recruit_pair`: composition theorem (sorry-free, takes median/nonmedian as hypotheses)

## Key Green Ammo (verified, 0 sorry, 0 axiom)

| Theorem | File:Line | Purpose |
|---------|-----------|---------|
| `odd_nonmedian_recruit_PairResAnsSafe` | OddRecruitDriver | Non-median recruit preserves ResAns (odd n) |
| `exists_unsettled_majority_child_of_settled_lt_majority` | OddRecruitDriver | Counting: settled < majority → ∃ unsettled majority child |
| `odd_exists_answer_safe_recruit_pair` | OddRecruitDriver | Composition: finds safe recruit pair |
| `cycle_potential_reaches_consensus` | BCF:3080 | Strong recursion on phiCount |
| `cycle_macro_discharge_tieaware` | BCF:~7850 | No-hNoTie macro step |
| `median_wrong_step_resAns_decrease_tieaware` | BCF:~7766 | Tie-aware wrong-step decrease |
| `all_resetting_from_seed_answer_aux` | BCF:1613 | Seed → all-Resetting uniform |
| `trigger_correct_reset_from_InSrank` | BCF:1253 | Timer=0 + wrong → reset seed (odd) |
| `trigger_correct_reset_from_InSrank_even` | BCF:1482 | Same for even (drops hne) |
| `exists_answer_safe_misordered_pair` | BCF:6908 | hSelect slot (green) |
| `recruit_step_preserves_ResAns_if_decision_safe` | BCF:3922 | hRecruit (needs PairResAnsSafe) |
| `all_resetting_uniform_to_InSswap_ResAns` | BCF:4298 | Non-weak re-entry (needs hRecruit+hSelect) |
| `all_resetting_uniform_to_InSswap_ResAns_weak` | BCF:5546 | Weak re-entry (needs hTreeW+hSelect) |
| `opinionToAnswer_median_eq_majorityAnswer_odd` | DecisionReach:178 | Median correct at InSswap (odd) |
| `opinionToAnswer_lower_median_eq_majorityAnswer_even` | DecisionReach:134 | Median correct at InSswap (even) |
| `decision_step_at_median_pair_even_tie_decreases` | DecisionTieCase:114 | Even-tie direct progress |
| `exists_wrong_nonmedian_of_med_correct` | BCF (green) | 0<wrongCount + med-correct → ∃ non-med wrong |
| `odd_timer_one_max_step_clean_or_seed` | BCF:7656 | Odd timer=1 → clean OR seed |
| `timer_descent_to_one` | TimerDescentNoSwap:231 | Odd timer≥2 → ≤1 |
| `nAOf_execution_eq` / `nBOf_execution_eq` | Step.lean | Inputs invariant along execution |
| `majorityAnswer_execution_eq` / `_runPairs_eq` | Step/BCF | majorityAnswer invariant |
| `reach_zero_potential_macro` | PotentialReach:90 | Generic (Pinv,φ) strong recursion |
| `exists_schedule_after_runPairs` | BCF:1941 | runPairs → ∃ execution |

### Finding 10 (2026-05-17, session 2): OddRecruitDriver sorries closed

Closed 4 of 5 OddRecruitDriver sorries, introduced 2 focused timer-condition sorries in helper.

**Closed:**
- Pigeonhole (line 499 → 611): `unrecruitedTargetRankCount=0 + SettledRanksInj → InSrank` via `Finite.injective_iff_surjective`
- J preservation (line 537): full `NoResettingCfg ∧ SettledRanksInj` preservation through recruit step. Key insight: rank set after step = {parent_rank, target_rank} ∪ others, regardless of phase4_swap (which may permute but doesn't change the SET)
- ρ recruited (line 555): target rank occupied after step (witness from rank disjunction)
- Ranks subset (line 560): old recruited ranks stay recruited (others unchanged, parent's rank still occupied by someone via rank disjunction)

**New helper:** `recruit_step_roles_ranks_odd` — structural facts for (Settled, Unsettled) transitionPEM:
- Both outputs Settled
- Ranks: {parent_rank, target_rank} (disjunction on which goes where)
- Key arithmetic: `valid_parent_not_at_median_odd` — valid parent can't be at ceilHalf n (for odd n, median's children would have rank ≥ n)

**Remaining 2 sorries in helper (timer conditions):** `phase4_propagate_settled_of_positive_median_timers` needs ht₀/ht₁. Argument: parent NOT at median (validity), child at median gets timer = 7*(Rmax+4) from prePhase4 timer init. After swap+decide, timer preserved. Effective timer ≥ 27 > 0.

**Net sorry change:** 8 → 6 → 4 (OddRecruitDriver: 5→1, EndpointRepair: 2→2→2, BCF: 1→1)

### Finding 11 (2026-05-17, session 2 continued): Core selector sub-problems

The core selector sorry needs three sub-components:

**Sub-problem 1: Ready parent with free target rank (tree frontier)**
- From SettledRanksInj + ¬InSrank → ∃ Settled parent with valid child slot at unrecruited rank
- REQUIRES a tree structure invariant: `BinaryTreeProperty` (rank 0 Settled, every Settled non-root has Settled parent) or `HeapPrefix`
- Without tree invariant, SettledRanksInj alone doesn't guarantee connected tree structure
- Invariant is maintained: each recruit adds a child at binary tree position, parent already Settled
- FreshRankingStart → BinaryTreeProperty (root at rank 0)
- From BinaryTreeProperty + ¬InSrank: walk up binary tree from unrecruited rank to find frontier parent

**Sub-problem 2: Counting argument at median step**
- At median target (rank (n-1)/2 for odd n): need Unsettled child with majority opinion
- `exists_unsettled_majority_child_of_settled_lt_majority` needs settledCount < majorityCount
- With HeapPrefix/BFS order: at median step k=(n-1)/2, settledCount=k < (n+1)/2=majorityCount ✓
- Without BFS order: need to separately ensure settledCount < majorityCount when median is targeted

**Sub-problem 3: PairResAnsSafe at median (relaxed)**
- `odd_median_recruit_PairResAnsSafe_of_majority_parent_child` requires BOTH parent and child majority
- Analysis shows: phase4_decide uses `opinionToAnswer x₁` at median, independent of swap
- For (Settled pos0, Unsettled pos1): x₁ = child's opinion → only CHILD majority needed
- For (Unsettled pos0, Settled pos1): x₁ = parent's opinion → only PARENT majority needed
- Can write relaxed theorem `odd_median_recruit_PairResAnsSafe_of_majority_child` (child only)

**Recommended approach:** Switch OddRecruitDriver to HeapPrefix-based induction (BFS order). This:
1. Gives ready parent for free (parent of rank k, at rank < k, Settled)
2. Guarantees settledCount = k at each step → counting argument trivial at median
3. Avoids the tree frontier problem entirely
4. Cost: ~100 lines refactoring, reusing heapPrefix_recruit_step's structure

### Finding 12: EndpointRepair consolidated plan

allResettingUniform_proof restructuring:
1. Phase A: phaseA_discharge (proven) → FreshRankingStart + ResAns
2. Phase B: ranking with ResAns → InSrank + ResAns + timer≥2 + majorityAnswer
   - Odd n: fresh_start_to_InSrank_ResAns_odd (needs core selector)
   - Even n: fresh_start_ResAns_to_InSrank_safe with recruit_PairResAnsSafe_even (universal hRecruit)
   - Both need timer≥2 at InSrank (from prePhase4 timer init at median, never decremented during ranking because median can't be parent)
3. Phase C: InSrank_to_InSswap_ResAns_with_inv → InSswap + ResAns (needs swap timer sorry)
4. Endpoint: ResAns at InSswap → phiCount=0 (all answers = m₀, no phi)

Swap timer sorry (EndpointRepair:262): timer≥2 → timer≥2 after swap step is FALSE (median-max interaction drops timer by 1). Fix: use SwapTimerState (disjunction of timer≥2 OR (max-B ∧ timer≥1)). ChatGPT suggested this approach.

## Commits This Session (all green, pushed)

- `e1bfee6e` — request-3 lemmas green (odd timer-1 step)
- `6292a2c4` — nAOf/nBOf_execution_eq
- `5431eefb` — GPT (A) tie-aware hNoTie resolution GREEN
- `2d326007` — GPT round-2 green composition layer
- `e670e276` — Disjunctive seed-or-progress repair GREEN (Props #2/#3 over-strong fix)
- CHECKPOINTs 16o–16y documenting all findings

## Next Step (concrete, well-defined)

Prove `AllResettingUniformToInSswapResAnsPhiZero` via **endpoint repair**.

### Key Insight (2026-05-16 session)

The `hRecruit` / `hTreeW` routes (maintaining ResAns invariantly) are blocked:
odd-n median recruit writes `opinionToAnswer(child_opinion)` which may be minority
= not in {m₀, .phi}. But **this doesn't matter** because at the FINAL InSswap:
- `opinionToAnswer_median_eq_majorityAnswer_odd/even` proves median answer = m₀
- Non-median answers are NEVER modified (no step writes them):
  - `phase4_decide`: identity at non-ceilHalf (odd) / non-(n/2,n/2+1) pair (even)
  - `phase4_propagate`: requires timer=0, but timer≥1 throughout
    (initialized to 7*(Rmax+4) at recruit, ranking_field_proof gives ≥2 at InSrank,
    swap_reaches gives ≥1 at InSswap; never hits 0)

### Finding 13 (2026-05-17, session 3): family route received; Phase C is now green

Received the ChatGPT/family route:
```
AllResettingUniformToInSswapResAnsPhiZero
  ← normalize all-resetting answers
  ← all-resetting/fresh-start bridge
  ← answer-preserving ranking to InSrank
  ← answer-preserving swap to InSswap
  ← no-phi endpoint
```

Implemented the non-circular Phase C part using the correct timer invariant,
not the false global `timer ≥ 2` invariant:
- `PairNoPhiSafe_of_answer_safe_misorder_case`
- `exists_answer_safe_noPhi_misordered_pair_of_swapInv`
- `InSrank_to_InSswap_ResAns_noPhi_with_swapInv`
- `InSrank_to_InSswap_ResAns_with_inv`

`SwapInv` is exactly the needed disjunction:
```
timer ≥ 2 at median
∨ (timer ≥ 1 at median ∧ max-rank input is B)
```

Also added:
- `allResettingUniform_from_safe_noPhi_phases`
- `allResettingUniform_from_safe_noPhi_phaseA_rank`

The latter reduces `AllResettingUniformToInSswapResAnsPhiZero` to only:
1. Phase A: all-Resetting uniform → `FreshRankingStart + ResAns + noPhi`
2. Phase B: `FreshRankingStart + ResAns + noPhi → InSrank + ResAns + noPhi + timer≥2`

Remote verification on uisai1:
```
/tmp/ssem-build/bcf-remote-20260517-222638.log  -- green after Phase C wrapper
/tmp/ssem-build/bcf-remote-20260517-222923.log  -- green after phaseA+rank composition
Build completed successfully (764 jobs).
```

Current `rg` sorry audit remains exactly one `sorry`, the final
`hMedCorrectExit` local proof in `BurmanConvergenceFinal.lean`.
  - `prePhase4` phi-wipe/spread: only for Resetting agents (none after FreshRankingStart)

### Even-tie Case (Prop #1 IS TRUE in tie)

Confirmed: phase4_decide in even-tie writes .outT (not opinionToAnswer). And
.outT = majorityAnswer in tie case. So median answer = majorityAnswer in tie too.
No `m₀ ≠ .outT` / `nAOf ≠ nBOf` hypothesis needed.

### Proof Route

1. `ranking_field_proof` from C → InSrank + (timer≥2 ∨ consensus)
2. Consensus branch: directly done
3. Timer≥2 branch: `swap_reaches_Sswap_from_timer_bound_with_timer` → InSswap + timer≥1
4. **Endpoint repair (NEW THEOREM):** at InSswap reached from uniform m₀:
   - Non-median: answer = m₀ (induction: per-step non-median answer preservation)
   - Median: answer = majorityAnswer = m₀ (opinionToAnswer_median lemmas)
   - Combined: ResAns m₀ ∧ phiCount = 0

### Required New Lemmas

**A. `step_preserves_nonmedian_answer`**: for any step at pair (u,v), if no agent is
Resetting AND timer≥1 at median, then non-median agents' answers are unchanged.
(Follows from: decide identity at non-median, propagate doesn't fire with timer≥1,
prePhase4 doesn't fire for Settled/Unsettled agents.)

**B. `execution_preserves_nonmedian_answer`**: induction over execution steps using A.
Need: no Resetting agents throughout + timer≥1 throughout. Both hold:
- No Resetting: FreshRankingStart has all Settled/Unsettled; ranking only creates Settled
- Timer≥1: initialized high at recruit, ranking_field_proof ensures ≥2 at InSrank

**C. Tie-aware `median_answer_at_InSswap_eq_majorityAnswer`**: case split:
- Odd: `opinionToAnswer_median_eq_majorityAnswer_odd` (GREEN)
- Even no-tie: `opinionToAnswer_lower_median_eq_majorityAnswer_even` (GREEN, needs hne)
- Even tie: `transitionPEM_at_median_pair_even_disagreed_inputs` from DecisionTieCase.lean

### Route CONFIRMED (2026-05-16/17 session, ChatGPT Pro)

Use `all_resetting_uniform_to_InSswap_ResAns` (BCF:4298), NOT `ranking_field_proof`.
Code: EndpointRepair.lean (main proof) + OddRecruitDriver.lean (odd-n selector).

**7 sorries remain (all mechanical):**
- EndpointRepair: hRecruit, hSelect, hPhaseA, phiCount=0
- OddRecruitDriver: median safety, nonmedian safety, counting

**KEY ISSUE:** Universal hRecruit FALSE for odd n. Fix: OddRecruitDriver
chooses non-median target when available, majority child otherwise.
Needs `Settled < nA` invariant. Also: `transitionPEM_recruit_ba_answer_inert_of_no_median`
expects (Unsettled,Settled) but PairResAnsSafe passes (Settled,Unsettled) — need symmetric version.

**hPhaseA** is NOT a standalone theorem — callers supply it. Need to trace through
the normalize chain or construct directly from all-Resetting.

ChatGPT task 7e326905 pending (corrected odd-n driver code).

This is a FORMALIZATION task (composing existing green ammo), not open research.

## Formulation Audit (2026-05-16, confirmed with ChatGPT Pro)

All three Props are **TRUE** (including even-n tie case). Confirmed:
- Phase4_decide writes .outT in even-tie (not opinionToAnswer) = majorityAnswer ✓
- CorrectResetSeed IS reachable in tie case (agents CAN hold .outT via phase4_decide)
- No `m₀ ≠ .outT` / `nAOf ≠ nBOf` guard needed on any Prop

The REAL obstruction was: trying to use existing theorem routes (hRecruit/hTreeW) that
require per-step answer preservation. Median recruit in odd-n writes opinionToAnswer
of possibly-minority opinion = NOT in {m₀, .phi}. But this is a TRANSIENT violation
corrected at the InSswap endpoint. The fix is endpoint repair, not weakening the Prop.

## Anti-patterns to Avoid

- "This is irreducible research / 撼不动" — NO. This is Kanaya et al.'s CORRECT published proof. If Lean won't close it, OUR STATEMENT has a bug, not the math.
- Treating the median-recruit transient as an unbreakable obstruction — it's a transient corrected at the endpoint.
- Using `phiCount` as the reset-cycle progress measure — it's already 0 at uniform all-Resetting; it measures the OUTER cycle, not the re-entry.
- Demanding per-recruit answer-preservation (hRecruit/hTreeW) — the correct route is structural-recruit + endpoint-repair.
- Waiting for ChatGPT Pro without making independent progress — dispatch and continue.

## ChatGPT Bridge

- Channel: `family` (confirmed working; old `exact-mj` is dead/garbage)
- Auto-retry on garbage answers is deployed
- Full replies in `/tmp/chatgpt-bridge/<id>.md` (read with cat, not tail)
- Dispatched `b0mbqdzr8` on structural recruit + endpoint repair (may have completed)

## 2026-05-17 Codex Session Update

Current real proof-term audit:

```bash
rg -n '^\s*(sorry|admit|axiom)(\s|$)' SSExactMajority -g'*.lean'
```

returns exactly:

```text
SSExactMajority/Convergence/BurmanConvergenceFinal.lean:8309:        sorry
```

Newly removed real `sorry`s:

- `SSExactMajority/Convergence/OddRecruitDriver.lean`: the odd recruit driver proof is now closed. Remote uisai1 verification succeeded:
  `lake build SSExactMajority.Convergence.OddRecruitDriver`
  with `Built SSExactMajority.Convergence.OddRecruitDriver (187s)`.
- `SSExactMajority/Convergence/EndpointRepair.lean`: the unused/dead `allResettingUniform_proof` route via `ranking_field_proof` was deleted. That route was invalid because black-box ranking loses the `ResAns` / no-`.phi` endpoint information.
  Remote uisai1 verification succeeded:
  `lake build SSExactMajority.Convergence.EndpointRepair`
  with `Built SSExactMajority.Convergence.EndpointRepair (129s)`.

Current `BCF:8309` dependency chain:

```lean
hMedCorrectExit
  <- hMedCorrectExit_from_reservoir_entry_and_reset_leaf
       hEntry hLeaf

hEntry
  <- med_correct_live_InSswap_to_reservoir_entry_from_seed_and_reentry
       hDmax1 hSeedPrefixEntry hReentry

hLeaf
  <- reservoir_reset_leaf_from_seed_and_reentry
       hDmax1 hSeedPrefixReservoir hReentry
```

So the remaining non-circular obligations are:

- `hReentry : AllResettingUniformToInSswapResAnsPhiZero Rmax Emax Dmax hn`
- `hSeedPrefixEntry : MedCorrectLiveProducesCorrectSeedOrProgress Rmax Emax Dmax hn`
- `hSeedPrefixReservoir : ReservoirCaseProducesCorrectSeedOrProgress Rmax Emax Dmax hn`

Do not reintroduce the deleted `EndpointRepair` theorem or use `ranking_field_proof`
to prove `hReentry`; that would hide the same gap. The route must be structural:
all-Resetting/uniform -> answer-tracked fresh/ranking/swap -> `InSswap ∧ ResAns ∧ phiCount = 0`,
then use that as the re-entry input for the seed-prefix builders.

## 2026-05-17 Late Update

Received the ChatGPT/family non-circular route:

```text
AllResettingUniformToInSswapResAnsPhiZero
  <- normalize all-resetting answers
  <- all-resetting/fresh-start bridge
  <- answer-preserving ranking to InSrank
  <- answer-preserving swap to InSswap
  <- no-phi endpoint
```

Confirmed in code:

- Phase C is now represented by `InSrank_to_InSswap_ResAns_with_inv` in
  `BurmanConvergenceFinal.lean`, using `SwapInv` rather than the false invariant
  "median timer >= 2 after every swap".
- New local odd recruit no-phi kernels are green in `OddRecruitDriver.lean`:
  `odd_nonmedian_recruit_ba_PairNoPhiSafe` and
  `odd_median_recruit_ba_PairNoPhiSafe_of_majority_child`.
  Remote verification:
  `/tmp/ssem-build/odd-pair-nophi-20260517-224417.log`
  (`Build completed successfully (765 jobs)`).

Do not use `ranking_from_all_resetting` as the re-entry proof: it reaches ranking
but does not carry `ResAns` / no-phi. The next real work item is still Phase B:
build a practical `FreshRankingStart + ResAns + noPhi -> InSrank + ResAns + noPhi + timer`
driver without making the proof term too expensive.

## 2026-05-17 Late Update 2

`OddRecruitDriver.lean` now has the practical odd Phase B driver:

```lean
fresh_start_to_InSrank_ResAns_odd :
  FreshRankingStart C ->
  ResAns m₀ C ->
  (∀ w, (C w).1.answer ≠ .phi) ->
  ceilHalf n ≤ majorityCountOfAnswer C m₀ ->
  ∃ L,
    InSrank (runPairs P C L) ∧
    ResAns m₀ (runPairs P C L) ∧
    (∀ w, ((runPairs P C L) w).1.answer ≠ .phi) ∧
    majorityAnswer (runPairs P C L) = majorityAnswer C ∧
    (∀ μ, median_rank μ in runPairs P C L -> 2 ≤ timer μ)
```

This was verified on uisai1:

```text
/tmp/ssem-build/odd-nophi-timer3-20260517-230042.log
Build completed successfully (765 jobs)
remote-exit 0
```

Current actual source-level placeholder audit still has exactly one real `sorry`,
now at approximately:

```text
SSExactMajority/Convergence/BurmanConvergenceFinal.lean:9440
```

Important structural issue: `OddRecruitDriver.lean` imports
`BurmanConvergenceFinal.lean`, so BCF cannot directly call this theorem without
creating an import cycle. To use it for the final re-entry composition, either
move the odd Phase B driver or its required kernel below/into BCF, or put the
completed all-resetting re-entry/final composition in a later module and then
remove the BCF-local open theorem.

## 2026-05-17 Late Update 3

Current actual source-level placeholder audit is still exactly one real
`sorry`, now around:

```text
SSExactMajority/Convergence/BurmanConvergenceFinal.lean:9543
```

New Phase-A/no-phi plumbing added in `BurmanConvergenceFinal.lean`:

- `runPairs_preserves_noPhi_of_pairNoPhiSafe`
- `phaseA_discharge_noPhi`

This strengthens the existing structural Phase A wrapper from
`FreshRankingStart + ResAns` to:

```lean
FreshRankingStart C₁ ∧
ResAns m₀ C₁ ∧
(∀ w, (C₁ w).1.answer ≠ .phi) ∧
majorityAnswer C₁ = majorityAnswer C
```

Remote uisai1 single-file verification:

```text
/tmp/ssem-build/bcf-phaseA-nophi-20260517-231345.log
remote-exit 0 Sun May 17 23:14:27 CDT 2026
```

The remaining final-sorry chain is unchanged:

```lean
hMedCorrectExit
  <- hMedCorrectExit_from_reservoir_entry_and_reset_leaf
       hEntry hLeaf

hEntry
  <- med_correct_live_InSswap_to_reservoir_entry_from_seed_and_reentry
       hDmax1 hSeedPrefixEntry hReentry

hLeaf
  <- reservoir_reset_leaf_from_seed_and_reentry
       hDmax1 hSeedPrefixReservoir hReentry
```

The still-open concrete obligations are:

- `hReentry : AllResettingUniformToInSswapResAnsPhiZero Rmax Emax Dmax hn`
- `hSeedPrefixEntry : MedCorrectLiveProducesCorrectSeedOrProgress Rmax Emax Dmax hn`
- `hSeedPrefixReservoir : ReservoirCaseProducesCorrectSeedOrProgress Rmax Emax Dmax hn`

## 2026-05-17 Late Update 4

Added two small green reductions in `BurmanConvergenceFinal.lean`:

- `correctResetSeed_of_timer_zero_wrong_nonexceptional`
  - parity-splits the already-proven odd/even reset triggers into one
    reusable `CorrectResetSeed` wrapper.
- `hMedCorrectExit_from_reentry_and_seed_prefixes`
  - composes:
    `hReentry`
    + `MedCorrectLiveProducesCorrectSeedOrProgress`
    + `ReservoirCaseProducesCorrectSeedOrProgress`
    into the exact local `hMedCorrectExit` shape.

Both are verified by local single-file Lean:

```text
lake env lean SSExactMajority/Convergence/BurmanConvergenceFinal.lean
exit 0
```

Remote uisai1 single-file checks:

```text
/tmp/ssem-build/bcf-wrapper-20260517-232230.log
remote-exit 0 Sun May 17 23:23:18 CDT 2026

/tmp/ssem-build/bcf-composite-20260517-232651.log
remote-exit 0 Sun May 17 23:27:36 CDT 2026
```

Current source-level placeholder audit is still exactly one real `sorry`, in
the local `hMedCorrectExit` proof inside `burmanConvergence_concrete`.

## 2026-05-17 Late Update 5

Added two green timer-zero median-correct seed helpers:

- `correctResetSeed_of_median_correct_timer_zero_wrong_nonexceptional`
  - from `InSswap`, median correct, median timer `0`, and one wrong agent
    avoiding median/max/upper ranks, returns `CorrectResetSeed`.
- `med_correct_timer_zero_seed_or_wrong_exceptional`
  - same median-correct timer-zero setup plus `wrongAnswerCount > 0`;
    either returns `CorrectResetSeed`, or isolates a wrong non-median agent
    whose rank is exceptional (`n` or `n / 2 + 1`).

Local verification:

```text
lake env lean SSExactMajority/Convergence/BurmanConvergenceFinal.lean
exit 0
```

Remote uisai1 verification started:

```text
/tmp/ssem-build/bcf-medtimer0-20260517-233307.log
remote-exit 0 Sun May 17 23:33:51 CDT 2026

/tmp/ssem-build/bcf-exceptional-20260517-233719.log
remote-exit 0 Sun May 17 23:38:05 CDT 2026
```

The remaining mathematical work is the exceptional-rank branches and the
positive-timer drain that gets the median timer down to `0`.

## 2026-05-17 Late Update 6

Tightened the timer-zero median-correct reset helper:

- Removed the unnecessary `wrong rank ≠ n` hypothesis from the underlying
  reset-trigger route.  The trigger proof never used it; max-rank wrong
  agents are valid reset partners in this timer-zero branch.
- Added `correctResetSeed_of_timer_zero_wrong_nonupper`.
- Strengthened `med_correct_timer_zero_seed_or_wrong_exceptional`: its
  actual remaining exceptional case is now the even upper-median rank
  `n / 2 + 1`; max rank is no longer exceptional for this helper.

Local single-file verification:

```text
lake env lean SSExactMajority/Convergence/BurmanConvergenceFinal.lean
exit 0
```

Remote uisai1 single-file verification:

```text
/tmp/ssem-build/bcf-timer0-nonupper-clean-20260517-235435.log
remote-exit 0 Sun May 17 23:55:25 CDT 2026
```

Source-level placeholder audit is still exactly one real `sorry`, in the
local `hMedCorrectExit` proof inside `burmanConvergence_concrete`.

## 2026-05-18 Update 10

Phase-A dormant-to-fresh answer-preservation route is now green in BCF.

Added local one-step kernels:

- `step_both_resetting_pos_preserves_uniform_answer`
- `step_dormant_dt_decrease_preserves_uniform_answer`
- `step_dormant_leader_low_dt_preserves_uniform_answer`
- `step_dormant_follower_low_dt_preserves_uniform_answer`
- `step_settled_meets_dormant_preserves_uniform_answer`
- `step_dormant_leader_unsettled_preserves_uniform_answer`

Added multi-step dormant route:

- `phase3bc_from_awakening_uniform_answer`
- `phase3a_to_awakening_uniform_answer`
- `dormant_to_FreshRankingStart_uniform_answer`
- `dormant_uniform_to_FreshRankingStart_resAns_noPhi`

Meaning: once a configuration is already `IsDormantConfig` and all
answers are uniform `m₀ = majorityAnswer C`, Phase A now gives
`FreshRankingStart ∧ ResAns m₀ ∧ noPhi ∧ majorityAnswer preserved`.

Local single-file verification:

```text
lake env lean SSExactMajority/Convergence/BurmanConvergenceFinal.lean
exit 0
```

Remote uisai1 single-file verification so far:

```text
/tmp/ssem-build/bcf-phaseA-step-kernels-20260518-030437.log
remote-exit 0 Mon May 18 03:05:22 CDT 2026

/tmp/ssem-build/bcf-phase3bc-uniform-20260518-030754.log
remote-exit 0 Mon May 18 03:08:38 CDT 2026

/tmp/ssem-build/bcf-dormant-fresh-uniform-20260518-031721.log
remote-exit 0 Mon May 18 03:18:05 CDT 2026
```

Latest endpoint wrapper remote verification:

```text
/tmp/ssem-build/bcf-dormant-phaseA-endpoint-20260518-031957.log
remote-exit 0 Mon May 18 03:20:42 CDT 2026
```

Remaining Phase-A gap: bridge arbitrary uniform all-`Resetting` to the
dormant condition while preserving uniform answer/noPhi, or otherwise
produce the full safe Phase-A certificate directly.

Current source-level placeholder audit remains exactly one real `sorry`:

```text
SSExactMajority/Convergence/BurmanConvergenceFinal.lean:13097
```

## 2026-05-18 Update 8

Current continuation is Codex-only; do not wait on family/channel output.

Added two green BCF helpers:

- `allResettingUniformToInSswapResAnsPhiZero_of_consensus`
  - turns any uniform all-`Resetting` consensus reachability theorem into
    the required `AllResettingUniformToInSswapResAnsPhiZero` endpoint.
  - This is only an endpoint wrapper; it cannot be used with
    `all_resetting_uniform_reaches_consensus_noncircular` inside the
    current `hReentry`, because that would make the existing
    `hMedCorrectExit` construction circular.
- `dormant_to_FreshRankingStart`
  - composes `phase3a_to_awakening` and `phase3bc_from_awakening`.
  - It is structural only; answer/no-`.phi` preservation still needs the
    safe Phase-A certificates consumed by `phaseA_discharge_noPhi`.

Verified locally with the allowed single-file command:

```text
lake env lean SSExactMajority/Convergence/BurmanConvergenceFinal.lean
exit 0
```

Verified on uisai1 single-file:

```text
/tmp/ssem-build/bcf-endpoint-wrapper-20260518-023208.log
remote-exit 0 Mon May 18 02:32:55 CDT 2026

/tmp/ssem-build/bcf-dormant-fresh-20260518-024149.log
remote-exit 0 Mon May 18 02:42:36 CDT 2026
```

Placeholder audit remains exactly one source-level `sorry`:

```text
SSExactMajority/Convergence/BurmanConvergenceFinal.lean:12412
```

## 2026-05-18 Update 9

Added one more green Phase-A prefix wrapper in
`SSExactMajority/Convergence/BurmanConvergenceFinal.lean`:

- `all_resetting_uniform_normalize_resAns_noPhi`
  - from uniform all-`Resetting` with `m₀ = majorityAnswer C`, runs the
    existing normalizer and returns an all-`Resetting` endpoint carrying
    `ResAns m₀`, no `.phi`, and preserved `majorityAnswer`.
  - This is still a prefix only; it does not yet reach
    `FreshRankingStart`.

Local single-file verification:

```text
lake env lean SSExactMajority/Convergence/BurmanConvergenceFinal.lean
exit 0
```

Remote uisai1 single-file verification:

```text
/tmp/ssem-build/bcf-normalize-wrapper-20260518-025554.log
remote-exit 0 Mon May 18 02:56:39 CDT 2026
```

Current source-level placeholder audit remains exactly one real `sorry`:

```text
SSExactMajority/Convergence/BurmanConvergenceFinal.lean:12447
```

## 2026-05-18 Update 7

Zinan/family collaboration is no longer active for this session; continue
from local project state only.

Added endpoint wrapper:

```lean
allResettingUniformToInSswapResAnsPhiZero_of_consensus
```

It packages any already-proven uniform all-`Resetting` consensus
reachability into the `AllResettingUniformToInSswapResAnsPhiZero`
endpoint by converting `IsConsensusConfig` to `InSswap`, `ResAns`, and
`phiCount = 0`.

Verification:

```text
local:  lake env lean SSExactMajority/Convergence/BurmanConvergenceFinal.lean
        exit 0

remote: /tmp/ssem-build/bcf-endpoint-wrapper-20260518-023208.log
        remote-exit 0 Mon May 18 02:32:55 CDT 2026
```

Current source-level placeholder audit remains exactly one real `sorry`:

```text
SSExactMajority/Convergence/BurmanConvergenceFinal.lean:12383
```

## 2026-05-18 Update 5

Added the live-timer drain kernels in
`SSExactMajority/Convergence/BurmanConvergenceFinal.lean`:

- `step_at_median_max_no_swap_odd_explicit`
- `step_at_median_max_no_swap_odd_explicit_preserves_InSswap`
- `odd_timer_descent_to_one_explicit`
- `step_at_even_lower_max_timer_ge_two`
- `step_at_even_lower_max_timer_ge_two_preserves_InSswap`
- `even_lower_timer_descent_to_one`

The odd kernel removes the old `input = A` restriction by taking the
no-swap condition explicitly, so it also covers odd majority-B states.
The even kernel handles lower-median/max pairs with timer at least two;
no answer-agreement hypothesis is needed because the post-decrement timer
is still nonzero.  Both multi-step drain lemmas land exactly at timer one.

Remote uisai1 single-file verification:

```text
/tmp/ssem-build/bcf-odd-drain-explicit-20260518-005924.log
remote-exit 0 Mon May 18 01:00:53 CDT 2026

/tmp/ssem-build/bcf-even-ge2-step-20260518-010219.log
remote-exit 0 Mon May 18 01:03:49 CDT 2026

/tmp/ssem-build/bcf-even-drain-20260518-010532.log
remote-exit 0 Mon May 18 01:07:00 CDT 2026

/tmp/ssem-build/bcf-drain-eq1-20260518-010815.log
remote-exit 0 Mon May 18 01:09:47 CDT 2026
```

Remaining proof work: use these drain kernels to close the
median-correct reservoir leaf by reducing arbitrary positive median
timers to the existing timer-one/timer-zero seed-or-progress cases.

## 2026-05-18 Update 6

The final local `hMedCorrectExit` hole has been reduced one layer further.
The proven seed-prefix builders are now wired into
`hMedCorrectExit_from_reentry_and_seed_prefixes`:

```lean
med_correct_live_seed_or_progress
reservoir_case_seed_or_progress
```

The single remaining source-level placeholder is now precisely:

```lean
hReentry :
  AllResettingUniformToInSswapResAnsPhiZero Rmax Emax Dmax hn
```

Remote uisai1 single-file verification after this reduction:

```text
/tmp/ssem-build/bcf-reentry-isolated-20260518-022131.log
remote-exit 0 Mon May 18 02:22:15 CDT 2026
```

Current placeholder audit remains exactly one real `sorry`:

```text
SSExactMajority/Convergence/BurmanConvergenceFinal.lean:12353
```

The remaining work is no longer the reservoir/timer seed-prefix layer.
It is the all-resetting re-entry proof:

```lean
all-Resetting uniform
  -> FreshRankingStart + ResAns + noPhi
  -> InSrank + ResAns + noPhi + median timer >= 2
  -> InSswap + ResAns + noPhi
  -> phiCount = 0
```

`allResettingUniform_from_safe_noPhi_phaseA_rank` already packages the
last two phases once Phase A and Phase B are supplied.  The missing
concrete inputs are still:

- Phase A: all-Resetting uniform -> `FreshRankingStart + ResAns + noPhi`
- Phase B: `FreshRankingStart + ResAns + noPhi -> InSrank + ResAns + noPhi + timer`

Do not use `ranking_from_all_resetting` to hide this; it does not preserve
the needed answer/no-phi endpoint data.

## 2026-05-18 Update 4

Zinan exited; current work is Codex-only.

Cleared the temporary `EndpointRepair.lean` skeleton sorries introduced by
the side channel, to avoid a duplicate
`reservoir_timer_zero_seed_or_progress_core` theorem name and keep the
project placeholder count at one.

Added green reservoir timer-zero core infrastructure in BCF:

- `correctResetSeed_of_odd_timer_zero_wrong_nonmedian`
  - odd `InSswap`, median timer `0`, nonmedian wrong answer: one step gives
    `CorrectResetSeed`; unlike the mixed parity trigger wrapper it does not
    require the median answer field to already be correct.
- `even_median_pair_wrong_decision_resAns_phi_decrease`
  - generalized the even lower/upper median decision step to allow either
    endpoint to be wrong, preserving `InSswap`/`ResAns` and strictly
    decreasing `phiCount`.
- `odd_timer_zero_only_median_wrong_resAns_phi_decrease`
  - odd `InSswap + ResAns + phiCount>0`, timer-zero median, all nonmedian
    answers correct: one no-reset decision step fixes the median `.phi` and
    reaches `phiCount = 0`.
- `reservoir_timer_zero_seed_or_progress_core`
  - removes the earlier median-answer-correctness assumption from the
    timer-zero reservoir branch.
- `reservoir_case_of_timer_zero_seed_or_progress`
  - small wrapper packaging the core for any reservoir case with an
    available timer-zero median.

Remote uisai1 single-file verification:

```text
/tmp/ssem-build/bcf-reservoir-core-20260518-004137.log
remote-exit 0 Mon May 18 00:42:23 CDT 2026

/tmp/ssem-build/bcf-timerzero-wrapper-20260518-004917.log
remote-exit 0 Mon May 18 00:50:02 CDT 2026
```

Remaining proof gap: the final `hMedCorrectExit` still needs the
median-correct/live-timer drain route.  The newly proved core discharges the
branch once a timer-zero median is available; it does not by itself drain a
positive median timer to zero while preserving the needed answer invariants.

## 2026-05-18 Update 1

Added the green upper-median progress lemma:

- `even_upper_wrong_decision_resAns_phi_decrease`
  - in the even lower/upper median pair, if the upper median is wrong
    under `ResAns (majorityAnswer C) C`, one decision step preserves
    `InSswap`, preserves `ResAns (majorityAnswer ·)`, and strictly
    decreases `phiCount`.
  - This is the progress branch needed for the remaining even
    upper-median exception after Late Update 6.

Local single-file verification:

```text
lake env lean SSExactMajority/Convergence/BurmanConvergenceFinal.lean
exit 0
```

Remote uisai1 single-file verification:

```text
/tmp/ssem-build/bcf-upper-progress-20260518-000258.log
remote-exit 0 Mon May 18 00:04:33 CDT 2026
```

## 2026-05-18 Update 2

Added the combined timer-zero reservoir lemma:

- `reservoir_med_correct_timer_zero_seed_or_progress`
  - assumptions: `InSswap`, `ResAns (majorityAnswer C) C`,
    `0 < phiCount C`, a median agent with `timer = 0`, and all median
    answers correct.
  - conclusion: a finite `runPairs` segment reaches either
    `CorrectResetSeed` or an `InSswap ∧ ResAns` endpoint with strictly
    smaller `phiCount`.
  - internally uses `med_correct_timer_zero_seed_or_wrong_exceptional`;
    the only remaining exceptional wrong rank is the even upper median,
    discharged by `even_upper_wrong_decision_resAns_phi_decrease`.

Local single-file verification:

```text
lake env lean SSExactMajority/Convergence/BurmanConvergenceFinal.lean
exit 0
```

Remote uisai1 single-file verification:

```text
/tmp/ssem-build/bcf-reservoir-timer0-progress-20260518-000651.log
remote-exit 0 Mon May 18 00:07:59 CDT 2026
```

## 2026-05-18 Update 3

Read Zinan's latest handoff:

- `HANDOFF/inbox/from-zinan-003.md` provides
  `exists_runPairs_of_execution`, converting an `execution` endpoint to a
  `runPairs` list endpoint.
- Because `EndpointRepair.lean` imports `BurmanConvergenceFinal.lean`, BCF
  cannot import that theorem without a cycle.  Added the same bridge in BCF
  under the distinct name `exists_runPairs_of_execution_bcf`.

Added two green timer-one seed wrappers:

- `correctResetSeed_of_odd_timer_one_max_no_swap_diff`
  - odd median/max, timer `1`, no swap, post-decision answer mismatch:
    one step gives `CorrectResetSeed`.
- `correctResetSeed_of_even_lower_timer_one_max_wrong`
  - even lower-median/max, timer `1`, median answer correct and max answer
    wrong: one step gives `CorrectResetSeed`.

Also wrote `HANDOFF/outbox/from-codex.md` asking Zinan to take the remaining
reservoir zero-timer core branch where median answer correctness is not
available.

Local single-file verification:

```text
lake env lean SSExactMajority/Convergence/BurmanConvergenceFinal.lean
exit 0
```

Remote uisai1 single-file verification:

```text
/tmp/ssem-build/bcf-timer1-wrappers-runpairs-20260518-002732.log
remote-exit 0 Mon May 18 00:28:23 CDT 2026
```

Source-level placeholder audit is still exactly one real `sorry`, in the
local `hMedCorrectExit` proof inside `burmanConvergence_concrete`.

## 2026-05-18 Update 11

Extended Phase-A answer preservation through the positive-resetcount + leader
subcase.

New green BCF lemmas:

- `drain_pair_rc_LF_with_u_delay_uniform_answer`
- `drain_pair_rc_LL_to_LF_zero_with_u_delay_uniform_answer`
- `drain_pair_rc_L_any_to_LF_zero_with_u_delay_uniform_answer`
- `step_L_zero_any_pos_preserves_uniform_answer`
- `drain_L_zero_any_pos_to_zero_with_anchor_delay_uniform_answer`
- `drain_positive_except_anchor_to_zero_uniform_answer`
- `all_resetting_pos_with_leader_to_dormant_uniform_answer`
- `all_resetting_pos_with_leader_uniform_to_FreshRankingStart_resAns_noPhi`

This now discharges the Phase-A endpoint for the subcase:

```lean
∀ w, (C w).1.role = .Resetting
∀ w, 0 < (C w).1.resetcount
∃ ℓ, (C ℓ).1.leader = .L
∀ w, (C w).1.answer = m₀
m₀ = majorityAnswer C
```

It reaches `FreshRankingStart` while preserving `ResAns m₀`, no `.phi`, and
`majorityAnswer`.

Local single-file verification:

```text
lake env lean SSExactMajority/Convergence/BurmanConvergenceFinal.lean
exit 0
```

Remote uisai1 verification:

```text
/tmp/ssem-build/bcf-lean-positive-phaseA-uniform-20260518-035223.log
remote-exit 0 Mon May 18 03:53:04 CDT 2026
```

Note: remote target `lake build SSExactMajority.Convergence.BurmanConvergenceFinal`
was blocked before BCF by an existing style-linter error in
`SSExactMajority/Convergence/SwapStep.lean`; the server single-file BCF
verification above is green after rebuilding enough stale dependency oleans.

Remaining source-level placeholder audit is still exactly one real `sorry`, in
`burmanConvergence_concrete`'s local `hReentry` proof.

## 2026-05-18 Update 12

Moved the odd `ResAns` ranking route into BCF so it no longer depends on
`OddRecruitDriver.lean` (which imports BCF and cannot be imported back).

New green BCF ingredients:

- `majorityOpinionOfAnswerBCF`
- `majorityCountOfAnswerBCF`
- `majorityCountOfAnswerBCF_step_eq`
- `ceilHalf_le_majorityCountOfAnswerBCF_of_majorityAnswer`
- `exists_unsettled_majority_child_of_settled_lt_majority_BCF`
- `settledCount_of_heapPrefix_BCF`
- `odd_nonmedian_recruit_ba_PairResAnsSafe_BCF`
- `odd_nonmedian_recruit_ba_PairNoPhiSafe_BCF`
- `odd_median_recruit_ba_PairResAnsSafe_of_majority_child_BCF`
- `odd_median_recruit_ba_PairNoPhiSafe_of_majority_child_BCF`
- `heapPrefix_recruit_step_with_child_BCF`
- `fresh_start_to_InSrank_ResAns_odd_BCF`
- `fresh_start_to_InSrank_ResAns_odd_majority_BCF`

This gives BCF an internal odd-n heap-prefix ranking driver:

```lean
FreshRankingStart C
ResAns m₀ C
(∀ w, (C w).1.answer ≠ .phi)
ceilHalf n ≤ majorityCountOfAnswerBCF C m₀
¬ n % 2 = 0
m₀ = .outA ∨ m₀ = .outB
```

to:

```lean
InSrank + ResAns m₀ + noPhi + majorityAnswer preserved + median timer ≥ 2
```

Local single-file verification:

```text
lake env lean SSExactMajority/Convergence/BurmanConvergenceFinal.lean
exit 0
```

Latest remote single-file verification is running in the background:

```text
/tmp/ssem-build/bcf-heap-odd-bcf-20260518-045039.log
```

The source-level placeholder audit is still exactly one real `sorry`, in
`burmanConvergence_concrete`'s local `hReentry` proof.

Additional local check after adding the majority-specialized odd wrapper:

```text
lake env lean SSExactMajority/Convergence/BurmanConvergenceFinal.lean
exit 0
```

Also adjusted the phaseA/rank composition shape so the rank phase receives
`m₀ = majorityAnswer C`, and added:

- `allResettingUniform_from_safe_noPhi_phaseA_rank_odd_BCF`

This proves the full PhaseA → odd-rank → swap composition for odd `n`, assuming
the Phase-A endpoint hypothesis.  Local single-file check after this composition
also exits 0.

Remote uisai1 single-file check for the pre-wrapper BCF state:

```text
/tmp/ssem-build/bcf-heap-odd-bcf-session-20260518-045206.log
remote-exit 0 Mon May 18 04:52:54 CDT 2026
```
