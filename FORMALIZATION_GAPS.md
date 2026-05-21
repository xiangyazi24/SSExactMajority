# Formalization Gaps: Paper vs Lean 4

Comparing Burman et al. (PODC 2021) / Kanaya et al. (2025) informal proofs
with our Lean 4 formalization in `BurmanProof.lean`.

## 1. Missing hypotheses (paper "obvious", formalization FALSE without them)

### 1a. `phase3a_to_awakening` needs `0 < Rmax` and `0 < Dmax`

**Paper says:** "After PROPAGATE-RESET, all agents are Resetting. Leader
deduplication (L,L → L,F) reduces to a single leader."

**Formalization problem:** When `Rmax = 0`, collision sets `resetcount := 0`
immediately. Two dormant leaders (rc=0, dt=0) interact → both call `resetOSSR`
→ both become Settled rank 0 BEFORE the leader dedup line fires (dedup checks
`a.role = .Resetting ∧ b.role = .Resetting`, which is false after resetOSSR).
Duplicate Settled roots → collision → reset → infinite loop. No convergence.

**Fix:** Add `(hRmax : 0 < Rmax)` and `(hDmax : 0 < Dmax)` to `phase3a_to_awakening`.
Paper has `Rmax = 60 ln n` so this is always true, but never stated as a precondition.

**ChatGPT found this** (2026-05-10).

### 1b. Timer invariant `2 ≤ timer` is too weak for `heapPrefix_recruit_step`

**Paper says:** "The median agent's timer is initialized and counts down."

**Formalization problem:** During heap construction, the even-n lower median
(rank = n/2 - 1) is the parent of the max-rank child (rank = n-1). At the
LAST recruitment step, Phase 4 of `transitionPEM` decrements the median timer.
With invariant `2 ≤ timer`, after decrement → `1 ≤ timer`, violating the
postcondition `2 ≤ timer`.

**Fix:** Use `SettledMedianTimerStrong` (3 ≤ timer) as the induction invariant.
The timer is initialized to `7*(Rmax+4) ≥ 56`, so 3 ≤ is easily maintained.
Paper doesn't discuss this edge case because the timer budget is "obviously large enough."

**ChatGPT found this** (2026-05-10).

## 2. Protocol trace boilerplate (paper "by inspection", formalization ~50 lines each)

### 2a. transitionPEM passthrough

**Paper says:** "When both agents are not Settled, Phase 4 does not fire."

**Formalization:** `transitionPEM` is an 80-line nested if-then-else with 4 phases.
Proving that Phase 2/3 preserve structural fields (role, leader, rank, children,
resetcount, delaytimer) requires:
1. `@[simp]` projection lemmas for every struct-update combination
   (`{s with answer := a}.role = s.role`, etc.) — 16 lemmas
2. `generalize hrd : rankDelta ... = rd` to freeze the rankDelta output
3. `simp only [role_with_answer, role_with_timer, ...]` to normalize
4. `simp only [h_not_both, ite_false]` to kill Phase 4
5. `split_ifs <;> rfl` for Phase 2/3 branches

Without this infrastructure, `simp_all` produces silent `sorryAx` (Lean bug/limitation
where `<;>` on failing branches generates synthetic sorry).

**Key breakthrough:** ChatGPT suggested `generalize` + `@[simp]` lemmas (2026-05-12).
Before this, each trace took ~50 lines of manual simp. After: 5 lines via
`transitionPEM_structural_passthrough`.

### 2b. rankDeltaOSSR protocol traces

Each "step" of the protocol requires proving what `rankDeltaOSSR` does to both
agents' states. Paper says "by inspection of Algorithm 1." Formalization needs:

| Helper | Paper | Lean lines |
|--------|-------|------------|
| `rankDeltaOSSR_both_dormant` (dt=0) | "both wake" | 15 |
| `rankDeltaOSSR_settled_meets_dormant` | "follower wakes" | 12 |
| `rankDeltaOSSR_dormant_leader_wakes` | "leader wakes" | 15 |
| `rankDeltaOSSR_dormant_leader_low_dt_wakes` | not in paper | 15 |
| `rankDeltaOSSR_dormant_dt_decrease` | "dt decreases" | 15 |
| `propagate_reset_one_step` | "reset spreads" | 15 |
| `propagate_reset_spreader_state` | not in paper | 15 |

Total: ~100 lines of protocol traces for facts paper treats as obvious.

### 2c. Delaytimer countdown in `phase3a_to_awakening`

**Paper says:** "After resetcounts synchronize to 0, delaytimers count down,
and agents awaken via RESET."

**Formalization:** Required well-founded induction on `dt_ℓ + dt_w₁` with
3 cases:
- Both dt > 1: use `transitionPEM_dormant_dt_decrease` (both stay Resetting)
- Leader dt ≤ 1: leader wakes via `rankDeltaOSSR_dormant_leader_low_dt_wakes`
  + structural passthrough + IsAwakeningConfig construction (~80 lines)
- Follower dt ≤ 1: 2-step proof (follower wakes first, then leader wakes
  via `dormant_leader_wakes` meeting non-Resetting partner)

The follower case required tracking ALL fields through 2 Config.step
applications (leader, role, rank, children, resetcount for BOTH agents
at each intermediate state). ~150 lines total.

## 3. API threading gaps (paper composes freely, formalization needs exact types)

### 3a. phase1 output doesn't include `resetcount = Rmax`

**Paper:** "Collision detection sets both agents to Resetting with rc = Rmax."

**Formalization:** `phase1_trigger_reset_or_InSrank` returns
`∃ w, (C' w).1.role = .Resetting` — no info about resetcount.
`phase2_propagate_reset` needs `n ≤ (C r).1.resetcount` to ensure
enough budget for spreading.

**Status:** Not yet fixed. Needs strengthening phase1's output type.

### 3b. phase2 output doesn't give `IsDormantConfig`

**Paper:** "After propagation, all agents are Resetting. Resetcounts
synchronize to 0 via the max-minus-1 rule."

**Formalization:** `phase2_propagate_reset` returns `∀ w, role = .Resetting`.
But `IsDormantConfig` also needs `∀ w, resetcount = 0` and `unique leader`.
The rc=0 convergence and leader dedup need separate proofs.

**Status:** Not yet formalized.

### 3c. Epidemic (answer propagation)

**Paper:** "During Resetting, agents with answer = φ copy the answer from
non-φ agents (lines 7-8). Since ≥ 1 agent has the correct answer, it
spreads to all."

**Formalization:** Needs to track answer field through the entire
reset-and-re-rank cycle, showing majority answer is preserved.

**Status:** Not yet formalized.

## Summary

| Category | Count | Difficulty |
|----------|-------|-----------|
| False statements (missing hypotheses) | 2 | Found by ChatGPT |
| Protocol trace boilerplate | ~7 helpers | Mechanical but verbose |
| transitionPEM passthrough | 1 general lemma | Blocked until generalize trick |
| dt countdown case analysis | 3 cases | Hardest single proof |
| API threading | 3 gaps | Needs refactoring |
| Epidemic | 1 | Not started |
