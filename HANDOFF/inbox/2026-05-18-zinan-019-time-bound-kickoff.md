---
sender: zinan
receiver: codex
topic: kickoff — time-bound formalization (Theorem 3 + §5.2 quantitative)
status: open
---

# Kickoff: time-bound formalization

## Context

Qualitative half of Kanaya 2025 is **done** (`P_EM_solves_SSEM_final`,
unconditional, axioms `[propext, Classical.choice, Quot.sound]`).  The
paper's title ("Time- and Space-Optimal") implies a *time* side too.
That side is now scaffolded, not proven.

Scaffolds live outside the root import graph and use `sorry` for the
target theorems — the main library remains 0-sorry, 0-custom-axiom.
Built via explicit `lake build` targets (or `lake env lean <file>`).

## Files to read first

1. `docs/TIME_BOUND_PLAN.md` — the design plan (decisions A–D,
   sub-task breakdown, statement style).
2. `SSExactMajority/Probability/RandomScheduler.lean` — scaffold for
   uniform random pair-selection + Markov step.
3. `SSExactMajority/Probability/ExpectedTime.lean` — scaffold for
   expected hitting time + `parallelTime`.
4. `SSExactMajority/LowerBound/Time.lean` — Theorem 3 statement.
5. `SSExactMajority/UpperBound/Time.lean` — §5.2 quantitative statement.

## Your initial sub-tasks

### Sub-task A1 — fill `offDiagonalPairs_card`

`Probability/RandomScheduler.lean` has

```lean
theorem offDiagonalPairs_card (n : ℕ) :
    (OffDiagonalPairs n).card = n * (n - 1) := by
  sorry
```

This is pure counting on `Finset (Fin n × Fin n)`.  Should be doable in
~10 lines via `Finset.card_filter` + `Finset.card_product` + `Finset.card_fin`.

### Sub-task A2 — finalize `expectedHittingTime`

The current placeholder in `Probability/ExpectedTime.lean` mixes step
marginals and stopping times incorrectly.  The correct definition
needs the full path measure (canonical product `(Fin n × Fin n)^ℕ` →
`Config^ℕ`).  Two valid routes:

(α) Define stopping time `T ω = inf { t | Goal (execution P C₀ (γ ω) t) }`
    on the product space, then `expectedHittingTime = ∫ T dμ`.

(β) Use Mathlib's `ProbabilityTheory.kernel` directly: `iterate`d
    `stepDist` gives the marginal at step `t`; then `tsum` over `t` of
    `(1 - P[reach goal by t])` is the tail-sum formula
    `E[T] = ∑ P[T > t]`.

(β) is simpler in Mathlib idioms.  Pick (β) and rewrite
`expectedHittingTime`.  Verify it elaborates.

### Sub-task A3 — `SilentProtocol` definition

The placeholder in `LowerBound/Time.lean:46` is an existential per-execution
form.  Compare to Kanaya §2's definition.  If equivalent, prove the
equivalence with the existing `Config.isOutputStable`.  If not, replace.

## Communication

Once you've taken a sub-task, drop a marker file at
`HANDOFF/outbox/YYYY-MM-DD-codex-NNN-time-bound-<subtask>.md`
with the chosen approach.  I'll review and iterate before you sink hours
into Mathlib API hunting.

The harder pieces (Theorem 3 proof, §5.2 phase decomposition) wait until
A1–A3 land.  Those will likely need ChatGPT Pro for the
coupon-collector / Markov-chain lifting.

## Build verification

```bash
ssh uisai1 "export PATH=\$HOME/.elan/bin:\$PATH && cd repos/SSExactMajority && \
  lake build SSExactMajority.Probability.RandomScheduler \
             SSExactMajority.Probability.ExpectedTime \
             SSExactMajority.LowerBound.Time \
             SSExactMajority.UpperBound.Time"
```

(Note: `LowerBound.Time` and `UpperBound.Time` carry `sorry`; only their
elaboration is verified, not closure.)

## Blockers

None.  Scaffolds are committed; pick whichever sub-task A1/A2/A3 fits
first.
