---
sender: zinan
receiver: next-session
topic: 4 remaining sorry's — protocol-specific phase proofs
status: open
---

# State

- Time.lean: 4 sorry (standalone phase theorems at lines 5006, 5021, 5040, 5081)
- ExpectedTime.lean: 0 sorry (all infrastructure proved including strong Markov, potential descent, Markov inequality)
- Build: clean
- Monte Carlo: all 4 phases verified (prob ≈ 1.0 >> thresholds)

# Formalization SOP status

- 11-point rules: documented in cc-memory/feedback_proof_standard.md
- Remediation: Steps A-D completed (read paper, simulation, multi-model collab, bug detection)
- Step E (reflection): key insight is that probReached for non-absorbing targets needs "joint event" formalization

# The 4 sorry's

Each is a `probReached` or `ProbHitWithin` lower bound for one Table 2 phase:

1. **Phase 1** (Lemma 6): probReached for InSrank from any timer-bounded config
2. **Phase 2** (Lemma 8): probReached for InTswap28 from InSrank
3. **Phase 3** (Lemma 9): probReached for InSdecTimerBounded from InSswap ∧ timer≥28
4. **Phase 4** (Lemma 11): expectedHittingTime for IsConsensusConfig from InSswap ∧ correct ∧ timer bounded

# What's blocking

The core issue for Phases 1-3: `probReached` (exact time) for non-absorbing targets requires the "joint event" argument:
```
probReached(A ∧ B, t) ≥ P(A achieved by some s ≤ t) · P(B holds throughout [0,t])
```
where A = "protocol phase completed" and B = "timer survived".

For Phase 4: `expectedHittingTime` composition via `expectedHittingTime_add_le_of_absorbing` (proved) with sub-phase expected time bounds. The sub-bounds need `expectedHittingTime_le_of_potential_descent` (proved) with protocol-specific `hNonincrease` verification.

# Available proved infrastructure

- `expectedHittingTime_add_le` (general strong Markov)
- `expectedHittingTime_add_le_of_absorbing` (absorbing version)
- `expectedHittingTime_le_of_potential_descent` (potential descent with nonincrease)
- `ProbHitWithin_ge_half_of_expectedHittingTime_le` (Markov inequality)
- `ProbHitWithin_le_probReached_of_absorbing` (absorbing conversion)
- `probReached_mono_goal`, `ProbHitWithin_mono_time`
- `consensus_probReached_eq_one` (consensus absorbing)
- `PEMProtocol_preserves_bounded` (counter-bound invariant)
- One-step descent bounds: PEM_misordered_*, PEM_median_wrong_*, PEM_richResetSeed_*

# Next steps

1. For Phase 4: verify `hNonincrease` for timer potential within InSswap ∧ timer>0 region. This requires protocol transition analysis.
2. For Phases 1-3: formalize the "joint event" tool or find alternative approach.
3. Each phase proof is ~100 lines of protocol-specific Lean.

# Paper reference

Kanaya et al. 2025, Section 5.2, Lemmas 6-12, Table 2.
PDF: projects/SSExactMajority/papers/kanaya2025.pdf pages 9-11.
