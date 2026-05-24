---
sender: codex
receiver: zinan
topic: PEM_consensus_window_success_prob
status: theorem-closed-vacuously
---

# Summary

I verified the statement in `SSExactMajority/UpperBound/Time.lean` against the
local definitions and closed the Lean theorem, but the proof is vacuous.

The issue is the hypothesis

```lean
∃ K₀ : ℕ, ∀ (C : Config (AgentState n) Opinion n) (μ : Fin n),
  InSswap C →
  (C μ).1.rank.val + 1 = ceilHalf n →
  (C μ).1.timer ≤ K₀
```

This is not a bounded-timer invariant over a restricted reachable state space.
It quantifies over every `InSswap` configuration.  Since `AgentState.timer` is
an unrestricted `ℕ`, the hypothesis is inconsistent for `n ≥ 4`.

# Verification

Files read:

- `SSExactMajority/UpperBound/Time.lean`
- `SSExactMajority/Convergence/Sets.lean`
- `SSExactMajority/Convergence/Silent.lean`
- `SSExactMajority/Protocol/State.lean`
- `SSExactMajority/Probability/ExpectedTime.lean`
- `docs/TIME_BOUND_PLAN_C.md`

Findings:

1. `pem_table2_phase_window_to_ProbHitWithin` is type-compatible with the
   target.  It can compose the five Table 2 phase probabilities into a
   `ProbHitWithin` conclusion.
2. `SemPhase = IsConsensusConfig` and `tSem = 0` is compatible with the new
   `probReached_zero_of_goal` identity phase.
3. The real missing content remains the four nontrivial phase-window bounds:
   ranking, swap, median decision, and timer/propagation.
4. The current target hypothesis `hTimerConst` is too strong: it is false in
   the current model because arbitrary `InSswap` configurations can assign any
   natural timer value to the median agent.

# Lean Change

I replaced the `sorry` in `PEM_consensus_window_success_prob` with a
contradiction proof:

- obtain `K₀` from `hTimerConst`;
- construct an all-`A`, identity-rank `InSswap` configuration `Cbad`;
- set every agent's timer to `K₀ + 1`;
- choose the median-rank agent;
- `hTimerConst Cbad μ ...` gives `K₀ + 1 ≤ K₀`, contradiction.

This proves the theorem as stated, but only because the theorem's assumptions
are inconsistent.  It should not be treated as a formalization of Kanaya Table
2's probability window.

# Build

Remote command used:

```bash
rsync -az --delete --exclude .lake/ --exclude .git/ ./ uisai1:repos/SSExactMajority/
ssh uisai1 'cd repos/SSExactMajority && PATH=$HOME/.elan/bin:$PATH lake build SSExactMajority.UpperBound.Time'
```

Result:

```text
Build completed successfully (2601 jobs).
```

`rg -n "sorry|admit" SSExactMajority/UpperBound/Time.lean` returns no matches.

# Recommended Fix

Replace `hTimerConst` with either:

1. a reachable-state invariant, e.g. timer bounded only for states reachable
   from the protocol's intended initialized/bounded state space; or
2. a local phase-window hypothesis that directly supplies the `Sdec -> Stim`
   probability bound.

The existing docs already identify the other major gap: quantitative Burman
ranking is not present in the repo and should be imported/assumed as a real
probabilistic theorem rather than derived from qualitative reachability.
