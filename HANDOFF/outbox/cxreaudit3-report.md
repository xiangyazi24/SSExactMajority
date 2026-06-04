# ROUND 3 convergence re-audit report

## Verdict

**STILL-HAS-HOLE.**

The two round-2 fixes are present and the explicit arithmetic is genuinely
linear once the hypotheses are accepted.  However, the hypotheses of
`PEM_expectedParallelTime_On_explicit` are still not all satisfiable/faithful:
the cited ranking/re-ranking/rank-after-epidemic windows are quantified over
states with only a timer bound, while `AgentState` contains unbounded natural
counter fields.  A configuration with huge positive `resetcount` is timer
bounded but cannot reach `InSswap` or `IsConsensusConfig` within any fixed
`O(n^2)` window.

I did not run `lake build`; this is source inspection only.

## What is fixed

The majority-answer precondition on `h12rank` is now present:

- `SSExactMajority/UpperBound/Time/GenericKeystone.lean:687-695` for `PEM_expectedParallelTime_On`.
- `SSExactMajority/UpperBound/Time/GenericKeystone.lean:804-812` for
  `PEM_expectedParallelTime_On_explicit`.
- `OW_rankedEpidemicEndpoint` itself requires
  `majorityAnswer C = m` at `SSExactMajority/UpperBound/Time/OptimalWindows.lean:80-82`.

The renewal chain really supplies that precondition.  In
`CRS_to_silence_faithful_product_generic`, the proof defines
`MajInv D := majorityAnswer D = majorityAnswer C` and proves it is preserved by
one protocol step using `majorityAnswer_step_eq`:

- `SSExactMajority/UpperBound/Time/GenericKeystone.lean:139-150`.
- `SSExactMajority/Convergence/Step.lean:132-138`.

It then strengthens both the reset and epidemic hit targets with this invariant:

- reset target becomes `ResetCompletionTarget12 ... ∧ MajInv` at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:151-164`;
- epidemic target becomes `EpidemicPhiGoal ... ∧ MajInv` at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:165-185`;
- the final `h12rank` call is exactly
  `h12rank (majorityAnswer C) D hD.1 hD.2` at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:202-206`.

So the old wrong-answer `EpidemicPhiGoal m D` hole is closed.

The consensus escapes also do not by themselves turn arbitrary non-progress
states into success.  `IsConsensusConfig` is a strong correct-consensus
predicate requiring all agents settled, sorted ranks, and correct answers:
`SSExactMajority/Convergence/Silent.lean:73-83`.  The zero-time uses of the consensus branch are
therefore sound, e.g. `SSExactMajority/UpperBound/Time/GenericKeystone.lean:549-564` and `624-641`.

The explicit corollary also pins the reset probability and cancels the
quadratic sequential window:

- `p_reset` is fixed to `(2 : ENNReal)⁻¹` in
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:800-803`.
- `PEM_On_explicit_linearConstant` has no `n` or `p_reset` argument:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:779-781`.
- The final bound is exactly
  `expectedParallelTimeToConsensus <= ((K * n : Nat) : ENNReal)` at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:825-831`.
- The inverse is rewritten to `256` at `SSExactMajority/UpperBound/Time/GenericKeystone.lean:855-862`, and the
  quadratic-over-`n` cancellation is at `SSExactMajority/UpperBound/Time/GenericKeystone.lean:871-883`.

Thus, conditional on the hypotheses, the arithmetic is explicit `O(n)`.

## Remaining hole

The theorem still asks the cited windows to hold on too large a state space.
`AgentState` stores several counters as plain `Nat`:

- `resetcount : Nat`, `timer : Nat`, `children : Nat`, `errorcount : Nat`,
  `delaytimer : Nat` at `SSExactMajority/Protocol/State.lean:58-68`.

The only state-shape precondition exposed by the trank=1 keystone and explicit
corollary is timer boundedness:

- `IsTimerBoundedConfig K C := forall mu, (C mu).1.timer <= K` at
  `SSExactMajority/UpperBound/Time.lean:89-90`.
- the explicit theorem starts from every `C0` satisfying only
  `IsTimerBoundedConfig PEM_trank1_timer C0` at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:825-827`.

The same timer-only weakness appears in the cited hypotheses:

- `h12ranking` quantifies over all timer-bounded configs at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:791-799`;
- `h12reRank` quantifies over all timer-bounded configs not already live at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:813-822`;
- `h12rank` has no timer/role/counter boundedness precondition at all, only
  `EpidemicPhiGoal m D` and `majorityAnswer D = m`, at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:804-812`.

Counterexample shape: fix `n >= 4` and set every agent's role to `.Resetting`,
answer to `majorityAnswer C`, timer to `0`, and `resetcount` to some
`M > T_rank + T_rerank + C_rank*n*n` (or simply `M > T_rank` for `h12rank`).
This satisfies the timer bound and, for `h12rank`, satisfies
`EpidemicPhiGoal (majorityAnswer C) C` because `phiCount = 0` and all answers
are the majority answer (`EpidemicPhiGoal` is only answers/`phiCount`:
`SSExactMajority/UpperBound/Time/EpidemicBound.lean:21-23`).

But the target requires settled/ranked structure:

- `OW_rankedEpidemicEndpoint m` requires `InSswap` at
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:80-82`;
- `InSswap` extends `InSrank`, and `InSrank` requires every agent to be
  `.Settled`, at `SSExactMajority/Convergence/Sets.lean:34-41`;
- `IsConsensusConfig` also requires every agent to be `.Settled`, at
  `SSExactMajority/Convergence/Silent.lean:73-76`.

From a positive-resetcount all-Resetting configuration, one interaction cannot
make those agents settled.  The reset branch is selected whenever either agent
is `.Resetting` (`SSExactMajority/Protocol/RankDelta.lean:192-202`); the reset synchronization step only
sets the two selected resetcounts to `max (a.resetcount - 1)
(b.resetcount - 1)` (`SSExactMajority/Protocol/RankDelta.lean:129-132`); and `processAgent` only leaves
the Resetting case when `resetcount = 0` (`SSExactMajority/Protocol/RankDelta.lean:50-61`, with the
`resetcount != 0` identity lemma at `SSExactMajority/Protocol/RankDelta.lean:63-66`).  Hence with
`M > T_rank`, after any path of length `T_rank` every agent still has positive
resetcount, so no state in the path can satisfy `InSswap` or
`IsConsensusConfig`.

Therefore

```lean
((2 : ENNReal)⁻¹) <= ProbHitWithin ... C (OW_rankedEpidemicEndpoint m) T_rank
```

from `h12rank` is false for this legal quantified instance.  The analogous
timer-bounded huge-resetcount configuration also breaks `h12ranking` and
`h12reRank`, since their targets are `InSrank ... ∨ IsConsensusConfig` and
`InSswap ... ∨ IsConsensusConfig`, respectively.

This is not a mere proof-strength issue: no finite constant `C_rank`,
`C_T_rank`, or `C_T_rerank` can make these universal hypotheses true over
unbounded `Nat` counters.  The hypotheses would need an actual bounded/well
formed state invariant, or the h12 windows must be stated only on the reachable
bounded subspace supplied by the renewal chain.

## Classification

`PEM_expectedParallelTime_On_explicit` is **not** yet a genuinely non-vacuous
explicit `O(n)` theorem.  The arithmetic is `<= K*n`, and the majority-answer
precondition is supplied, but the window hypotheses remain over-strong and
unsatisfiable over the actual Lean state type.
