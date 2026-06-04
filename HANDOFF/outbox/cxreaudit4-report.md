# ROUND 4 convergence gate re-audit report

## Verdict

**STILL-HAS-HOLE.**

Class: **over-strong reset-epidemic one-step hypotheses / missing lower-bound
dormancy invariant**.

`WellFormed_step` itself appears to be genuinely proved and the explicit
arithmetic remains `<= K*n`.  The remaining hole is that `WellFormed` only gives
upper bounds on counters.  It does not exclude all-`Resetting` epidemic states
with `resetcount = 0` and `delaytimer = 0`, where `processAgent` wakes agents
out of `.Resetting`.  But `CRSResetCompletion12Generic.epidemicStep` and
`epidemicPairDescent` are still quantified over every `EpidemicRegion`, so those
fields are not satisfiable/faithful.

I did not run `lake build`; this is source inspection only.

## What Checks Out

`WellFormed` now covers the unbounded Nat fields that caused round 3:

- `AgentState` has Nat fields `resetcount`, `timer`, `children`,
  `errorcount`, `delaytimer` at
  `SSExactMajority/Protocol/State.lean:58-68`.
- `AgentWellFormed` bounds `resetcount <= Rmax`, `errorcount <= Emax`,
  `delaytimer <= Dmax`, and `children <= 2`; `WellFormed` also includes the
  timer bound at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:28-39`.

`WellFormed_step` is a theorem, not an assumption, and I found no
`sorry`/`admit`/`axiom`/`unsafe`/`native_decide` in the inspected files.  Its
proof threads through the actual transition pieces:

- `processAgent_preserves_agent_wellformed`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:51-77`.
- `propagateReset_preserves_agent_wellformed`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:114-148`.
- `rankDeltaOSSR_preserves_agent_wellformed`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:152-166`.
- pre-phase4 / phase4 preservation:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:168-291`.
- final `WellFormed_step`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:293-327`.

The renewal also threads `WellFormed` where the main windows need it:

- `CRS_to_silence_faithful_product_generic` defines
  `ChainInv := WellFormed ... ∧ MajInv` at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:444-468`.
- reset and epidemic targets are strengthened with `ChainInv` at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:469-503`.
- `h12rank` is called with `EpidemicPhiGoal`, `WellFormed`, and
  `majorityAnswer D = m` at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:514-524`.
- the outer invariant is `WellFormed ∧ IsTimerBoundedConfig T_timer` and is
  used in the renewal at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:643-691`.

The explicit corollary still has genuine linear arithmetic:

- final statement:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:1147-1153`;
- `p_reset` pinned to `1/2`:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:1121-1124`;
- linear constant:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:1096-1101`;
- quadratic window and division cancellation:
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:1063-1074`,
  `1177-1205`.

## Remaining Hole

`CRSResetCompletion12Generic` still contains global epidemic mechanics fields
over bare `EpidemicRegion`:

- `epidemicStep`, `epidemicNonincrease`, `epidemicPairDescent` at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:349-373`.
- These are consumed by `resetCompletion_to_phiGoal_window_generic` at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:377-410`.

But `EpidemicRegion` is too weak:

- it only requires all agents are `.Resetting`, answers are in `{m, phi}`,
  `m != phi`, and some agent has answer `m`:
  `SSExactMajority/UpperBound/Time/EpidemicMechanics.lean:18-22`;
- the file itself warns that all-`Resetting` alone does not force the epidemic
  branch, because `propagateReset` may wake dormant `resetcount = 0` agents:
  `SSExactMajority/UpperBound/Time/EpidemicMechanics.lean:11-15`.

Concrete counterexample shape:

- take `n >= 4`;
- all agents have role `.Resetting`, `resetcount = 0`, `delaytimer = 0`,
  `children = 0`, timer `0`, and leader `.L`;
- at least one agent has answer `m` and at least one has answer `.phi`.

This is `WellFormed` for any nonnegative bounds, and it satisfies
`EpidemicRegion m` but not `EpidemicPhiGoal m`.

Now schedule a pair consisting of a `.phi` agent and an `m` agent.  In the reset
subprotocol:

- `processAgent` wakes a `.Resetting` agent when `resetcount = 0` and the
  updated delay timer is `0`:
  `SSExactMajority/Protocol/RankDelta.lean:50-61`;
- `resetOSSR` sends a leader `.L` to `.Settled`:
  `SSExactMajority/Protocol/RankDelta.lean:40-44`;
- `rankDeltaOSSR` enters the reset branch whenever either endpoint is
  `.Resetting`:
  `SSExactMajority/Protocol/RankDelta.lean:192-202`;
- phase 4 only runs after the pre-phase result and cannot restore the selected
  agents to all-`Resetting` in this rank-0, non-median case:
  `SSExactMajority/Protocol/Transition.lean:97-106`.

After that step, the selected agents are `.Settled`, while a `.phi` answer still
exists.  Therefore the post-state is neither `EpidemicRegion m` nor
`EpidemicPhiGoal m` (`EpidemicPhiGoal` requires `phiCount = 0` and all answers
`m`: `SSExactMajority/UpperBound/Time/EpidemicBound.lean:21-23`).

Thus `CRSResetCompletion12Generic.epidemicStep` is false for this legal
quantified instance.  `epidemicPairDescent` is also false on the same scheduled
phi/non-phi pair: the post-state is not an epidemic region and `phiCount` has
not been forced down.

This is not repaired by the new `WellFormed` restriction.  The bad state is
well-formed because the failure is a missing **lower-bound / phase-stability**
condition, not an unbounded counter.  The older coupled reset contract had
explicit phase-stability obligations such as `stepNoPhase4`, `stepAllResetting`,
and `pairRankResetting`:
`SSExactMajority/UpperBound/Time/OptimalWindows.lean:367-390`.  The generic
contract currently assumes their consequences for all `EpidemicRegion` states,
which is too strong.

## Soundness Impact

The final renewal needs a uniform post-reset epidemic-to-phi window for every
mid-state.  `ProbHitWithin_add_ge_mul` requires the second-stage lower bound for
all states satisfying the mid predicate:
`SSExactMajority/Probability/ExpectedTime.lean:3654-3664`.

`CRS_to_silence_faithful_product_generic` sets the mid predicate to
`ResetCompletionTarget12 ... ∧ ChainInv`, where `ResetCompletionTarget12` is just
`EpidemicRegion`:

- `ResetCompletionTarget12 := EpidemicRegion` at
  `SSExactMajority/UpperBound/Time/OptimalWindows.lean:338-340`;
- mid target construction at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:469-503`;
- composition use at
  `SSExactMajority/UpperBound/Time/GenericKeystone.lean:504-535`.

Since the bad all-`Resetting`, `resetcount = 0`, `delaytimer = 0` state satisfies
that mid predicate but does not satisfy the epidemic one-step assumptions, the
renewal is still not a faithful non-vacuous proof.

## Classification

Not genuine yet.  The explicit arithmetic is `O(n)`, and the previous
unbounded-counter hole is mostly addressed, but the reset-completion/epidemic
bridge still has an over-strong universal hypothesis over pathological
well-formed epidemic states.  The target or contract needs an added lower-bound
or phase-stability invariant, or the generic contract must keep the explicit
`stepNoPhase4` / `stepAllResetting` / `pairRankResetting` obligations instead of
asserting their consequences for all `EpidemicRegion`.
