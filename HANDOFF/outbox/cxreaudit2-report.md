# Round 2 re-audit verdict: STILL-HAS-HOLE

Target: `SSExactMajority/UpperBound/Time/GenericKeystone.lean` at HEAD
`e8c864c`. I did not run `lake build`.

## Summary

The two previously reported holes are locally addressed:

- The ranking/reranking timer-35 vacuity from silent consensus states is fixed by
  adding `IsConsensusConfig` escape targets.
- The explicit corollary pins `p_reset = 1/2` and proves a literal
  `K * n` bound with `K = PEM_On_explicit_linearConstant ...`.

But a different over-strong hypothesis remains in both the fixed theorem and the
explicit corollary: `h12rank` is universally quantified over all
`m, D` satisfying `EpidemicPhiGoal m D`, while the target
`OW_rankedEpidemicEndpoint m` additionally requires `majorityAnswer = m`.
Since `majorityAnswer` is input-determined and invariant under execution, this
is unsatisfiable for configurations whose answers are all `m` but whose input
majority is a different answer.

Final classification: **STILL-HAS-HOLE**.

## Prior Hole 1

The consensus escape is present and the renewal treats it as done.

Evidence:

- Generic ranking target is now
  `(InSrank ∧ MedianTimerAtLeast 35 ∧ timer-bounded) ∨ IsConsensusConfig`
  (`SSExactMajority/UpperBound/Time/GenericKeystone.lean:243-253`).
- Generic rerank target is now
  `(InSswap ∧ MedianTimerAtLeast 35) ∨ IsConsensusConfig`
  (`GenericKeystone.lean:266-276`).
- The `trank = 1` theorem exposes the same escaped targets
  (`GenericKeystone.lean:641-649`, `662-671`).
- Internally the proof uses `RankOrConsensus` and `LiveOrConsensus`
  (`GenericKeystone.lean:293-307`).
- If the ranking target is reached through `IsConsensusConfig`, the proof uses a
  zero-time hit to consensus; if it is reached through the rank-live branch, it
  continues through rerank/live/decision (`GenericKeystone.lean:532-608`).
- The final renewal remains a genuine window-to-consensus statement, consumed by
  `expectedParallelTime_le_window_mul_inv_of_invariant`
  (`GenericKeystone.lean:609-631`;
  `SSExactMajority/Probability/ExpectedTime.lean:4495-4509`).

So the specific `InSem`/timer-zero vacuity from round 1 is closed.

## Prior Hole 2

The explicit corollary is a real linear arithmetic corollary, conditional on the
named window constants being fixed constants.

Evidence:

- `PEM_On_explicit_linearConstant C_rank C_reset C_T_rank C_T_rerank =
  256 * (2*C_rank + C_reset + C_T_rank + C_T_rerank + 76)`, with no `n`
  argument (`GenericKeystone.lean:742-747`).
- `PEM_expectedParallelTime_On_explicit` fixes the reset probability in
  `CRSResetCompletion12Generic` to `((2 : ENNReal)⁻¹)`
  (`GenericKeystone.lean:754-769`).
- It assumes quadratic rank/rerank windows
  `T_rank ≤ C_T_rank*n*n` and `T_rerank ≤ C_T_rerank*n*n`
  (`GenericKeystone.lean:788-789`).
- It concludes
  `expectedParallelTimeToConsensus ≤
  ((PEM_On_explicit_linearConstant ... * n : ℕ) : ENNReal)`
  (`GenericKeystone.lean:790-796`).
- The proof uses `OW_globalWindow_trank1_quadratic`, rewrites
  `(((2⁻¹) * (128⁻¹))⁻¹) = 256`, and cancels one `n`
  (`GenericKeystone.lean:806-848`).

No residual `1 / p_reset` remains in the explicit conclusion.

## Remaining Hole

`h12rank` is still over-strong.

In `PEM_expectedParallelTime_On`, the hypothesis is:

- for all `m` and all `D`,
  `EpidemicPhiGoal m D -> 1/2 ≤ ProbHitWithin ... D (OW_rankedEpidemicEndpoint m) T_rank`
  (`GenericKeystone.lean:654-661`).

The explicit theorem repeats the same shape (`GenericKeystone.lean:770-777`).

But:

- `EpidemicPhiGoal m C` only says `phiCount C = 0` and every agent's answer is
  `m`; it does **not** say `m = majorityAnswer C`
  (`SSExactMajority/UpperBound/Time/EpidemicBound.lean:21-23`).
- `OW_rankedEpidemicEndpoint m C` requires
  `InSswap C ∧ EpidemicPhiGoal m C ∧ majorityAnswer C = m`
  (`SSExactMajority/UpperBound/Time/OptimalWindows.lean:77-82`).
- `majorityAnswer` is computed from input counts, not from answers
  (`SSExactMajority/Convergence/Silent.lean:42-48`), and agent `answer` is an
  independent state field (`SSExactMajority/Protocol/State.lean:58-64`).
- `majorityAnswer` is invariant under every protocol step and execution
  (`SSExactMajority/Convergence/Step.lean:132-139`, `196-206`).

Thus take any `n ≥ 4` configuration with inputs majority `.B` but every
agent-state answer `.outA` and no `.phi`. Then `EpidemicPhiGoal .outA D` holds,
but every future configuration has `majorityAnswer = .outB`, so
`OW_rankedEpidemicEndpoint .outA` is unreachable. The finite-window hit
probability is therefore zero; the library even has the general zero-hit lemma
for impossible targets (`SSExactMajority/Probability/ExpectedTime.lean:3621-3627`).
This contradicts the required `1/2` lower bound.

The actual composition only uses `h12rank` after reset/epidemic with
`m = majorityAnswer C` (`GenericKeystone.lean:143-180`), so the likely repair is
to restrict `h12rank` to `majorityAnswer D = m` or otherwise thread the
majority-equality condition. As stated, both the fixed theorem and the explicit
corollary still depend on an unsatisfiable global hypothesis.

## No Other New Hole Found

I did not find a new problem in the consensus-escape renewal logic or in the
explicit `K*n` arithmetic. `CRSResetCompletion12Generic.resetReach` remains a
probabilistic `ProbHitWithin` reset-completion window, not the old deterministic
`CorrectResetSeed -> EpidemicRegion` invariant (`GenericKeystone.lean:31-44`).
