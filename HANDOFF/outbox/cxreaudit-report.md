# Re-audit verdict: STILL-HAS-HOLE

Target audited: `SSExactMajority/UpperBound/Time/GenericKeystone.lean`, especially
`PEM_expectedParallelTime_On`, `CRSResetCompletion12Generic`, and
`OW_globalWindow_trank1_quadratic`.

I did not run `lake build`.

## 1. Non-vacuity

Verdict: **still has a vacuity hole**, but **not** because `resetReach` is the old false invariant.

Evidence that `resetReach` itself has the right shape:

- `CRSResetCompletion12Generic.resetReach` is a finite-window probability hypothesis:
  from `CorrectResetSeed C`, it requires
  `p_reset ≤ Probability.ProbHitWithin (PEMProtocol n trank Rmax ...) ... C
  (ResetCompletionTarget12 (majorityAnswer C)) K_reset`
  (`SSExactMajority/UpperBound/Time/GenericKeystone.lean:37-44`).
- `ResetCompletionTarget12 m` is exactly `EpidemicRegion m`, not a deterministic
  `CorrectResetSeed -> EpidemicRegion` implication
  (`SSExactMajority/UpperBound/Time/OptimalWindows.lean:334-340`).
- `EpidemicRegion m` really requires all agents Resetting, plus answer-invariant,
  `m ≠ .phi`, and a non-phi witness
  (`SSExactMajority/UpperBound/Time/EpidemicMechanics.lean:18-22`).
- `ProbHitWithin` is `P[T ≤ t]`, i.e. the finite-prefix hit event
  (`SSExactMajority/Probability/ExpectedTime.lean:860-876`).

So the old `resetInv : CorrectResetSeed -> EpidemicRegion` false shortcut is not reintroduced
in `resetReach`.

However, `PEM_expectedParallelTime_On` has over-strong universal timing hypotheses:

- `h12ranking` quantifies over every `IsTimerBoundedConfig PEM_trank1_timer C`
  and demands expected hitting of
  `InSrank D ∧ MedianTimerAtLeast 35 D ∧ IsTimerBoundedConfig PEM_trank1_timer D`
  (`GenericKeystone.lean:573-581`).
- `h12reRank` also quantifies over every timer-bounded `C` with
  `¬ (InSswap C ∧ MedianTimerAtLeast 35 C)` and demands a window to
  `InSswap D ∧ MedianTimerAtLeast 35 D`
  (`GenericKeystone.lean:594-602`).

These are not faithful as stated: a `Sem`/silent consensus configuration has
`InSswap`/`IsConsensusConfig` but median timer `0`, hence is timer-bounded by `35`
and does **not** satisfy `MedianTimerAtLeast 35`.

Source facts:

- `MedianTimerAtLeast k C` means every median-rank agent has timer at least `k`
  (`SSExactMajority/UpperBound/Time.lean:112-116`).
- `InSem` extends `InStim`, and `InStim` is equivalent to `IsConsensusConfig`;
  `InSem` adds median timer `0`
  (`SSExactMajority/Convergence/Sets.lean:52-62`).
- `IsConsensusConfig.exists_median` gives a median-rank agent for `n > 0`
  (`SSExactMajority/Convergence/Sets.lean:64-75`), so an `InSem` config violates
  `MedianTimerAtLeast 35`.
- `step_preserves_consensus` and `execution_preserves_consensus` show consensus is
  preserved under execution (`SSExactMajority/Convergence/Step.lean:140-194`);
  the transition code only initializes the timer when an agent newly becomes
  Settled (`SSExactMajority/Protocol/Transition.lean:43-48`), so a settled
  consensus/`Sem` state is not a fresh-ranking timer source. In phase 4, the
  propagation code can decrement a median timer when paired with rank `n`, but it
  resets only on answer disagreement (`SSExactMajority/Protocol/Transition.lean:80-95`);
  in a consensus configuration all answers are already the majority answer
  (`SSExactMajority/Convergence/Sets.lean:48-56`).

Such a `Sem` model is not exotic: for `n ≥ 4`, assign all agents `.Settled`,
bijective ranks, rank-sorted inputs, every answer equal to `majorityAnswer C`, and
median timer `0`. These fields satisfy the definitions of `InSswap`/`IsConsensusConfig`
and `InSem`, while `IsTimerBoundedConfig 35` is immediate and `MedianTimerAtLeast 35`
fails at the median witness.

Therefore the theorem hypotheses include configurations for which the requested
timer-refresh target is not a faithful [12] ranking/re-ranking window. This makes
the theorem operationally vacuous unless these hypotheses are restricted, e.g. to
non-consensus/non-silent starts or to the actual states where the ranking window is
used. In fact the generic proof already receives `¬ IsConsensusConfig C` in `hwin`
but ignores it before calling `h12ranking` (`GenericKeystone.lean:487-499`), and
`h12reRank` is only consumed after reaching `RankTarget`
(`GenericKeystone.lean:500-525`), so the theorem statement is stronger than the proof
appears to need.

Local CRS propagation evidence supports satisfiability of a reset window in spirit:
`CorrectResetSeed` contains a rich Resetting leader with the majority answer
(`SSExactMajority/Convergence/BurmanConvergenceFinal.lean:13787-13797`), and existing
coupled-protocol lemmas give positive one-step descent of `nonResettingCount` from
CRS (`SSExactMajority/UpperBound/Time.lean:3565-3717`) and all-resetting endpoint
shape when `nonResettingCount = 0`
(`SSExactMajority/UpperBound/Time.lean:4345-4370`). But this is not a local
constructor for `CRSResetCompletion12Generic`; the generic theorem still assumes the
[12] reset window.

## 2. Genuine O(n)

Conditional arithmetic: **yes**, the window is quadratic if all window constants are
uniform constants and `p_reset` is uniformly bounded below.

Evidence:

- `OW_globalWindow n C_rank T_timer T_reset T_rank T_rerank` is
  `(2*C_rank*n*n + T_rerank) + OW_liveConsensusWindow ...`
  (`SSExactMajority/UpperBound/Time/OptimalWindows.lean:71-75`).
- `OW_liveConsensusWindow` expands to `decisionWindow n + OW_macLiveWindow n T_timer
  + (T_reset + OW_answerEpidemicWindow n + T_rank)`
  (`OptimalWindows.lean:61-65`).
- `decisionWindow n = 2*n*(n-1)`, `OW_macLiveWindow n T_timer =
  2*(T_timer*n*(n-1)+n*(n-1))`, and `OW_answerEpidemicWindow n = 2*n*n`
  (`DecisionTiming.lean:21-23`, `OptimalWindows.lean:52-59`).
- For `PEM_trank1_timer = 35` (`GenericKeystone.lean:565-566`),
  `OW_globalWindow_trank1_quadratic` proves
  `OW_globalWindow ... ≤
  (2*C_rank + C_reset + C_T_rank + C_T_rerank + 76) * n * n`
  from quadratic bounds on `K_reset`, `T_rank`, and `T_rerank`
  (`GenericKeystone.lean:640-651`).
- The final theorem divides by `n`:
  `... * (p_reset * 128⁻¹)⁻¹ / n`
  (`GenericKeystone.lean:603-610`), and `parallelTime` is sequential time divided by
  `n` (`SSExactMajority/Probability/ExpectedTime.lean:3484-3488`).

Hidden-factor caveat: `CRSResetCompletion12Generic` only states `0 < p_reset` and
`p_reset ≤ 1` (`GenericKeystone.lean:31-35`). It does not encode a uniform
lower bound on `p_reset` independent of `n`. Thus the Lean statement alone is not an
unconditional `O(n)` family theorem; it is `O(n/p_reset)` unless `[12]` supplies a
constant reset probability uniformly in `n`.

## 3. Faithful timer

The `trank = 1` timer is constant and exact:

- `PEM_trank1_timer : ℕ := 35` (`GenericKeystone.lean:565-566`).
- The protocol timer initialization uses `7 * (trank + 4)` when a median-ranked
  agent newly becomes Settled (`SSExactMajority/Protocol/Transition.lean:43-48`),
  so `trank = 1` gives `7*(1+4)=35`.
- `PEMProtocol` separates `trank` from `Rmax`
  (`SSExactMajority/UpperBound/Time.lean:37-45`), and
  `PEM_expectedParallelTime_On` instantiates `PEMProtocol n 1 Rmax ...`
  (`GenericKeystone.lean:569-610`).
- Timer boundedness is preserved with the exact bound via `generic_timer_preservation`
  (`SSExactMajority/UpperBound/Time/GenericTrank.lean:247-254`) and the theorem uses
  `7*(1+4) ≤ 35` (`GenericKeystone.lean:612-620`).

So the timer constant itself is faithful. The problem is the over-strong universal
timer-refresh hypotheses, not the value `35`.

## 4. Regression

`CRSResetCompletion12Generic` did **not** regress to the old false
`CorrectResetSeed -> EpidemicRegion` invariant. Its `resetReach` is the intended
`ProbHitWithin` window.

The regression/hole is elsewhere:

1. `h12ranking` and `h12reRank` are stated for all timer-bounded configurations,
   including silent consensus/timer-zero configurations, while their targets require
   `MedianTimerAtLeast 35`. That is an over-strong and apparently unsatisfiable
   assumption (`GenericKeystone.lean:573-581`, `594-602`).
2. The theorem’s asymptotic interpretation needs uniform constants, especially a
   uniform positive lower bound on `p_reset`; the structure only records positivity
   (`GenericKeystone.lean:31-35`).

Final classification: **STILL-HAS-HOLE**. The reset field shape is now faithful, and
the sequential window arithmetic is quadratic, but `PEM_expectedParallelTime_On` is
not yet a genuinely non-vacuous formal O(n) theorem as stated.
