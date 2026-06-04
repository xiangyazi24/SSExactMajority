# CX adversarial audit: deterministic reset vs paper reset

## Verdict

Classification: **(a) sound-but-unfaithful shortcut**, with an additional **vacuity/too-strong-hypothesis risk in the time keystone**.

The qualitative Lean theorem proves a modified/deterministically strengthened route: fresh reset seeds carry enough `resetcount` fuel to deterministically cover all non-resetting agents. That is not the paper's `Rmax = 60 log n` probabilistic epidemic argument.

I do **not** see evidence that the paper has a gap. The formalization changed the reset premise/protocol instantiation. I also do **not** think `(c)` is defensible for the current Lean chain: `Rmax = n` is not faithful to the paper's stated reset parameter, and the current time theorem is conditional on h12-style hypotheses that are not shown from [12] at `Rmax = n`.

## Q1: `CorrectResetSeed` is strictly stronger than the paper reset seed

`CorrectResetSeed` requires a seed `r` with
`nonResettingCount C < (C r).resetcount`, plus all Resetting agents have positive `resetcount` and the majority answer:

- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:13787`
- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:13789`
- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:13791`
- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:13794`

The downstream deterministic propagation lemmas explicitly use this fuel condition. `all_resetting_from_seed_aux` says a seed whose `resetcount` covers `nonResettingCount` can drive the system to all Resetting by repeatedly choosing a non-Resetting partner; the comment states each step decrements both the non-resetting count and seed fuel:

- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:994`
- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:1001`
- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:1008`
- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:1052`
- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:1060`

The one-step decrement fact is deterministic:

- `SSExactMajority/Convergence/BurmanProof.lean:3504`
- `SSExactMajority/Convergence/BurmanProof.lean:3513`
- `SSExactMajority/Convergence/BurmanProof.lean:3516`

Fresh CRS constructions discharge `nonResettingCount < Rmax` using `hRmax : n ≤ Rmax`, not a probabilistic epidemic lemma. Example:

- `SSExactMajority/UpperBound/Time/CRSEven.lean:72`
- `SSExactMajority/UpperBound/Time/CRSEven.lean:97`
- `SSExactMajority/UpperBound/Time/CRSEven.lean:109`

So Q1 answer: **yes, it is strictly stronger**. A single reset seed is made deterministically strong enough to dominate the remaining non-resetting population. That is not the paper's `Rmax = 60 log n` high-probability epidemic coverage argument.

## Q2: `Rmax = n` is not currently proved to preserve the paper's time theorem

For qualitative correctness, the final theorem is explicitly the `Rmax = n`, `trank = n` instance:

- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:16052`
- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:16057`
- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:16061`

And the concrete Burman convergence theorem requires `n ≤ Rmax`:

- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:15941`
- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:15946`
- `SSExactMajority/Convergence/BurmanConvergenceFinal.lean:15947`

For time, the current coupled time-layer explicitly sets `trank = Rmax`, and the literal instance sets both to `n`:

- `SSExactMajority/UpperBound/Time.lean:37`
- `SSExactMajority/UpperBound/Time.lean:43`
- `SSExactMajority/UpperBound/Time.lean:50`
- `SSExactMajority/UpperBound/Time.lean:54`
- `SSExactMajority/UpperBound/Time.lean:59`

The file itself warns that this literal timer range needs a separate theorem or a weakened `O(n^2)` statement:

- `SSExactMajority/UpperBound/Time.lean:7`
- `SSExactMajority/UpperBound/Time.lean:12`
- `SSExactMajority/UpperBound/Time.lean:13`

Later it states the same issue more directly: with coupled `Rmax`, the bound is `O(Rmax * n)` expected parallel time, hence `O(n^2)` when `Rmax = n`:

- `SSExactMajority/UpperBound/Time.lean:6542`
- `SSExactMajority/UpperBound/Time.lean:6545`
- `SSExactMajority/UpperBound/Time.lean:6549`
- `SSExactMajority/UpperBound/Time.lean:6553`

State count: if implemented with bounded counters, `resetcount ∈ [0,n]` would still be only `O(n)` values, and rank already has `n` values. But Lean's `AgentState` uses unbounded `ℕ` fields for counters, so the state-count claim is not formally represented by the type itself:

- `SSExactMajority/Protocol/State.lean:13`
- `SSExactMajority/Protocol/State.lean:58`
- `SSExactMajority/Protocol/State.lean:62`
- `SSExactMajority/Protocol/State.lean:64`
- `SSExactMajority/Protocol/State.lean:67`

## Q3: time-keystone hypotheses have a real too-strong/vacuity risk

`PEM_expectedParallelTime_optimal` is conditional. It assumes `n ≤ Rmax`, timer preservation, `h12ranking`, `h12resetDuration`, `h12rank`, and `h12reRank`:

- `SSExactMajority/UpperBound/Time/OptimalWindows.lean:1240`
- `SSExactMajority/UpperBound/Time/OptimalWindows.lean:1241`
- `SSExactMajority/UpperBound/Time/OptimalWindows.lean:1247`
- `SSExactMajority/UpperBound/Time/OptimalWindows.lean:1258`
- `SSExactMajority/UpperBound/Time/OptimalWindows.lean:1261`
- `SSExactMajority/UpperBound/Time/OptimalWindows.lean:1269`

`h12ranking` is passed through unchanged in `OW_rankBound`; it is not derived locally:

- `SSExactMajority/UpperBound/Time/OptimalWindows.lean:718`
- `SSExactMajority/UpperBound/Time/OptimalWindows.lean:721`
- `SSExactMajority/UpperBound/Time/OptimalWindows.lean:745`

The strongest vacuity risk is `CRSResetDuration12.resetInv`. Its type says every timer-bounded `CorrectResetSeed C` is immediately an `EpidemicRegion (majorityAnswer C) C`:

- `SSExactMajority/UpperBound/Time/OptimalWindows.lean:445`
- `SSExactMajority/UpperBound/Time/OptimalWindows.lean:447`
- `SSExactMajority/UpperBound/Time/OptimalWindows.lean:450`
- `SSExactMajority/UpperBound/Time/OptimalWindows.lean:451`

But `EpidemicRegion` requires all agents to be Resetting:

- `SSExactMajority/UpperBound/Time/EpidemicMechanics.lean:18`
- `SSExactMajority/UpperBound/Time/EpidemicMechanics.lean:20`

Fresh `CorrectResetSeed` constructions only reset the triggering pair; other agents are unchanged from `InSswap` and hence Settled. For example:

- `SSExactMajority/UpperBound/Time/CRSEven.lean:84`
- `SSExactMajority/UpperBound/Time/CRSEven.lean:95`
- `SSExactMajority/UpperBound/Time/CRSEven.lean:97`
- `SSExactMajority/UpperBound/Time/CRSEven.lean:117`
- `SSExactMajority/UpperBound/Time/CRSEven.lean:118`

That means `resetInv` is not just "unproved from [12]"; as stated, it appears false for the fresh CRS states that the same development constructs. This makes the time theorem vulnerable to vacuity through an over-strong `h12resetDuration`.

There is also a scale mismatch in the reset-window contract: `CRSResetDuration12.resetWindow` requires `2 * (n * n * (n - 1)) ≤ T_reset + 1`:

- `SSExactMajority/UpperBound/Time/OptimalWindows.lean:476`

Since the final time theorem divides the global interaction window by `n`, this lower bound alone is already quadratic parallel-time scale if used literally. The theorem can still be logically true with a huge bound, but this is not an `O(n)` optimal proof.

## Q4: bottom line

The qualitative Lean result is best read as:

> For the concrete Lean protocol with `trank = Rmax = n`, correctness follows by a deterministic fuel-dominance reset argument.

It should **not** be read as a faithful formalization of Kanaya et al.'s `Rmax = 60 log n` probabilistic reset renewal.

The time keystone is even weaker as evidence: it is conditional on h12-style hypotheses, and `h12resetDuration.resetInv` appears too strong/false for fresh CRS states. Therefore the current formalization does not establish that the paper's `[12]` reset/ranking timing lemmas are satisfiable at `Rmax = n`, nor that the paper's `O(n)` expected / `O(n log n)` w.h.p. bounds survive the Lean instantiation.

Recommended repair direction: redo the reset bridge at `Rmax = Θ(log n)` using the [12] probabilistic reset completion statement, or explicitly change the theorem statement to a different `Rmax = n`, `trank = O(1)`/uncoupled protocol and prove the corresponding timing assumptions without the `resetInv` shortcut.
