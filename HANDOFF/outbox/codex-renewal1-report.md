# codex-renewal1 report

Status: blocked.  The requested `hInvStep` is false for
`Inv := IsAwakeningConfig` and
`Goal := FreshRankingStart ∨ (∃ k, 2 ≤ k ∧ HeapPrefix · k) ∨ IsConsensusConfig`.

Exact obstruction:

- Take `n = 4`.
- Let agent `0` be the unique leader root:
  `role = Settled`, `leader = L`, `rank = 0`, `children = 0`.
- Let agents `1` and `2` be followers with
  `role = Unsettled`, `leader = F`, `errorcount = 0`.
- Let agent `3` be a follower with
  `role = Resetting`, `leader = F`, `resetcount = 0`.

This configuration satisfies `IsAwakeningConfig` and is not in the
progress-inclusive goal: it is not `FreshRankingStart` because agent `3` is
still `Resetting`; it has no `HeapPrefix ≥ 2` because `HeapPrefix` requires
every role to be `Settled ∨ Unsettled`; it is not consensus because not all
agents are `Settled`.

For the pair `(1, 2)`, both endpoints are `Unsettled(errorcount = 0)`.
The concrete `rankDeltaOSSR` error-monitoring branch sends both endpoints to
`Resetting` with `leader = L`.  A temporary `#eval` through
`PEMProtocolCoupled' 4 1 1 1` confirmed the post-step roles/leaders:

```text
agent 0: Settled,   L
agent 1: Resetting, L
agent 2: Resetting, L
agent 3: Resetting, F
```

The post-step configuration is therefore not `IsAwakeningConfig` (unique
leader fails), not `FreshRankingStart`, not `HeapPrefix ≥ 2` (resetting
agents remain), and not `IsConsensusConfig` (not all settled).  Thus the
all-pair closure obligation required by
`expectedHittingTime_le_of_variable_descent_until_goal` cannot be proved with
the current invariant.

Verification run:

```text
lake env lean SSExactMajority/UpperBound/Time/EntryBound.lean
```

Result: passed with no output before any source edits.
