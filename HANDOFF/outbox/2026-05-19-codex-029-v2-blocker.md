---
sender: codex
receiver: zinan
topic: PEM_consensus_window_success_prob_v2 is still false for arbitrary Config
status: blocked-statement-false
---

# Summary

I read `HANDOFF/inbox/2026-05-19-zinan-024-corrected-targets.md` and checked
the new target

```lean
PEM_consensus_window_success_prob_v2
```

against the protocol definitions.  The vacuous `hTimerConst` problem is fixed,
but the corrected statement is still not true as stated because it quantifies
over arbitrary `Config (AgentState n) Opinion n`.

The state fields

```lean
timer resetcount delaytimer errorcount : ℕ
```

are unbounded in `AgentState`.  The new window depends only on
`c * Rmax * n * n`, but arbitrary initial configurations can contain much
larger counters.

# Concrete Counterexample Shape

Fix any proposed constant `c` and let

```lean
K = c * Rmax * n * n
```

Take an initial configuration `Cbad` where every agent is:

```lean
role       := .Unsettled
errorcount := K + 1
```

with arbitrary ranks, answers, timers, resetcounts, leaders, and inputs.

For an interaction between two non-resetting, non-settled agents,
`rankDeltaOSSR` reaches the error-monitoring branch:

```lean
if a.role = .Unsettled then
  let a'' := { a with errorcount := a.errorcount - 1 }
  if a''.errorcount = 0 then
    { a'' with role := .Resetting, resetcount := Rmax, leader := .L }
  else a''
else a
```

So an agent can lose at most one unit of `errorcount` per interaction in which
it participates.  In any length-`K` schedule, each fixed agent participates at
most `K` times.  Starting from `K + 1`, every agent still has positive
`errorcount` after `K` steps and therefore never reaches `.Settled`.

Thus after `K` steps the execution cannot satisfy `IsConsensusConfig`, whose
first field requires:

```lean
∀ v, (C v).1.role = .Settled
```

Consequently the hit probability within `K` steps is zero for this `Cbad`,
while `pemTable2SuccessProb > 0`.

# Why the Existing Phase Plan Cannot Prove v2

The Table 2 phase argument is for the intended bounded protocol state space,
not arbitrary unbounded Lean configurations.  The current v2 statement still
starts from every raw `Config`, so the first phase cannot have a uniform
constant-success finite window depending only on `Rmax` and `n`.

The same issue also affects `PEM_expected_parallel_time`: from the `Cbad`
family above, the expected time must grow with the initial `errorcount`, so it
cannot be bounded by `C * Rmax * n` uniformly over all raw configurations.

# Recommended Corrected Target

Add a well-formed/bounded-state predicate to the theorem, for example:

```lean
def PEMBoundedConfig (Rmax Emax Dmax : ℕ)
    (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ v,
    (C v).1.timer ≤ 7 * (Rmax + 4) ∧
    (C v).1.resetcount ≤ Rmax ∧
    (C v).1.errorcount ≤ Emax ∧
    (C v).1.delaytimer ≤ Dmax
```

Then either:

1. restrict the window theorem to `PEMBoundedConfig Rmax Emax Dmax C`, with a
   window depending on `Rmax`, `Emax`, and `Dmax`; or
2. prove that the protocol first re-enters such a bounded state within a
   window depending on the initial counter maxima.

As written, `PEM_consensus_window_success_prob_v2` should not be proved.
