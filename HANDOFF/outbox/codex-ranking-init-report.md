2026-06-03 start: read HANDOFF/codex-ranking-init-spec.md. Scope is one new Lean file `SSExactMajority/UpperBound/Time/RankingInit.lean`; verification command is `PATH=$HOME/.elan/bin:$PATH lake env lean SSExactMajority/UpperBound/Time/RankingInit.lean`.
2026-06-03 observation: the requested theorem as written has no `delaytimer` bound. `AgentState.delaytimer` is a plain `Nat`; `IsTimerBoundedConfig` only bounds `timer`. Since `processAgent` with both partners Resetting and rc=0 decrements `delaytimer` until it reaches zero, a bound independent of the initial `delaytimer` is not derivable from the stated hypotheses. I will try an adjusted nontrivial theorem with an explicit `∀ w, delaytimer ≤ Dmax` hypothesis.
2026-06-03 verification: created `SSExactMajority/UpperBound/Time/RankingInit.lean` with the requested target predicate `RankingInitTarget` and the sanity lemma `not_rankingInitTarget_of_all_resetting`; it contains no `sorry`, no `axiom`, no `native_decide`. Verified with `PATH=$HOME/.elan/bin:$PATH lake env lean SSExactMajority/UpperBound/Time/RankingInit.lean`.

2026-06-03 final status: BLOCKED-at-statement.

Precise blocker:

The target statement from the handoff cannot be proved as stated:

```lean
(hBounded : IsTimerBoundedConfig (7 * (Rmax + 4)) C)
```

bounds only `(C w).1.timer`; it does not bound `(C w).1.delaytimer`. In `SSExactMajority/Protocol/State.lean`, `delaytimer : ℕ` is an unbounded field. In `SSExactMajority/Protocol/RankDelta.lean`, `processAgent` on a Resetting rc=0 agent with a Resetting partner takes the branch

```lean
{ s with delaytimer := s.delaytimer - 1 }
```

and fires `resetOSSR` only when the decremented `delaytimer = 0`.

Therefore, for any proposed polynomial bound `B = c * Dmax * n * n`, choose an all-Resetting, rc=0, unique-L, correct-answer configuration with every `delaytimer = B + 2` and `timer = 0`. It satisfies all displayed hypotheses in the handoff, including `IsTimerBoundedConfig (7 * (Rmax + 4)) C`, but no agent can leave `.Resetting` in fewer than `B + 2` participations of that agent, and in particular no target state `FreshRankingStart ∨ IsConsensusConfig ∨ InSrank` can occur before more than `B` sequential steps. The requested uniform expected-hitting-time upper bound is thus false without an initial delaytimer bound.

Missing assumption/lemma needed to proceed:

```lean
hDelayBounded : ∀ w : Fin n, (C w).1.delaytimer ≤ Dmax
```

or a stronger bounded-config hypothesis that includes `delaytimer`, such as `IsBoundedConfig ... C`, plus corresponding step-preservation and descent lemmas for the mixed post-conversion region. A second nontrivial lemma is also needed after the first agents leave Resetting: arbitrary scheduler steps between already non-Resetting agents can start heap recruitment before all Resetting agents have converted, so the invariant for a coupon-collector proof must either include partial `HeapPrefix` states with residual Resetting agents or treat that region as a separate goal with its own expected-time bound.
