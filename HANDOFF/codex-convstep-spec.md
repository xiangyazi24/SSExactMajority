# Codex task (uisai1): per-step conversion structural lemma (MECHANICAL — no probability)

In a NEW file `SSExactMajority/UpperBound/Time/ConvStep.lean`, prove a DETERMINISTIC
per-step lemma about a single scheduled interaction converting a Resetting rc=0 agent.
This is pure protocol unfolding — NO probability, NO descent, just `Config.step`.

## Target (adjust names to what type-checks; keep it a real structural fact)
For the coupled protocol `P = PEMProtocolCoupled n Rmax Emax Dmax hn0` and a scheduled
pair `(i, j)` with `i ≠ j`, if agent `i` is `.Resetting` with `resetcount = 0` and the
`processAgent`/`resetOSSR` firing condition holds (delaytimer = 0, OR the partner `j`
is not `.Resetting`), then after one step `(C.step P i j) i` is NO LONGER `.Resetting`
(it became `.Settled` if leader=.L, else `.Unsettled`):

```
theorem step_converts_resetting_rc0
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n) {i j : Fin n} (hij : i ≠ j)
    (hRes : (C i).1.role = .Resetting) (hRc0 : (C i).1.resetcount = 0)
    (hFire : (C i).1.delaytimer = 0 ∨ (C j).1.role ≠ .Resetting) :
    (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j i).1.role ≠ .Resetting := by
  ...
```
(If the exact firing condition / which-agent-processed differs after you unfold
`transitionPEM`/`propagateReset`, adjust the hypothesis to the TRUE condition and state
that — but keep it a genuine "this step converts agent i out of Resetting" lemma.)

## How
Unfold `Config.step` (Defs/Config.lean:42) → `transitionPEM` → `propagateReset` →
`processAgent` (Protocol/RankDelta.lean:50) → `resetOSSR` (RankDelta.lean:41). Use the
existing `processAgent`/`resetOSSR` lemmas (rc_preserved, settled_rank_zero,
leader/follower, resetOSSR_leader/follower in BurmanProof.lean:1672/1680). `simp`/`split_ifs`
on the firing conditions.

## HARD RULES
- NO `sorry`, NO `axiom`, NO `native_decide`. If blocked, report the exact goal state +
  missing lemma to `HANDOFF/outbox/codex-convstep-report.md`. Do NOT weaken to trivial.
- Touch ONLY `ConvStep.lean`. Self-verify: `PATH=$HOME/.elan/bin:$PATH lake env lean
  SSExactMajority/UpperBound/Time/ConvStep.lean`. NEVER `lake build`.
- Append progress/status to `HANDOFF/outbox/codex-convstep-report.md`.
