# Codex -> Zinan (outbox/2026-05-13-codex-004)

Sender: Codex (GPT-5.5)
Receiver: Zinan
Topic: inbox 004 passthrough rewrite blocked by declaration order / fresh elaboration

## What I tried

I read inbox 004 and took `HANDOFF/locks/BurmanProof.lean.lock`.

The proposed rewrite for `propagate_reset_one_step` is mathematically right:
`rankDeltaOSSR_propagate_reset` gives the rankDelta output's second role is
Resetting, so the rankDelta output cannot be both Settled, and a structural
passthrough theorem should transfer that role through `transitionPEM`.

## Blocker 1: declaration order

`propagate_reset_one_step` is around line 682.
`transitionPEM_structural_passthrough` is around line 1320.

Lean cannot use the later theorem from the earlier proof. I tried moving/copying
the passthrough theorem above `propagate_reset_one_step`, then using the exact
rewrite from inbox 004.

Result: `lake env lean SSExactMajority/Convergence/BurmanProof.lean` produced
no output for about three minutes. I killed it. This matches my previous stdin
reproductions: the passthrough proof's

```lean
unfold transitionPEM
rw [hrd]
```

path does not behave robustly under fresh elaboration.

I reverted this code change before committing.

## Blocker 2: spreader helper

For `propagate_reset_spreader_state`, inbox 004 correctly notes we also need a
rankDelta-layer fact for the first component:

```lean
(rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
(rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = s.resetcount - 1
```

I tried proving this by unfolding only `rankDeltaOSSR`, `propagateReset`, and
`processAgent`, with `hDmax : 1 < Dmax`. The proof again expanded into a huge
nested `if t.role = Resetting then ... else ...` term and left large goals.
No clean proof was found in this round.

## Blocker 3: line 696 calc fix not independently useful yet

The suggested calc replacement for the initial `by omega` in
`phase2_propagate_reset` is locally sensible, but the file still cannot reach
that point cleanly while `propagate_reset_one_step` /
`propagate_reset_spreader_state` are unresolved. I did not commit an untested
partial edit.

## Current repository change

Only this outbox file is committed in this round. No Lean code was changed.

## Suggested next move

I think the practical next step is to stop trying to use
`transitionPEM_structural_passthrough` from earlier proofs unless we move it and
first make that theorem itself fresh-build clean.

Two possible routes:

1. Put a small, admitted local helper immediately before the Phase 2 lemmas:

```lean
theorem transitionPEM_rankDelta_second_resetting_role ...
```

and use it to unblock the cascade, marking it as the same `transitionPEM`
structural gap.

2. Refactor only the needed `transitionPEM` shape into a small lemma in
`Protocol/Transition.lean`, close to the definition, where it can be proved
before `BurmanProof.lean` imports it.

No Lean/lake process is left running.

— Codex
