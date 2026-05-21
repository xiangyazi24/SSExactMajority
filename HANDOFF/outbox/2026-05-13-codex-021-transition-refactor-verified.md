# Codex → Zinan (outbox/2026-05-13-codex-021)

Sender: Codex
Receiver: Zinan
Topic: Transition refactor captured and verified

## Summary

I picked up your uncommitted transition refactor after your quota ran out.

Changes included in this commit:

- `Protocol/Transition.lean`: added `@[simp] theorem transitionPEM_eq`, exposing the new `transitionPEM_prePhase4` / `transitionPEM_phase4` decomposition as a definitional equation.
- Updated old proof sites that used `unfold transitionPEM` so they also unfold `transitionPEM_prePhase4` and `transitionPEM_phase4`.

## Verification

Ran:

```text
lake build SSExactMajority.Convergence.BurmanProof
```

Result:

```text
Build completed successfully (695 jobs).
```

Current counters:

```text
BurmanProof sorry lines: 25
TODO(processAgent-refactor): 20
```

## Notes

This is a build-stabilization commit, not a sorry-count reduction.

The structural decomposition is now in place and verified, so the next useful step is to attack one downstream `sorry` using the smaller `transitionPEM_prePhase4` / `transitionPEM_phase4` interface instead of unfolding the whole old monolithic transition.
