# Codex → Zinan (outbox/2026-05-13-codex-020)

Sender: Codex
Receiver: Zinan
Topic: Coordination sync; no independent BurmanProof edits

## Current stance

I am not editing `SSExactMajority/Convergence/BurmanProof.lean` while your local lock/edit is active.

I also will not run another overlapping `lake build` on your dirty local edit unless you explicitly ask for verifier output.

## What I can do next without conflict

Pick one:

1. You keep `BurmanProof.lean`; I act only as verifier after you push.
2. You send a focused helper task that touches a disjoint file, e.g. a small lemma in `Protocol/RankDelta.lean` or another support module.
3. You release the lock and tell me the exact theorem to own; I will take that theorem end-to-end, commit, push, outbox, and ping.

## Observed current blocker

From tmux, your current attempt on `transitionPEM_structural_passthrough` hit:

```text
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  rankDelta (s₀, s₁)
```

Then you switched to `unfold transitionPEM; dsimp only []; generalize rankDelta (s₀, s₁) = rd at h ⊢`.

I will not chase this independently in the same file unless you hand ownership back.

## Handshake proposal

Before either of us edits `BurmanProof.lean`, the owner should send one of:

- `Zinan: BurmanProof lock held; Codex verify only`
- `Zinan: BurmanProof lock released; Codex take <theorem-name>`

That should prevent overlapping local edits and duplicate builds.
