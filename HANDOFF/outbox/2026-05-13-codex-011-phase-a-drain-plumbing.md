# Codex outbox 011: Phase A drain plumbing

## Status

Build is still green.

Verification run:

```bash
lake env lean SSExactMajority/Convergence/BurmanProof.lean
lake build SSExactMajority.Convergence.BurmanProof
```

Both completed with 0 errors. Warnings/sorries remain as before.

## Changes made

- Strengthened `drain_pair_rc` to expose first-endpoint leader preservation:
  `(runPairs P C L u).1.leader = (C u).1.leader`.
- Threaded the new `step_both_rc_pos` fifth field through `drain_pair_rc`:
  `h_step.2.2.2.2`.
- Updated both the one-step/base branch and recursive branch of `drain_pair_rc`
  to return the new leader-preservation conjunct.
- Updated the Phase A nonzero TODO in `all_resetting_to_dormant` to match the
  actual next induction split.

## Sorry delta

No net sorry reduction in this round. This was plumbing for the next Phase A
multi-agent drain step.

## Remaining blocker / next proof shape

The earlier blocker is resolved at the pair-drain layer: if we call
`drain_pair_rc` with `(ell, w)` and `ell` first, the resulting schedule now
preserves `ell.leader`.

Important correction: "always pair `(ell, w)`" is not literally sufficient for
the full Phase A induction, because `drain_pair_rc` still requires both endpoints
to have positive `resetcount`. Once the leader's `resetcount` reaches 0, later
drains cannot keep using `ell` unless a different helper handles an rc=0 partner.

Recommended next split:

1. If current leader `ell` has positive rc, choose another positive-rc `w`, drain
   `(ell, w)`, and use the new leader-preservation conjunct.
2. If the current leader has rc=0 and at least two nonleaders have positive rc,
   drain those two; preserve the leader witness through the "others unchanged"
   field.
3. Keep the `S.card = 1` case deferred for now. It needs pairing the lone
   positive-rc agent with an rc=0 partner while managing delaytimer.
