# Codex → Zinan (outbox/2026-05-13-codex-010)

Sender: Codex
Receiver: Zinan
Topic: Phase A rc countdown base case + blocker

## What changed

- In `all_resetting_to_dormant`, replaced the raw Phase A `sorry` with a `Finset` split on
  ```lean
  S := Finset.univ.filter (fun w : Fin n => 0 < (C w).1.resetcount)
  ```
- Proved the `S.card = 0` branch:
  - schedule `L_rc = []`
  - all roles stay Resetting from `hAllReset`
  - all resetcounts are `0` by contradiction with membership in `S`
  - the existing leader witness is preserved from `hLeader`
- Kept the nonzero branch as the remaining TODO/sorry, with the intended strong-induction plan documented in code.

## Verification

- `lake env lean SSExactMajority/Convergence/BurmanProof.lean` passes.
- `lake build SSExactMajority.Convergence.BurmanProof` passes.

## Sorry delta

No net sorry reduction. This replaces the old raw Phase A sorry with a real base case plus one deferred nonzero branch.

## Blocker

The `S.card ≥ 2` induction wants to always drain `(ℓ, w)` with the current leader `ℓ` as the first endpoint. The existing
`drain_pair_rc` gives roles/rc for the two endpoints and full preservation for other agents, but it does not expose:

```lean
(runPairs P C L ℓ).1.leader = (C ℓ).1.leader
```

for the first endpoint. To finish the multi-agent induction cleanly, I think we need a wrapper lemma around `drain_pair_rc`
or a strengthened drain lemma that includes first-endpoint leader preservation when `u` is scheduled first and `(C u).1.leader = .L`.

The `S.card = 1` case remains the separately allowed deferred case: lone positive-rc agent paired with an rc=0 partner while managing delaytimer.
