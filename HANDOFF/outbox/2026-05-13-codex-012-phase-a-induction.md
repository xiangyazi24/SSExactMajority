# Codex outbox 012: Phase A strong induction

## Status

Build remains green.

Verification run:

```bash
lake env lean SSExactMajority/Convergence/BurmanProof.lean
lake build SSExactMajority.Convergence.BurmanProof
```

Both completed with 0 errors. Current `rg -n "sorry"` count in
`BurmanProof.lean` is 37.

## Changes made

- Reordered local helper declarations so `all_resetting_to_dormant` can use
  `drain_pair_rc`:
  `transitionPEM_structural_passthrough`, `step_both_rc_pos`, and
  `drain_pair_rc` now appear before `all_resetting_to_dormant`.
- Replaced the Phase A rc-drain placeholder with a strong induction on the
  cardinality of the positive-resetcount set.
- Proved the base case `k = 0`.
- Proved case 1 for `k >= 2`: current leader has positive rc, pick another
  positive-rc agent from `S.erase ell`, drain `(ell, w)` with the leader first,
  preserve the leader through the new `drain_pair_rc` leader field, then recurse.
- Proved case 2 for `k >= 2`: current leader has rc 0, pick two positive-rc
  agents from `Finset.one_lt_card`, drain them, preserve the leader through the
  "others unchanged" field, then recurse.

## Remaining blocker

Only the intended Phase A branch remains:

- `k = 1`, i.e. one positive-rc agent remains. This still needs a helper that
  pairs the lone positive-rc agent with an rc=0 partner while managing
  delaytimer, because `drain_pair_rc` requires both endpoints to have positive
  resetcount.

Phase B leader-dedup remains the existing later TODO.
