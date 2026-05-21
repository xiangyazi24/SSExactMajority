# Codex outbox 013: Phase B leader dedup sweep

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

- Replaced the Phase B placeholder in `all_resetting_to_dormant` with a strong
  induction on the number of `.L` leaders.
- Proved the `k = 1` base case using `Finset.card_eq_one`.
- Proved the `k = 0` impossible case from the existing leader witness.
- Proved the `k >= 2` recursive case:
  - choose a leader `ell` and another leader `w` from `S.erase ell`;
  - apply `step_leader_dedup`;
  - show all roles stay `.Resetting`;
  - show all resetcounts stay `0`;
  - show the leader count decreases by erasing `w`;
  - recurse and append the one-step schedule.

## Remaining blocker

The only new assumptions left open are the intended delaytimer obligations:

```lean
-- TODO(dt-invariant): Phase A must carry enough delaytimer budget.
```

There are two such `sorry`s, one for `ell.delaytimer > 1` and one for
`w.delaytimer > 1`. This replaces the old whole-Phase-B `sorry`, so the net
sorry count is unchanged.

The full fix needs Phase A to carry a delaytimer lower-bound invariant, or a
separate lemma proving enough budget at `C_mid`.
