# Q50 / research1 — final action-plan validation

Yes: steps 1–4 are basically correct.

## Direct answers

1. **Plan validity:** correct, with two cautions. First, after deletion, run `rg` once more before `lake build` to catch hidden helper references/import-only fallout. Second, step 3’s one-line `nlinarith [hn4, hRmax, hm]` may still fail on `Nat` normalization; use the `m := n - 1` rewrite plus the explicit intermediate inequality fallback if needed.

2. **Helper theorem deadness:** yes, `odd_timer_one_max_diff` and `even_lower_timer_one_max_wrong` should be dead if their only callers were the deleted CRS proofs. Confirm with `rg` after deleting CRS_even/CRS_odd/ARS.

3. **timer_drain dependency on deleted helpers:** no, the restored `timer_drain` should not call those helper theorems. Its only break-to-CRS dependency should become `crs_of_InSswap_break_with_MedC`; the rest is deterministic descent, rank/timer preservation, median uniqueness, and local transition simplification.

4. **Expected sorry count:** starting from 9: delete 3 dead sorry theorems → 6; restore `PEM_expected_timer_drain` → 5; fix arithmetic `nlinarith` → **4 remaining sorry**. Those should be exactly the Time composition holes: `allR`, `epidemic`, `anyResetSeed`, and `hConsensusBound`, unless you also delete `anyResetSeed_to_consensus` as dead.

## Minor correction to step 2

Also include explicit `(i := ...) (j := ...)` arguments on `step_rank_preserved_of_InSswap` / `step_timer_le_of_InSswap` if the restored proof uses them. That is the most likely remaining v4.30 elaboration issue.

## Final recommendation

Proceed in this order: delete dead step proofs and helpers, run `rg`; restore `timer_drain` with the wrapper call; fix arithmetic; run `lake build`. Expected endpoint: **4 sorry, BUILD OK**.
