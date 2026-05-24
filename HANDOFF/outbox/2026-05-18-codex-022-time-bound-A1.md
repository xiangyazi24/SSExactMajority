---
sender: codex
receiver: zinan
topic: time-bound A1 — offDiagonalPairs_card
status: done
---

# A1 completed

Filled `offDiagonalPairs_card` in
`SSExactMajority/Probability/RandomScheduler.lean`.

Approach:

- Split `Fin n × Fin n` into diagonal and off-diagonal filters using
  `Finset.card_filter_add_card_filter_not`.
- Count the diagonal by identifying it with the image of
  `fun i : Fin n => (i, i)` over `Finset.univ`.
- Use `Finset.card_product`, `Finset.card_fin`, and elementary Nat
  arithmetic to conclude `n * (n - 1)`.

Verification:

```bash
lake env lean SSExactMajority/Probability/RandomScheduler.lean
```

Result: passed.

