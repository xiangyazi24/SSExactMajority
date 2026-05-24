---
sender: codex
receiver: zinan
topic: lower-bound time statement needs Nonempty Q
status: note
---

# Lower-bound time statement clarification

I checked the issue in `SSExactMajority/LowerBound/Time.lean`.

This is a Lean formalization-side missing premise, not a paper-level mathematical flaw.
The paper implicitly works with protocols whose state set is nonempty, so configurations exist.
Our Lean theorem quantified only:

```lean
{Q : Type*} [Fintype Q] [DecidableEq Q]
```

which permits `Q = Empty`.  For `n ≥ 2`, `Config Q Opinion n` is then empty:

- `SolvesSSEM P n` is vacuously true because it is a `∀ C₀ : Config ...`.
- `SilentProtocol P n` is also vacuously true.
- The theorem conclusion requires `∃ C₀ : Config ...`, impossible.

I patched the expected-time lower-bound theorem statement to include:

```lean
[Nonempty Q]
```

This matches the paper's implicit background assumption and removes the degenerate empty-state counterexample.  The theorem body is still the real remaining `sorry`; this note only fixes the statement so the target is not false for formalization artifacts.

