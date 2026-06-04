# codex-distail report

## 2026-06-04

Implemented `SSExactMajority/UpperBound/Time/DisruptionTail.lean`.

Closed pieces:

- `selectedAt`, `selectionCount`, and monotonic/successor lemmas for deterministic schedulers.
- `ErrorLoadCertificateAt` and `ErrorCounterStepOK`, with `ErrorLoadCertificateAt.step` proving the counter-load invariant propagates under the abstract one-step counter condition.
- `DisruptionBeforeK` and `disruption_before_K_implies_high_load`: if an error-timeout selected endpoint appears before `K` with the load certificate at the pre-step configuration, then some agent has `selectionCount γ a K ≥ Emax`.
- Scheduler-prefix high-load combinatorics:
  - `prefix_agent_high_load_has_selected_subset`
  - `prefix_agent_high_load_mass_le_choose`
  - `prefix_high_load_mass_le_union_choose`
  - `disruption_event_mass_le_union_choose`

The tail theorem is stated in the reusable finite-prefix form:

```lean
mass {ω | D ω} ≤
  (n : ENNReal) * (Nat.choose K r : ENNReal) *
    (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r)
```

under the standard finite-union and cylinder hypotheses, where the cylinder
hypothesis is exactly the independent uniform ordered-pair fact that a fixed
agent is selected on a fixed `r`-set of times with probability `(2/n)^r`.

Status note: I did not instantiate the cylinder hypothesis with a concrete
PMF/product scheduler prefix object, because the existing repo path API keeps
configuration-chain distributions but does not expose a scheduler-prefix
product PMF preserving endpoint-selection counts. The new theorem is set up so
that such an instantiation is a separate counting/product-measure lemma.

Verification:

```text
lake env lean SSExactMajority/UpperBound/Time/DisruptionTail.lean
```

passed with no warnings. `rg -n "sorry|axiom|native_decide"` on the new file
returns no matches.
