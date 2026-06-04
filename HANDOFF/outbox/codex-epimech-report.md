# codex-epimech report (2026-06-04)

Created `SSExactMajority/UpperBound/Time/EpidemicMechanics.lean`.

Verified:

```bash
lake env lean SSExactMajority/UpperBound/Time/EpidemicMechanics.lean
```

Result: success.

## Proven interface

Definitions/theorems added:

- `EpidemicRegion m C`: all agents Resetting, answers in `{m, phi}`,
  `m ≠ phi`, and at least one `m` carrier.
- `epidemicRegion_answerInv`: immediate projection to `EpidemicAnswerInv`.
- `epidemicRegion_phiCount_nonincrease`: protocol-level one-step
  nonincrease for `protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)`
  under the necessary `transitionPEM_prePhase4` no-both-Settled guard.
- `epidemicRegion_phiPair_descent`: strict `phiCount` descent for a
  scheduled ordered `(phi, non-phi)` pair, provided the `rankDeltaOSSR`
  output for that pair is still Resetting on both endpoints.
- `epidemicRegion_step_closed`: region closure when the same no-Phase4 guard
  holds and the caller supplies the reset-duration fact that the post-step
  roles are all Resetting.

The proof bottoms out in `transitionPEM_prePhase4` plus
`rankDeltaOSSR_answer_preserved`; the pair descent proof shows the actual
one-way `phi -> m` copy when both endpoints remain in the Resetting branch.

## Exact obstruction to the unguarded spec

The unguarded all-Resetting statement is false for the concrete
`transitionPEM`.

Reason: `rankDeltaOSSR` enters `propagateReset` when an endpoint is
Resetting, but `propagateReset` then calls `processAgent`. If an endpoint is
Resetting with `resetcount = 0`, old resetcount `0`, and low delaytimer, then
`processAgent` can call `resetOSSR` and wake that endpoint to `.Settled`
or `.Unsettled`. In that case the `transitionPEM_prePhase4` epidemic guard

```lean
a₀.role = .Resetting ∧ a₁.role = .Resetting
```

does not necessarily hold. A scheduled `(phi, m)` pair may therefore wake
instead of executing the phi-spread branch, so strict `phiCount` descent is
not derivable from `EpidemicRegion m C` alone.

Thus the epidemic mechanics are protocol-provable only while the cited
reset-duration invariant ensures the selected endpoints remain Resetting
through this step. That is exactly the extra role/branch hypothesis carried
by `epidemicRegion_phiPair_descent` and `epidemicRegion_step_closed`.
