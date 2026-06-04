## 2026-06-03 codex global resetMass

Implemented:

- `SSExactMajority/UpperBound/Time/GlobalDrift.lean`
- root wrapper `GlobalDrift.lean` for the literal check command

Definitions and proved facts:

- `resetMass C := ∑ w, (C w).1.resetcount`.
- `resetMass_step_eq`: for an off-diagonal scheduled pair `(i,j)`, the
  post-step mass is exactly the two post-`δ` endpoint resetcounts plus the
  unchanged bystander mass.
- `resetMass_step_add_pair_eq`: equivalent pair-effect equation
  `mass(step i j) + rc_i + rc_j = mass(C) + rc'_i + rc'_j`.
- `DrainPairsAtRC C r`: ordered pairs of distinct Resetting agents both at
  resetcount `r`.
- Exact drain count:
  `|DrainPairsAtRC C r| = m_r * (m_r - 1)`, where
  `m_r = |{w : role Resetting ∧ resetcount = r}|`.
- Drain witness/count lower bound:
  two distinct agents at the same positive rc give a nonempty drain set; if
  `2 ≤ m_r`, then `2 ≤ |DrainPairsAtRC C r|`.
- Drain effect:
  for `r > 0`, `Dmax > 0`, and `p ∈ DrainPairsAtRC C r`,
  `resetMass (C.step P p.1 p.2) + 2 = resetMass C`.
  Thus each such ordered pair drops the two endpoints by one each; the ordered
  pair contribution is `-2` to `resetMass`.
- `FreshResetPairs Rmax P C`: positive-increase pairs whose two scheduled
  endpoints are post-step Resetting and have post resetcount `≤ Rmax`.
- Fresh reset max/count:
  `|FreshResetPairs Rmax P C| ≤ n(n-1)` and every such pair has
  `resetMass(step) ≤ resetMass(C) + 2*Rmax`.
- Syntactic candidate count bounds:
  `RankCollisionPairs C` and `ErrorTimeoutPairs C` each have cardinality
  `≤ n(n-1)`.

Exact per-step drift identity:

Let `N = n(n-1)`, `P = PEMProtocolCoupled n Rmax Emax Dmax hn`, and

`δ_p(C) := resetMass (C.step P p.1 p.2) - resetMass C`

as an integer pair effect.  The proved pair identity gives

`δ_(i,j)(C) = rc'_i + rc'_j - rc_i - rc_j`

for every ordered off-diagonal pair.  Therefore under the uniform scheduler,

`Δ(C) = E[resetMass after one step] - resetMass C
      = (1 / N) * ∑_{p ∈ OffDiagonalPairs n} δ_p(C)`.

The useful proved upper bound on the clean drain subfamily is:

`∑_{p ∈ DrainPairsAtRC C r} δ_p(C) = -2 * |DrainPairsAtRC C r|`

for every `r > 0`.  Fresh positive reset pairs contribute at most
`2*Rmax` each and have count at most `N`.

Conclusion for `IsBoundedConfig`:

There is no per-step negative drift inequality

`Δ(C) ≤ -ε`

for `resetMass` on all non-goal `IsBoundedConfig` states.  The obstruction is
not only collision/error fresh resets.  `propagateReset` synchronizes two
Resetting endpoints to `max(rc_i - 1, rc_j - 1)`.  Thus:

- equal positive rc gives clean drain: pair effect `-2`;
- unequal Resetting rc can increase mass:
  if `rc_i ≥ rc_j`, the pair effect is
  `2*(rc_i - 1) - rc_i - rc_j = rc_i - rc_j - 2`;
- Resetting positive rc meeting a non-Resetting endpoint can also increase
  mass: from `r` to `2*(r-1)`, pair effect `r - 2`.

On `IsBoundedConfig M` with
`M = 7*(Rmax+4)+Emax+Dmax`, those non-fresh synchronization increases can be
as large as `M-2`, so they are not bounded by the fresh-reset `2*Rmax` term.
The only unconditional per-step compensator-style bound available from the
proved endpoint bound is the crude positive-part bound `δ_p(C) ≤ 2*M` for any
off-diagonal pair whose post-state remains `IsBoundedConfig M`.

So `resetMass` cannot be the global Lyapunov component with a standalone
per-step negative drift on `IsBoundedConfig`.  Fresh resets and resetcount
synchronization need a global total-increase compensator, or the reset
component must be replaced by a level/max/exponential reset potential that
charges upward synchronization.

Verification:

```bash
PATH=$HOME/.elan/bin:$PATH lake env lean SSExactMajority/UpperBound/Time/GlobalDrift.lean
PATH=$HOME/.elan/bin:$PATH lake env lean -o .lake/build/lib/lean/SSExactMajority/UpperBound/Time/GlobalDrift.olean -i .lake/build/lib/lean/SSExactMajority/UpperBound/Time/GlobalDrift.ilean SSExactMajority/UpperBound/Time/GlobalDrift.lean
PATH=$HOME/.elan/bin:$PATH lake env lean GlobalDrift.lean
rg -n "sorry|axiom|native_decide" GlobalDrift.lean SSExactMajority/UpperBound/Time/GlobalDrift.lean
```

All Lean checks passed; forbidden-construct grep had no matches.
