# codex-consensusA report

Status: blocked; `OW_consensusBound_of_reRank` was not proved.

Date: 2026-06-04

I checked the requested Scope-A route in
`SSExactMajority/UpperBound/Time/OptimalWindows.lean` against the available
formal lemmas.

The explicit `hReRank` hypothesis from the spec can give, via
`ProbHitWithin_ge_half_of_expectedHittingTime_le`, a half-probability return
window from a `CorrectResetSeed` or live-swap exit state to

```lean
(InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D) ∨
  IsConsensusConfig D
```

But the currently proved swap/timer window is
`swap_live_to_cons_or_crs_or_break`, whose target is only

```lean
IsConsensusConfig D ∨ CorrectResetSeed D ∨
  ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
```

This is insufficient to establish the uniform hypothesis required by
`expectedHittingTime_le_window_mul_inv` / invariant-window amplification:

```lean
∀ C, Inv C → ¬ IsConsensusConfig C →
  p ≤ ProbHitWithin P hn C IsConsensusConfig K
```

The missing formal bridge is specifically a positive finite-window lower bound
from

```lean
InSswap C ∧ MedianAnswerCorrect C ∧ MedianTimerAtLeast 1 C
```

to `IsConsensusConfig`, not merely to
`IsConsensusConfig ∨ CorrectResetSeed ∨ exit`. Without that lower bound, a
model satisfying all currently available lemmas may put all mass of the
timer-drain window on the CRS/exit branch, then use `hReRank` only to return to
the same live MAC region. That gives return/renewal but no per-cycle success
probability for consensus.

I also checked `PolynomialBound.lean`: the file explicitly records the same
quantitative gap for the CRS/epidemic path. The finite version exists, but the
polynomial CRS/all-resetting-to-consensus bound needed for this renewal remains
unavailable.

No Lean theorem was added, to avoid introducing a misleading statement or an
extra unrequested hypothesis.

Verification:

```bash
lake env lean SSExactMajority/UpperBound/Time/OptimalWindows.lean
```

Result: success. Existing warnings only:

- `OW_rankBound` uses `sorry`.
- `OW_consensusBound` uses `sorry`.
- `decision_window` has existing unused section variable warnings.
