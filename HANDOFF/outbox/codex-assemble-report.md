# codex-assemble report

Status: `OW_consensusBound` is closed modulo one explicit cited [12] hypothesis
`hRank12`. No new `sorry`/axiom/native_decide was introduced; the existing
`OW_rankBound` `sorry` remains unchanged.

Files changed:
- `SSExactMajority/UpperBound/Time/OptimalWindows.lean`

Added endpoint/window definitions:

```lean
def OW_silenceEndpoint {n : ℕ} (C : Config (AgentState n) Opinion n) : Prop :=
  InSswap C ∧ ResAns (majorityAnswer C) C ∧ phiCount C = 0

def OW_restartBranch {n : ℕ} (C : Config (AgentState n) Opinion n) : Prop :=
  CorrectResetSeed C ∨ ¬ (InSswap C ∧ MedianTimerAtLeast 1 C)

def OW_swapWindow (n Rmax : ℕ) : ℕ :=
  2 * (n * (n - 1)) + 2 * (7 * (Rmax + 4) * n * (n - 1))

def OW_rank12Window (n Rmax : ℕ) : ℕ :=
  Rmax * n * n

def OW_consensusExpectedSteps (n Rmax : ℕ) : ℕ :=
  8 * (OW_swapWindow n Rmax + OW_rank12Window n Rmax)
```

Exact `hRank12` form consumed by `OW_consensusBound`:

```lean
(hRank12 :
  ∀ C : Config (AgentState n) Opinion n,
    IsTimerBoundedConfig (7 * (Rmax + 4)) C →
    OW_restartBranch C →
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C OW_silenceEndpoint
          (OW_rank12Window n Rmax))
```

Renewal structure formalized:
- timer-bounded invariant is the outer invariant for
  `expectedHittingTime_le_window_mul_inv_of_invariant`;
- if a bounded non-consensus state is live (`InSswap ∧ MedianTimerAtLeast 1`),
  `swap_live_to_cons_or_crs_or_break` gives probability `1/4` to hit
  `IsConsensusConfig ∨ CorrectResetSeed ∨ ¬ live`, with timer bounded threaded by
  `ProbHitWithin_eq_and_inv_of_invariant`;
- from a consensus branch, success is immediate;
- from a CRS/exit branch, `hRank12` gives probability `1/2` to hit
  `OW_silenceEndpoint`;
- `isConsensusConfig_of_InSswap_phiCount_zero` maps `OW_silenceEndpoint` to
  `IsConsensusConfig`;
- product probability is `1/8`, and `window_mul_inv` gives
  `E[T] ≤ OW_consensusExpectedSteps n Rmax`.

Because the proven swap window is larger than the old `10 * Rmax * n * n`
target, the consensus bound is now the explicit renewal polynomial
`OW_consensusExpectedSteps`. `PEM_expectedParallelTime_optimal` was updated to
take the same `hRank12` and use
`OW_globalWindow n Rmax = (2 * Rmax * n * n + 4 * n * n)
  + 2 * OW_consensusExpectedSteps n Rmax`.

Verification:

```text
lake env lean SSExactMajority/UpperBound/Time/OptimalWindows.lean
```

exited 0. Remaining warnings are the pre-existing `OW_rankBound` `sorry` and the
existing unused-section-variable warning on `decision_window`.
