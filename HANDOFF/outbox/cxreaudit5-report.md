# ROUND 5 convergence gate re-audit report

Commit audited: `d9c6cf7`

Verdict: **STILL-HAS-HOLE**.

Class: **faithfulness regression / over-strengthened resetReach contract**.

The Lean composition from `CorrectResetSeed` to `OW_silenceEndpoint` is now formally covered, but only because `resetReach` has been strengthened to land directly in `EpidemicPhiGoal (majorityAnswer C)`. That removes the old local epidemic-step gap from the proof script by moving the answer-propagation/drain race into the cited reset window. I do not find evidence that this strengthened target is faithfully derivable from Burman [12] Lemma 3.2 / Cor. 3.5 as the reset-completion citation was previously scoped.

## Evidence

1. **Actual reset contract target is stronger than the earlier faithful reset shape.**

   In the generic keystone, `CRSResetCompletion12Generic.resetReach` now requires:

   - preconditions: `WellFormed ... C` and `CorrectResetSeed C`;
   - target: `Probability.ProbHitWithin ... (EpidemicPhiGoal (majorityAnswer C)) K_reset`.

   Evidence: `SSExactMajority/UpperBound/Time/GenericKeystone.lean:329-349`.

   The coupled legacy contract has the same strengthened target:
   `SSExactMajority/UpperBound/Time/OptimalWindows.lean:342-363`.

   This is stronger than the earlier documented reset-completion obligation, which was explicitly shaped as `ProbHitWithin` to `EpidemicRegion` / all-Resetting:

   - `HANDOFF/RESET_REARCH_DOCTRINE.md:22-26`
   - `HANDOFF/INTEGRATION_PLAN.md:4-6`
   - `HANDOFF/reset_rearch_spec.md:17-28`

2. **The source-level CRS-to-silence path has no remaining internal composition gap if the stronger resetReach is accepted.**

   `CRS_to_silence_faithful_product_generic` first turns the strengthened reset hit into a hit of
   `EpidemicPhiGoal (majorityAnswer C) ∧ ChainInv` using step invariance of `WellFormed` and `majorityAnswer`:
   `SSExactMajority/UpperBound/Time/GenericKeystone.lean:383-421`.

   It then calls `h12rank` with exactly the needed majority precondition:
   `majorityAnswer D = majorityAnswer C` comes from `ChainInv`, and is supplied at
   `SSExactMajority/UpperBound/Time/GenericKeystone.lean:422-437`.

   Finally it composes the two finite-window hits:
   `SSExactMajority/UpperBound/Time/GenericKeystone.lean:438-460`.

   So the h12rank `majorityAnswer D = m` precondition is supplied by the renewal chain. This part is sound.

3. **But the removed epidemic-step fields leave no local proof of the old `EpidemicRegion -> answer epidemic/silence` bridge.**

   The code now says the race is “part of the cited reset-completion window”:
   `SSExactMajority/UpperBound/Time/GenericKeystone.lean:331-335`.

   That is precisely the regression. The local mechanics file documents why bare all-Resetting/EpidemicRegion is not enough:
   `SSExactMajority/UpperBound/Time/EpidemicMechanics.lean:11-15`.

   The prior faithful plan was to cite [12] only for reset completion to `EpidemicRegion`, then use local epidemic mechanics for the answer epidemic:
   `HANDOFF/reset_rearch_spec.md:21-28`. Those local obligations are no longer exposed in the reset contract, and the current `resetReach` target requires answer epidemic completion directly.

4. **Other checked obligations do not expose a separate hole.**

   `WellFormed` bounds the natural fields used by the current windows: `resetcount`, `errorcount`, `delaytimer`, `children`, and the protocol timer:
   `SSExactMajority/UpperBound/Time/GenericKeystone.lean:25-39`.

   The remaining cited windows in the explicit theorem are WellFormed-restricted:
   `h12ranking`, `h12rank`, and `h12reRank` at
   `SSExactMajority/UpperBound/Time/GenericKeystone.lean:1036-1069`.

5. **The explicit O(n) arithmetic is genuine conditional on the hypotheses.**

   The quadratic global window is proved as
   `OW_globalWindow ... <= (2*C_rank + C_reset + C_T_rank + C_T_rerank + 76) * n * n`:
   `SSExactMajority/UpperBound/Time/GenericKeystone.lean:987-999`.

   The explicit theorem pins `p_reset = 1/2`, cancels the quadratic sequential window by dividing by `n`, and concludes
   `<= PEM_On_explicit_linearConstant ... * n`:
   `SSExactMajority/UpperBound/Time/GenericKeystone.lean:1033-1078` and
   `SSExactMajority/UpperBound/Time/GenericKeystone.lean:1102-1130`.

## Conclusion

This is **not** an arithmetic hole and not a missing `h12rank` majority precondition. It is a citation/faithfulness hole:

`resetReach` is now doing more than the documented [12] reset-completion window. The theorem becomes a valid conditional theorem only under a stronger external hypothesis: from `CorrectResetSeed`, hit the completed answer epidemic `EpidemicPhiGoal (majorityAnswer C)` in `O(n^2)` sequential time with constant probability. Unless Burman [12] is meant to include that full answer-propagation/drain race, the keystone is still not a genuine non-vacuous faithful explicit `O(n)` result.
