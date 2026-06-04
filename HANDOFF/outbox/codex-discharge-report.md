# codex-discharge report

Status: added a verified CRS-to-silence composition skeleton in
`SSExactMajority/UpperBound/Time/OptimalWindows.lean`.

Added:

- `OW_rankedEpidemicEndpoint m`:
  `InSswap ∧ EpidemicPhiGoal m ∧ majorityAnswer = m`.
- `OW_silenceEndpoint_of_rankedEpidemicEndpoint`:
  the proven silence link from a ranked uniform/no-phi endpoint to
  `OW_silenceEndpoint`; no [12] timing hypothesis is used.
- `epidemic_phiCount_to_zero_window_ge_half`:
  Markov-window wrapper around the proven
  `epidemic_phiCount_to_zero_expected_le`.
- `CRS_to_silence_of_rank12`:
  from `CorrectResetSeed`, it invokes the proven epidemic descent, then composes
  the rank window through `ProbHitWithin_add_ge_mul`, and finally applies the
  silence link.

Important probability obstruction:

The faithful composition exposes a product constant.  The epidemic theorem plus
Markov gives an epidemic window probability `1/2`; a [12] rank window of
probability `1/2` then gives only `1/4` for the composed silence window.  The
new theorem therefore has an explicit product premise

```lean
(hProduct : ((2 : ENNReal)⁻¹) ≤ ((2 : ENNReal)⁻¹) * rankProb)
```

so the old `hRank12 : 1/2 ≤ ProbHitWithin ... OW_silenceEndpoint ...` is not
derivable from a faithful `1/2` epidemic window plus a faithful `1/2` rank
window.  To recover the old `1/2` restart-branch probability, the reset/epidemic
side must be probability one inside its window, or the rank-window probability
must be strengthened so the product is at least `1/2`.

This is a probability-composition obstruction, not an answer-preservation
failure: the ranked endpoint-to-silence conversion is proved.

Verification:

```text
lake env lean -o .lake/build/lib/lean/SSExactMajority/UpperBound/Time/EpidemicBound.olean -i .lake/build/lib/lean/SSExactMajority/UpperBound/Time/EpidemicBound.ilean SSExactMajority/UpperBound/Time/EpidemicBound.lean
lake env lean SSExactMajority/UpperBound/Time/OptimalWindows.lean
```

Both exited 0. Remaining warnings are the pre-existing `OW_rankBound` `sorry`
and the existing unused-section-variable warning on `decision_window`.
