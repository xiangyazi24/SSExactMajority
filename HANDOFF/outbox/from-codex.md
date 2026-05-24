# From Codex -> Zinan

## Current green additions

In `SSExactMajority/Convergence/BurmanConvergenceFinal.lean` I added:

```lean
theorem correctResetSeed_of_odd_timer_one_max_no_swap_diff
theorem correctResetSeed_of_even_lower_timer_one_max_wrong
theorem exists_runPairs_of_execution_bcf
```

Local single-file verification:

```bash
lake env lean SSExactMajority/Convergence/BurmanConvergenceFinal.lean
```

passes with only the pre-existing final `sorry`.

Remote verification started:

```text
/tmp/ssem-build/bcf-timer1-wrappers-runpairs-20260518-002732.log
```

## Useful fact from your inbox #003

`exists_runPairs_of_execution` cannot be imported into BCF because
`EndpointRepair.lean` imports BCF, so I duplicated it in BCF with the name
`exists_runPairs_of_execution_bcf`.

## Specific sublemma request

Please take the reservoir core branch:

```lean
ReservoirCaseProducesCorrectSeedOrProgress
```

especially the hard subcase:

```lean
InSswap D
ResAns (majorityAnswer D) D
0 < phiCount D
∃ μ, median μ ∧ timer μ = 0
```

without assuming median answer correctness.

The existing green lemma

```lean
reservoir_med_correct_timer_zero_seed_or_progress
```

already handles the `Or.inl hMedCorrect` case. The missing branch is:
zero-timer median exists, but a median answer may be wrong or `.phi`.

Please aim for a theorem shaped like:

```lean
theorem reservoir_timer_zero_seed_or_progress_core
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hSswap : InSswap D)
    (hRes : ResAns (majorityAnswer D) D)
    (hPhi : 0 < phiCount D)
    {μ : Fin n}
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (hμ_timer : (D μ).1.timer = 0) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) D L
      CorrectResetSeed C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C' ∧
          phiCount C' < phiCount D)
```

Do not use `RankingEndpoint` for this lemma; it loses the reservoir
invariant we need.
