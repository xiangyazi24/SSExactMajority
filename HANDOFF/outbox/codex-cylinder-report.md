# Codex cylinder report

Implemented `SSExactMajority/Probability/SelectionCount.lean`.

Scheduler/path measure used:

- `SSEM.Probability.schedulerPrefixPMF n hn K :
  PMF (SchedulerPrefix n K)`, where `SchedulerPrefix n K = Fin K → Fin n × Fin n`.
- Its point mass is the product
  `schedulerPrefixWeight n hn K σ = ∏ t : Fin K, uniformPair n hn (σ t)`.
- This is the minimal finite product scheduler-prefix PMF; the existing
  `nthStepDist`/configuration-chain API does not retain the selected pair at
  each step.

Main proved lemmas:

- `uniformPair_apply_ne_zero_iff`: the one-step support is exactly the
  off-diagonal pairs.
- `schedulerPrefixPMF_support`: the prefix support is coordinatewise
  off-diagonal.
- `schedulerPrefix_selectedAt_step_mass`: for a fixed step,
  `P[a selected] = 2 / n`.
- `schedulerPrefix_cylinder_selectedOn`: for fixed `T : Finset (Fin K)`,
  `P[a selected on every t ∈ T] = ((2 : ENNReal) * (n : ENNReal)⁻¹) ^ T.card`.
  This is the cross-step independence/cylinder instantiation.
- `selectionCount_tail_le_choose`: the choose-union tail
  `P[PrefixAgentHighLoad σ a r] ≤ choose K r * (2/n)^r`, obtained by feeding
  the concrete cylinder theorem and finite-union outer-measure bound into
  `prefix_agent_high_load_mass_le_choose`.

Verification:

```bash
lake build SSExactMajority/UpperBound/Time/DisruptionTail.lean:olean
lake env lean SSExactMajority/Probability/SelectionCount.lean
rg -n "sorry|axiom|native_decide" SSExactMajority/Probability/SelectionCount.lean
```

The `lake env lean` check for `SelectionCount.lean` completed with no output.
The `rg` check found no matches.
