# Codex task (uisai1): close awakening->FreshRankingStart E[T], then dormant->awakening

Continue in EXISTING SSExactMajority/UpperBound/Time/EntryBound.lean (you own it).

## STEP A (should close cleanly — the witness is already proven)
Wire `awakening_step_descent_prob` (just proven, in this file) into a clean E[T] bound:
```
theorem awakening_to_FreshRankingStart_expected_le
  (hn4 : 4 ≤ n) (C) (hAwake : IsAwakeningConfig C) :
  Probability.expectedHittingTime (PEMProtocolCoupled' n Rmax Emax Dmax hn) (by omega:2≤n) C
    FreshRankingStart ≤ (((awakeningResettingFollowers C).card * (n * (n - 1)) : ℕ) : ENNReal)
```
via `Probability.expectedHittingTime_le_of_variable_descent_until_goal` (ExpectedTime.lean:4379)
with φ D := (awakeningResettingFollowers D).card, Goal=FreshRankingStart, Inv=IsAwakeningConfig,
pRate = 1/(n(n-1)). The descent hypothesis is EXACTLY awakening_step_descent_prob; the
φ=0 ⟹ Goal is freshRankingStart_iff_awakeningResettingFollowers_card_zero_of_awakening;
Inv-preservation is in awakening_step_descent_witness's conclusion (generalize to all pairs:
IsAwakeningConfig preserved by any step — prove `IsAwakeningConfig`-step-closure if needed).
Check the EXACT signature/hypotheses of the variable-descent lemma and match them.

## STEP B (the remaining half of the entry link)
dormant -> awakening E[T]. Progress measure: `followerDormantMeasure` (BurmanProof.lean) /
leader delaytimer. The qualitative `phase3a_to_awakening` uses strong induction on leader
delaytimer. Build the per-step descent witness (∃ pair decreasing the delaytimer measure,
prob ≥1/(n(n-1))) and the E[T] bound `dormant_to_awakening_expected_le ≤ poly`. If blocked,
report the exact obstruction (which pair / measure-increase) — Opus refines.

## HARD RULES
- NO sorry/axiom/native_decide. Blocked → exact obstruction to HANDOFF/outbox/codex-entry2-report.md.
- ONLY EntryBound.lean. Self-verify lake env lean. NEVER lake build. Report STEP A and STEP B
  status separately (A is the priority — close it first and report before B).
