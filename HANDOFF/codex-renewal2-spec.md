# Codex task (uisai1): avenue (a1) — awakening relaxed-goal descent E[T] (escape-to-restart)

DOCTRINE docs/DOCTRINE.md avenue (a). Key idea: put "disruption" (left the phase invariant) INTO the
goal, so all-pair closure becomes TRIVIAL. The outer renewal will absorb the disruption-exit later.

Continue in EXISTING SSExactMajority/UpperBound/Time/EntryBound.lean.

## Target
```
theorem awakening_to_goal_or_exit_expected_le
  (hn4 : 4 ≤ n) (C) (hAwake : IsAwakeningConfig C) :
  Probability.expectedHittingTime (PEMProtocolCoupled' n Rmax Emax Dmax hn) (by omega:2≤n) C
    (fun D => FreshRankingStart D ∨ (∃ k, 2 ≤ k ∧ HeapPrefix D k) ∨ IsConsensusConfig D
              ∨ ¬ IsAwakeningConfig D)
    ≤ (((awakeningResettingFollowers C).card * (n*(n-1)) : ℕ) : ENNReal)
```
via `expectedHittingTime_le_of_variable_descent_until_goal` (ExpectedTime.lean:4379):
- φ D := (awakeningResettingFollowers D).card ; Inv := IsAwakeningConfig ; Goal := the 4-way
  disjunction above (NOTE it includes ¬IsAwakeningConfig).
- hInvStep (TRIVIAL now): ∀ C, Inv C → ¬Goal C → ∀ i j, Inv(step) ∨ Goal(step). If the step stays
  IsAwakeningConfig, left disjunct of Inv∨Goal is Inv(step). If it leaves, then ¬IsAwakeningConfig(step)
  is a Goal disjunct. So `by by_cases h : IsAwakeningConfig (C.step ...); [exact Or.inl h; exact
  Or.inr (Or.inr (Or.inr (Or.inr h)))]` (adjust nesting).
- hZeroGoal: card = 0 ⟹ FreshRankingStart (freshRankingStart_iff_awakeningResettingFollowers_card_zero
  _of_awakening) ⟹ Goal. (Holds under Inv.)
- hNonincrease: ∀ C, Inv C → ¬Goal C → ∀ i j, φ(step) ≤ φ(C). For a non-goal step, C.step is STILL
  IsAwakeningConfig (since ¬Goal ⟹ ¬¬IsAwakeningConfig(step) i.e. IsAwakeningConfig(step) holds — the
  ¬IsAwakeningConfig disjunct of Goal is false). With both C and C.step awakening, prove card
  non-increase: the only way card rises is creating a Resetting-follower, which requires a reset that
  sets leader=L (breaking unique-leader ⟹ ¬awakening ⟹ would be Goal, contradiction). So no non-goal
  step raises card. Prove this case analysis (use the role/leader structure of IsAwakeningConfig).
- hp: ProbHitWithin(Goal ∨ (Inv ∧ φ<k)) ≥ 1/(n(n-1)). The proven `awakening_step_descent_prob` gives
  ≥1/(n(n-1)) for the SMALLER goal (FreshRankingStart ∨ (awakening ∧ smaller card)); lift to the bigger
  Goal via `Probability.ProbHitWithin_mono_goal`.

## FIRST sub-goal
Get hInvStep + hp wired (both nearly immediate). Then hNonincrease (the real content — the
no-card-rise-while-staying-awakening case analysis). If hNonincrease has a genuine counterexample
(a non-goal awakening step that raises card), report it EXACTLY.

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide. Grind to a proof or a precise obstruction in
  HANDOFF/outbox/codex-renewal2-report.md. ONLY EntryBound.lean. Self-verify lake env lean.
  NEVER lake build. Do not stop on "hard" — try multiple tactics.
