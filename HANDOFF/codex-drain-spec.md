# Codex task (uisai1): refined timer-drain — the precise closing piece for OW_consensusBound

cxelim identified this exact missing lemma ("the right shape, not completed"). Build it; it eliminates
the circular exit branch and closes OW_consensusBound faithfully.

## KEY FACT: in InSswap there is NO disruption
InSswap = all Settled with unique ranks ⟹ no recruit, no collision (unique ranks), no error (no
Unsettled). So from InSswap∧MAC, the timer DETERMINISTICALLY drains to 0 STAYING InSswap∧MAC (MAC
preserved by step_median_answer_of_InSswap_both_v2; InSswap preserved while no median timer-0 reset).
The ONLY way to leave is timer=0 → median triggers propagate-reset → CRS (productive). No disruptive exit.

## Target (refined drain — split the ¬live endpoint into productive pieces)
```
theorem timer_drain_to_zero_productive
  (hn4 ...) (C) (hS : InSswap C) (hMAC : MedianAnswerCorrect C) (hB : IsTimerBoundedConfig (7*(Rmax+4)) C) :
  Probability.expectedHittingTime P hn C
    (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨ (InSswap D ∧ MedianAnswerCorrect D ∧
        (∀ μ, (D μ).1.rank.val+1 = ceilHalf n → (D μ).1.timer = 0)))   -- timer=0 at median, still InSswap∧MAC
    ≤ ((7*(Rmax+4)*n*(n-1) : ℕ) : ENNReal)
```
Build by CLONING PEM_expected_timer_drain_poly (PolynomialBound:151) but SPLITTING its ¬live exit
endpoint: instead of "cons ∨ CRS ∨ ¬live", target "cons ∨ CRS ∨ (InSswap∧MAC∧median-timer=0)". The
deterministic descent measure is the median timer (drains by 1 on median–rank-n interactions; reuse
maxMedianTimer / the timer-descent machinery). Staying InSswap∧MAC: use step_median_answer_of_InSswap_
both_v2 (MAC preserved) + the no-disruption-in-InSswap fact.

## Then CHAIN (eliminate hRank12)
decision_before_timer_zero (InSswap∧timer≥35 → MAC-live ∨ cons ∨ CRS, ≥1/4 PROVEN) → on MAC-live,
timer_drain_to_zero_productive → (cons ∨ CRS ∨ MAC∧timer=0); on MAC∧timer=0, PEM_expected_reset_trigger_v2
→ cons∨CRS; CRS → CRS_to_silence_faithful → consensus. ALL productive, NO circular exit. Restructure
OW_consensusBound (entry MedianTimerAtLeast 35) to use this, DROP hRank12. Update PEM_expectedParallelTime_optimal.

## FIRST sub-goal
timer_drain_to_zero_productive (the refined drain, deterministic descent staying InSswap∧MAC). This is
the precise closing piece. If staying-InSswap∧MAC through the drain genuinely fails (some median-max
step breaks it), report the exact step.

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide. Grind or precise obstruction to HANDOFF/outbox/codex-drain-report.md.
  Edit OptimalWindows.lean / DecisionTiming.lean / a helper. Self-verify lake env lean. NEVER lake build.
