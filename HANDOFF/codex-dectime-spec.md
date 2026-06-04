# Codex task (uisai1): decision-timing isolation — P(reach MAC before timer=0) ≥ const

The root obstruction for OW_consensusBound: in InSswap (all Settled, unique ranks) there is NO
disruption (no Unsettled→no error-reset; unique ranks→no collision). The only exits are the median's
timer events. So the productive isolation reduces to DECISION TIMING: from InSswap+timer+¬MAC, does the
median reach MAC (correct decision) BEFORE the timer drains to 0? (Kanaya §5.2; timer=7(trank+4) is
sized for this.)

## Target
```
theorem decision_before_timer_zero
  (hn4 ...) (C) (hS : InSswap C) (hT : MedianTimerAtLeast 1 C) :
  (const : ENNReal) ≤ ProbHitWithin P hn C
    (fun D => (InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D)  -- reached MAC, timer still live
              ∨ IsConsensusConfig D ∨ CorrectResetSeed D)  -- or already productive
    (decisionWindow n)
```
i.e. isolate the PRODUCTIVE outcome (MAC-still-live ∨ cons ∨ CRS) from the non-productive timer=0-without-MAC.
Investigate the decision mechanism (Protocol/Transition.lean phase4_decide, lines ~65; median compares
with rank-n agent, decrements timer on rank-n interaction line 415). The median needs to interact with
the rank-n agent to decide; the timer drains on those same interactions. Key: characterize when the
decision COMPLETES (MAC) vs times out. Reuse decision_window, the maxMedianTimer descent, step_at_median_
max_timer_one_no_reset (MacroStepComposition:65), the TransitionLemmas timer-zero lemmas.

## FIRST sub-goal
Determine whether decision_window's MAC branch can be lower-bounded SEPARATELY from its ¬live(timer=0)
branch — i.e. is P(MAC reached while timer still ≥1) ≥ const? If the decision deterministically completes
within the timer (timer sized for it), this may be provable; if it genuinely needs §5.2's probabilistic
timing argument, report the EXACT structure needed (which interactions, what timer budget).

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide. Grind or precise obstruction to HANDOFF/outbox/codex-dectime-report.md.
  New file SSExactMajority/UpperBound/Time/DecisionTiming.lean. Self-verify lake env lean. NEVER lake build.
