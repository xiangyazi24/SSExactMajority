# From Zinan — ChatGPT analysis of the two Props (precise blockers)

## The two Props needed to close the sorry:
1. `MedCorrectLiveProducesCorrectSeedOrProgress` (BCF:9445)
2. `ReservoirCaseProducesCorrectSeedOrProgress` (BCF:9469)

## Precise blockers (from ChatGPT analysis):

### Blocker 1: Timer drain as runPairs prefix
`timer_descent_to_one` returns `execution` facts. The Props need `runPairs` lists.
Need a wrapper: `inSswap_med_correct_drain_to_timer_zero_or_seed` that:
- Drains timer to 0 via median-max interactions
- Returns result as a `runPairs` list (not execution)
- Preserves InSswap + median answer correctness
- OR produces CorrectResetSeed directly (from odd_timer_one_max_step_clean_or_seed)

### Blocker 2: Even upper-median case
`trigger_correct_reset_from_InSrank_even` EXCLUDES `v.rank+1 = n/2+1`.
Your `med_correct_timer_zero_seed_or_wrong_exceptional` correctly splits this out.
Need: handle the "exceptional" case (wrong at max or upper-median) separately.
- For max: the wrong agent at max rank needs special treatment
- For upper-median: need the even decision-step that handles this
  (possibly `decision_step_at_median_pair_even_tie_decreases` or a non-tie analogue)

### Key insight from ChatGPT:
Prop #2 (ReservoirCase) is almost a one-line wrapper IF the core lemma exists.
Prop #1 (MedCorrectLive) needs the timer drain + the core lemma.

## Your `med_correct_timer_zero_seed_or_wrong_exceptional` is exactly right
It splits: seed OR exceptional. The exceptional cases need separate handling.

## What I can do
If you get stuck on the even upper-median case or the timer drain wrapper,
write to HANDOFF/outbox/from-codex.md and I'll take over that sub-lemma.
