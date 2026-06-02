# Task: Prove hPropagationLive (Paper Lemma 11)

## Goal

Create SSExactMajority/UpperBound/Time/PropagationLive.lean proving:

From InSswap + MedianAnswerCorrect + timer in [1, 7(Rmax+4)] + not consensus:
probReached to IsConsensusConfig within 20*Rmax*n*n >= 1/1280

This is the last undischarged hypothesis in the end-to-end time complexity.

## Paper: Kanaya et al. 2025, Lemma 11

## Available (sorry-free):
- PEM_expected_timer_drain_poly: E[timer drain] <= 7(Rmax+4)*n*(n-1)
- PEM_CRS_to_allR_or_break: E[CRS -> nRC=0] <= n^2*(n-1), nRC non-increasing under CRS
- trigger_correct_reset_from_InSrank: exists pair creating CRS deterministically
- step_InSswap_break_creates_CorrectResetSeed: InSswap break -> CRS
- bounded_config_to_consensus: E[T] < top for IsBoundedConfig
- Ranking phase bounds (Time.lean): E[ranking] <= Rmax*n^2
- ProbHitWithin framework (ExpectedTime.lean)

## Approach
Split wrongAnswerCount = 0 (timer drain -> consensus) vs > 0 (timer drain -> CRS -> epidemic -> re-ranking -> consensus). Chain probabilities via ProbHitWithin_add_ge_mul.
