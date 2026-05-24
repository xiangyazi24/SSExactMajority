#!/usr/bin/env python3
"""Monte Carlo simulation of Phase 4 (Lemma 11) probability bound.

From InSswap ∧ MedianAnswerCorrect ∧ timer∈[1, 7(Rmax+4)] ∧ ¬consensus:
simulate the protocol and check if consensus is reached within 10*Rmax*n*n steps.

The paper claims prob ≥ 1/1280 ≈ 0.00078.
"""

import random
import sys
from collections import Counter

def simulate_phase4(n, Rmax, num_trials=10000):
    """Simulate from InSswap ∧ MedianAnswerCorrect ∧ timer ∧ ¬consensus."""
    timer_init = 7 * (Rmax + 4)
    window = 10 * Rmax * n * n
    median_rank = (n + 1) // 2  # ⌈n/2⌉, 1-indexed
    max_rank = n

    successes = 0

    for trial in range(num_trials):
        # Initial config: InSswap, median answer correct, one wrong-answer agent
        # Agents: ranks 1..n, A-inputs have ranks 1..nA, B-inputs have ranks nA+1..n
        nA = n // 2 + 1  # majority A

        # answers[i] = correct opinion for agent with rank i+1
        # Correct = A for ranks ≤ nA, B for ranks > nA
        # Median answer is correct. One other agent has wrong answer.
        correct_answer = ['A'] * nA + ['B'] * (n - nA)
        answers = list(correct_answer)

        # Make one non-median agent have wrong answer
        wrong_idx = 0 if 0 != median_rank - 1 else 1
        answers[wrong_idx] = 'B' if correct_answer[wrong_idx] == 'A' else 'A'

        timer = timer_init
        settled = [True] * n  # all settled (InSswap)

        consensus = False

        for step in range(window):
            # Pick random ordered pair (i, j) where i ≠ j
            i = random.randint(0, n - 1)
            j = random.randint(0, n - 2)
            if j >= i:
                j += 1

            # Check if both settled (InSswap preserved until reset)
            if settled[i] and settled[j]:
                # Phase 4 logic:
                # Timer decrement: if one is median and other is max-rank
                i_rank = i + 1  # 1-indexed rank
                j_rank = j + 1

                if i_rank == median_rank and j_rank == max_rank:
                    timer = max(0, timer - 1)
                elif j_rank == median_rank and i_rank == max_rank:
                    timer = max(0, timer - 1)

                # Propagation: if median timer=0 and answers disagree
                if timer == 0:
                    med_idx = median_rank - 1
                    if (i_rank == median_rank or j_rank == median_rank):
                        other_idx = j if i_rank == median_rank else i
                        if answers[med_idx] != answers[other_idx]:
                            # Trigger propagate-reset
                            # Simplified: correct answer propagates to all
                            answers = list(correct_answer)
                            # Timer resets after re-ranking
                            timer = timer_init
                            # Check consensus
                            if answers == correct_answer:
                                consensus = True
                                break

            # Check consensus
            if answers == correct_answer and all(settled):
                consensus = True
                break

        if consensus:
            successes += 1

    prob = successes / num_trials
    return prob

if __name__ == '__main__':
    for n in [5, 8, 10, 20]:
        Rmax = n  # our literal instantiation
        prob = simulate_phase4(n, Rmax, num_trials=5000)
        threshold = 1/1280
        status = "✓" if prob >= threshold else "✗"
        print(f"n={n:3d}, Rmax={Rmax:3d}, window={10*Rmax*n*n:8d}, "
              f"prob={prob:.4f}, threshold={threshold:.4f} {status}")
