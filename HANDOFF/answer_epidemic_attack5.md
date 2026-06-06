# ATTACK 5: the answer-epidemic bridge via (cited standard epidemic-speed) + (PROVEN drain-no-wake) + composition

Attacks 2-4 proved (counterexamples) there is NO deterministic dormancy invariant — it is a probabilistic race.
Time-scale analysis: epidemic is O(log n) time, drain-to-wake is O(n) time, so the epidemic wins comfortably,
BUT only if we use the O(log n)-time (= O(n log n)-interaction) epidemic bound. Our coupon bound is only O(n^2)
interactions, which is too loose (an agent gets selected ~n times in n^2 interactions, enough to drain).

## Clean faithful + tractable decomposition
1. h_epidemic_fast (CITED — STANDARD one-rumor epidemic, clearly labeled NOT [12], NOT Kanaya; this is the
   textbook rumor-spreading O(log n)-time-w.h.p. result used throughout population protocols): from EpidemicRegion
   m C, p_e <= ProbHitWithin P C (EpidemicPhiGoal m) K_fast, with K_fast = C_e * n * Nat.clog 2 n (O(n log n)
   interactions) and p_e a positive constant. State it as its own clearly-named hypothesis/contract field
   `epidemicFast` — DISTINCT from resetReach. (Scope: citing a generic standard epidemic-speed lemma is faithful;
   Kanaya s contribution is the renewal/race composition, which we PROVE.)
2. drain_no_wake (PROVE this — the machinery EXISTS): within K_fast = O(n log n) interactions, with prob >= p_d
   (constant, in fact 1 - o(1)), NO agent wakes. Proof: an agent wakes only after being SELECTED (in the rc=0
   processAgent branch) at least delaytimer >= ... times; newly-caught delaytimer = Dmax >= n (hDmax). Use
   `selectionCount_tail_le_choose` (Probability/SelectionCount.lean:247) to bound P[some fixed agent selected >= n
   times in K_fast=O(n log n) interactions] (binomial tail: expected selections per agent ~ 2*K_fast/n = O(log n)
   << n, so the tail is tiny), then UNION BOUND over the n agents. Relate "an agent woke by step K_fast" to "that
   agent was selected >= (drain count) times" via `ProbHitWithin_le_eventCountDist_tail_of_support_imp`
   (Probability/ExpectedTime.lean:1250). This is the genuine Kanaya-side proof and it is assemblable from existing
   tools.
3. bridge (PROVE — compose 1 and 2): from EpidemicRegion, p_e * p_d <= ProbHitWithin P C
   (fun D => EpidemicPhiGoal m D AND <all still Resetting>) K_fast. Use ProbHitWithin_union_le / the or-bound to
   combine "epidemic hit" and "no wake".
4. resetReach (CITED [12]) restored FAITHFUL: target EpidemicRegion (all-Resetting), NOT EpidemicPhiGoal. [12] Lemma 3.2.
5. Compose: resetReach -> EpidemicRegion -> (bridge) -> (EpidemicPhiGoal AND Resetting) -> silence link. Thread
   WellFormed/MajInv. Bound <= K*n (K_fast=O(n log n) is below the O(n^2) ranking/reset terms, fine).

## HARD
WRITE LEAN. The drain_no_wake (step 2) is PROVABLE from selectionCount_tail_le_choose + union bound +
the eventCountDist tail lemma — do it, do not punt. Only h_epidemic_fast (step 1) is a cited standard result
(label it clearly as the standard epidemic-spreading lemma, separate field, NOT folded into [12]). resetReach
MUST be faithful. No sorry/axiom, full lake build. If selectionCount_tail_le_choose genuinely cannot be applied
here, report the precise gap (### BLOCKER), but it looks directly applicable. Report proved theorem names+file:line.
