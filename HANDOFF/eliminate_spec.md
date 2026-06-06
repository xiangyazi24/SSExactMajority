# Piece B2: eliminate the n <= Dmax from the log endgame — route through YOUR fresh bridge, not the old lemma

## Diagnosis
log_seed_uniform_leader_to_FreshRankingStart_resAns_noPhi (LogRegimeConvergence.lean:44) carries hDmax_n only
because at :98 it routes through the OLD chain lemma
all_resetting_pos_with_leader_uniform_to_FreshRankingStart_resAns_noPhi (which drains via the old
positive-rc-budget path). Your OWN fresh bridge fresh_uniform_unique_to_FreshRankingStart_resAns_noPhi
(LogRegimeConvergence.lean:64) needs NO n <= Dmax. Compose growth -> YOUR drain -> YOUR :64 bridge instead.

## What is missing for that composition
1. DRAIN preserving answer + leader: extend drain_all_floor_two_to_fresh to also conclude
   (forall w, answer w = m0) and (the unique .L is preserved). Per-step facts: pairing two Resetting agents
   with answer = m (non-phi) keeps both = m (prePhase4 only fills phi from non-phi,
   Transition.lean:49-55, and you already proved step_resetting_pair_majority_answer); .L/.L demotion
   (RankDelta.lean:196-202) never fires when at most one endpoint is .L, and leader is otherwise preserved —
   prove the per-step leader-preservation fact if not already present.
2. UNIQUE leader: growth gives the root .L but other agents may also be .L (recruitment inherits the old
   leader; non-Resetting .L agents recruited into the tree stay .L). Resolve with a FUELED TOURNAMENT after
   growth, before drain: while at least two .L agents exist, pair .L agents with each other pairwise
   (disjoint pairs per round; odd one sits out). Each pairing: both Resetting and fueled, Phase 2 drops both
   fuels by 1, and the .L/.L rule demotes one (RankDelta.lean:196-202 — verify which endpoint survives and
   use that). Rounds <= clog 2 n (leader count at least halves); each agent loses <= clog 2 n fuel total.
   So raise the growth fuel floor: run balanced_tree_growth_floor_answer_leader with
   d := clog 2 n + 2 (tournament budget + drain floor 2), i.e. total seed fuel requirement about
   2 * clog 2 n + 3 — report the exact constant you land on. Answers unaffected (both .L carriers have m).
3. Compose: growth(answer/leader) -> tournament (unique .L, all fueled >= 2, answers = m) -> drain(answer/
   leader) -> all FreshResettingAt Dmax AND uniform m AND exactly-one .L -> YOUR :64 bridge -> conclusion of
   the :44 theorem WITHOUT hDmax_n. Name it log_seed_uniform_leader_to_FreshRankingStart_resAns_noPhi_log
   (or replace the :44 theorem — your file).

## Note on uniqueness bookkeeping
"Exactly one .L" needs counting: track the Finset of .L agents; tournament rounds strictly halve its card
(ceil); terminate at card = 1. The demoted endpoint flips to .F permanently (verify no rule re-promotes
during drain — drain pairs are Resetting/Resetting, the only leader rule is the .L/.L demotion which cannot
fire once card = 1... it CAN fire if you pair the survivor with itself-no; with another .L-none left. Safe.)

## HARD RULES (automode: NO effort cap)
Files: LogTreeReset.lean / LogRegimeConvergence.lean (yours). Iterate
lake build SSExactMajority.Convergence.LogRegimeConvergence until clean. No sorry/axiom/native_decide. The
final theorem must NOT contain n <= Dmax (nor n <= Rmax, n <= Emax) — only clog-level and constant bounds.
Commit clean with [Xiang-proxy]. Report theorem names + the exact fuel constant + confirmation hDmax_n is gone
to HANDOFF/outbox/cxfix-report.md.
