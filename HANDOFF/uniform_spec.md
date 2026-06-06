# Piece B: extend the log-tree construction to deliver uniform answer + unique leader at the fresh endpoint

## Goal
all_fresh_from_log_seed_unconditional delivers all agents (Resetting, rc=0, delaytimer=Dmax) but with arbitrary
answers/leaders. The proven fresh bridge (fresh_uniform_unique_to_FreshRankingStart_resAns_noPhi,
LogRegimeConvergence.lean:64) additionally needs UNIFORM ANSWER and UNIQUE LEADER. Extend the construction:
  all_fresh_uniform_from_log_seed :
    from a config with the collision-style seed pair (the actual producers give TWO agents with rc = Rmax,
    leader = .L, answer = the majority answer m — see BurmanConvergenceFinal.lean:395-396, :646, :741; pick the
    precondition shape those producers can feed), with clog 2 n + 2 (or +3, whatever the construction needs)
    <= Rmax, 1 < Dmax, 2 <= n:
    exists L, after runPairs: forall w, FreshResettingAt Dmax w AND (C2 w).1.answer = m, AND exactly one agent
    has leader = .L.

## FIRST: investigate the sync semantics (do not assume)
Read the actual transition (propagateReset + rankDeltaOSSR + transitionPEM, RankDelta.lean) and determine:
1. What happens to .answer on recruitment? (the recruit keeps its OLD answer — the update record only sets
   role/resetcount/delaytimer — CONFIRM.)
2. Is there an answer-sync between two RESETTING agents (fueled or dormant)? Find the exact rule that spreads
   answers among Resetting agents (the answer epidemic). Note its preconditions (dormant-only? any Resetting?).
3. What happens to .leader when two leaders (.L,.L) meet, and on recruitment? Find the leader-resolution rule.
Report these three facts with file:line in your report BEFORE building.

## Design (adapt to what you find)
Preferred order if answer-sync works between FUELED Resetting agents (timers frozen): grow tree -> uniformize
answers + resolve the two seed leaders while everyone is fueled (free, no timer cost) -> drain to fresh.
If answer-sync only fires for DORMANT agents: drain first, then spread the answer with a LINE schedule (agent i
selected at most twice: receive then pass), costing each agent <= 2 timer decrements — then the endpoint has
delaytimer >= Dmax - 2, NOT = Dmax. In that case ALSO generalize the fresh bridge you proved at
LogRegimeConvergence.lean:64 to accept delaytimer >= Dmax - 2 (or a floor parameter) instead of exact equality
— check which form its proof actually needs; it is your own lemma, adjust whichever side is cheaper while
keeping it faithful. Same handling for the leader duel (one pairing of the two leaders).
Track the invariant through the existing tree induction (answers of fueled set = m, leader count bookkeeping).

## HARD RULES (automode: NO effort cap)
Work in LogTreeReset.lean / LogRegimeConvergence.lean (yours). Do NOT edit other files. Iterate
lake build SSExactMajority.Convergence.LogRegimeConvergence until clean. No sorry/axiom/native_decide. If a
sync rule genuinely cannot deliver uniformity (mechanism-level), STOP and report exact file:line + the rule.
Commit clean with [Xiang-proxy]. Report the three sync facts + theorem names + exact preconditions to
HANDOFF/outbox/cxfix-report.md.
