# Phase A: the balanced-doubling growth construction — discharge hBalancedTreeGrowth

## Goal
LogTreeReset.lean (yours) proved Phase B but left Phase A as the hypothesis hBalancedTreeGrowth. Now prove it:
  theorem balanced_tree_growth
      [Inhabited (Fin n x Fin n)] {Rmax Emax Dmax : N} {hn : 0 < n} (hDmax : 1 < Dmax) :
      forall (C : Config (AgentState n) Opinion n) (r : Fin n),
        (C r).1.role = .Resetting -> Nat.clog 2 n + 1 <= (C r).1.resetcount ->
        exists Lgrow : List (Fin n x Fin n),
          let C1 := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C Lgrow
          forall w : Fin n, (C1 w).1.role = .Resetting AND 0 < (C1 w).1.resetcount
and then a corollary all_fresh_from_log_seed_unconditional that feeds it into the existing
all_fresh_from_log_seed (also supply the trivial covering disjoint pair list over Fin n for its pairs argument
— e.g. consecutive pairs (2i, 2i+1) plus handling odd n by pairing the last agent... NOTE pairEndpoints must
cover ALL agents; for odd n use a final overlapping pair only if PairListDisjoint allows — if not, generalize:
the drain theorem needs disjointness; for odd n cover with floor(n/2) disjoint pairs + one extra pair that
reuses one already-drained agent is NOT disjoint. Check drain_pair_list_to_fresh_on_endpoints: if it
fundamentally needs disjoint cover, odd n needs one agent drained separately — pair the leftover agent with an
already-fresh one? That pairing would select a dormant agent (timer decrement!). Cleaner: drain in two disjoint
rounds: round 1 pairs {(0,1),(2,3),...} leaving agent n-1 fueled; round 2 the single pair (n-1, 0) — agent 0 is
dormant rc=0 delaytimer=Dmax; the interaction syncs... 0 is Resetting so Phase2 fires: both get
max(rc_{n-1}-1, 0-1) = rc_{n-1}-1, RE-FUELING agent 0! That breaks freshness. Alternative: in Phase A, leave
the seed r OUT of the final fueled set... it cannot be (everyone must be fueled). SOLUTION: drain pair
(n-1, 0) repeatedly until BOTH hit 0 — the last sync max(1-1,1-1)=0 drains both simultaneously and BOTH refresh
delaytimer:=Dmax in that same step. So pair equal-fuel agents and the pair drains together. Generalize the
drain to handle a chain: actually simplest fully-general drain: repeatedly pair the two MAX-fuel agents until
all rc=0 (each such pairing is a single pair list element; agents hit 0 simultaneously in their last pairing and
refresh). If the existing drain theorem cannot express this, prove a small extension lemma in your file.)

## The doubling argument (use it)
Invariant (induction on g): exists Finset S, r in S, |S| >= min(2^g, n... careful: use min (2^g) n), and
forall w in S: role=Resetting AND R - g <= rc (R := clog2 n + 1 wlog the seed has exactly >= R), and agents
outside S are UNTOUCHED from C.
Generation step (g -> g+1) while |S| < n: choose T := an injection from S into (univ \ S) covering
t := min |S| (n - |S|) targets; pair each chosen s in S with its target. Each pair (s, w):
 - if w non-Resetting: Phase1 recruits (w.role:=Resetting, rc:=0, delaytimer:=Dmax), then Phase2 syncs both to
   (C s).rc - 1 > 0.
 - if w dormant Resetting (rc=0): Phase2 syncs both to rc_s - 1 > 0; processAgent sees post-sync rc>0 so NO
   delaytimer decrement and NO wake test. (Verify against processAgent: the dormant branch tests CURRENT
   resetcount.)
 - if w Resetting with rc>0 already (only possible if untouched-from-C agents can be fueled — then just skip w,
   it is already fueled; fold such agents into S at g=0).
Pairs within a generation are DISJOINT (s distinct, targets distinct, s not target) so sequential runPairs
bookkeeping: each pair only changes its two endpoints (reuse the unchanged-tail lemmas from your Phase B work).
After the step: S' := S ∪ targets, everyone in S' has rc >= R - (g+1) (the pairing decrements the fueled side
by 1; UNPAIRED members of S keep rc >= R-g >= R-(g+1)). |S'| >= min(2^(g+1)) n. Terminate at g* <= clog2 n:
|S| = n, everyone fueled with rc >= R - clog2 n >= 1.
Base: S = {r} ∪ {already-fueled agents of C}, g=0... the invariant fuel floor must hold for pre-fueled agents:
either require (cleanest) forall w, (C w).1.role = .Resetting -> (w = r OR (C w).1.resetcount = 0) — i.e. the
seed is the unique fueled agent (this matches the post-collision CorrectResetSeed situation; CHECK what the
CRS-producing lemmas give: both collision agents get rc=Rmax, so allow a SET of seeds: generalize hseed to a
nonempty Finset S0 of fueled agents each with rc >= clog2 n + 1, everyone else either non-Resetting or dormant).
Pick the cleanest precondition that the collision lemmas (rc=Rmax on both endpoints) can feed.

## HARD RULES (automode: NO effort cap; this is the hard core of the program — grind it)
Work in LogTreeReset.lean (yours) or a new LogTreeGrowth.lean imported by it. Decompose freely: per-pair step
lemmas, one-generation lemma, the induction, the final unconditional corollary. Iterate
lake build SSExactMajority.Convergence.LogTreeReset until clean. No sorry/axiom/native_decide. Do NOT leave
the doubling as another hypothesis — discharge it fully; if a genuine definitional blocker appears (a transition
behaving differently than stated above), STOP and report the exact mismatch with file:line instead of weakening
the statement. Commit clean with [Xiang-proxy]. Report theorem names + file:line + exact preconditions to
HANDOFF/outbox/cxfix-report.md.
