# Step 2 piece 1: balanced-tree reset at Rmax = Theta(log n) — the log-regime foundation

## Goal (paper-faithful regime: Rmax = 60 log n, NOT n <= Rmax)
Prove the log-regime replacement for all_resetting_from_seed_aux (BurmanConvergenceFinal.lean:989, which
needs seed resetcount >= nonResettingCount, forcing Rmax >= n). New file
SSExactMajority/Convergence/LogTreeReset.lean (you own it).

## Verified mechanism facts (use them; all in propagateReset / processAgent, RankDelta.lean)
1. Recruitment: a.role=Resetting AND 0<a.resetcount AND b.role!=Resetting => b becomes Resetting with
   resetcount:=0, delaytimer:=Dmax. Then Phase 2 (both now Resetting) syncs BOTH to
   max(a.rc-1, b.rc-1) = a.rc-1 (since b.rc=0). NET: one interaction turns seed(rc=k)+fresh into TWO
   Resetting agents each with rc = k-1. THIS IS THE DOUBLING.
2. Two Resetting agents pairing: both get rc := max(a.rc-1, b.rc-1). Pairing two rc=k agents => both rc=k-1
   (MUTUAL DRAIN, one step per fuel unit).
3. processAgent: positive-rc Resetting agents NEVER decrement delaytimer (timers frozen while fueled). The
   oldRc>0 -> rc=0 transition REFRESHES delaytimer := Dmax. Dormant (rc=0) agents decrement delaytimer only
   when selected.
So a schedule that (A) recruits by doubling, (B) drains by pairing equal-fuel agents with each other, and
(C) never selects an agent after it goes dormant, ends with EVERY agent role=Resetting, rc=0,
delaytimer=Dmax EXACTLY — the perfectly fresh seed — deterministically.

## Target theorem (shape; adapt names/binders to the existing aux infrastructure: runPairs, protocolPEM,
rankDeltaOSSR — mirror all_resetting_from_seed_aux which you can read at BurmanConvergenceFinal.lean:985-1065)
  theorem all_fresh_from_log_seed
      [Inhabited (Fin n x Fin n)] {Rmax Emax Dmax : N} {hn : 0 < n}
      (hDmax : 1 < Dmax)
      (hfuel : Nat.clog 2 n + 1 <= R)   -- log fuel suffices
      : forall C : Config (AgentState n) Opinion n,
        (exists r, (C r).1.role = .Resetting AND R <= (C r).1.resetcount) ->
        (forall a, (C a).1.role = .Resetting -> 0 < (C a).1.resetcount) ->  -- adapt: side conditions as needed
        exists L : List (Fin n x Fin n),
          let C2 := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
          (forall w, (C2 w).1.role = .Resetting AND (C2 w).1.resetcount = 0 AND (C2 w).1.delaytimer = Dmax)
Pick the precise preconditions yourself from what the construction needs (e.g. starting agents non-Resetting
except the seed, or handle already-Resetting agents by including them in the drain). State the cleanest
version that the existing CorrectResetSeed-producing lemmas can feed (a collision seed has rc = Rmax).

## Construction (strong induction, mirror the existing aux style)
Phase A (doubling): invariant after generation g: exists set S, |S| >= min(2^g, n), all in S Resetting with
rc >= R-g, everyone else untouched. Generation step: pair each fueled agent in S with a distinct
non-Resetting agent (recruitment fact 1). Stop when S = all agents: g* = ceil(log2 n) generations, fuel
R - g* >= 1.
Phase B (drain): repeatedly pair agents of positive rc with each other (fact 2) until all rc=0. To handle
unequal/odd fuels: pairing rc=a with rc=b gives both max(a-1,b-1); pair the two max-fuel agents each round —
fuel strictly decreases; termination by max-fuel measure. Each rc>0 -> 0 transition refreshes delaytimer:=Dmax
(fact 3). After an agent hits rc=0, never select it again.
End state: all Resetting, rc=0, delaytimer=Dmax.
Use/extend the existing per-step lemmas (propagate_reset_step_partner_rc, ..._sender_rc, the recruitment and
sync step facts) — read them at BurmanConvergenceFinal.lean:150-300 and BurmanProof.lean:3500-3520. If a
needed step lemma is missing (e.g. exact two-sided sync values, delaytimer refresh on drain), prove it in your
new file from the definitions.

## HARD RULES (automode: NO effort cap — grind; this is the foundation of the paper-faithful track)
New file LogTreeReset.lean only; do NOT edit existing files. Iterate
lake build SSExactMajority.Convergence.LogTreeReset until clean. No sorry/axiom/native_decide. The induction
bookkeeping (disjoint pairs, leftover odd agent, Finset cardinalities) is the hard part — decompose into
helper lemmas freely. Commit clean with [Xiang-proxy]. Report theorem names + file:line + the exact
preconditions you landed on to HANDOFF/outbox/cxfix-report.md.
