# Step 2 final piece: thread the log-seed theorem through the convergence chain -> correctness at Theta(log n)

## Goal
Produce the log-regime correctness theorem: P_EM solves SSEM at Rmax = Emax = Dmax = Theta(log n) parameters
(target shape: hypotheses like clog 2 n + 2 <= Rmax, c0 <= Dmax, c1 <= Emax with c0/c1 constants or
clog-level, NOT n <= _). New file SSExactMajority/Convergence/LogRegimeConvergence.lean (yours), importing
LogTreeReset and the existing convergence files (read-only).

## What exists
- all_fresh_from_log_seed_unconditional (LogTreeReset.lean:1286): from any config with one Resetting seed of
  resetcount >= clog 2 n + 2, a schedule reaches ALL agents FreshResettingAt Dmax (Resetting, rc=0,
  delaytimer=Dmax). This replaces the old single-seed route (all_resetting_from_seed_aux,
  BurmanConvergenceFinal.lean:989) which forced n <= Rmax.
- The existing chain (BurmanConvergenceFinal.lean): collision/error -> CorrectResetSeed (seed rc=Rmax) ->
  [single-seed all-Resetting] -> normalize answers -> wake/rank -> silence -> burmanConvergence_concrete
  (:~15941, requires n <= Rmax) -> P_EM_solves_SSEM_final (:~16052, instantiated at Rmax=trank=n).

## Plan
1. MAP the chain first: find where all_resetting_from_seed_aux's conclusion is consumed (≈ lines 2151-2211)
   and what the next phase needs from that state. List every lemma between there and burmanConvergence_concrete
   that carries n <= Rmax, n <= Dmax, or n <= Emax, and for each, determine WHY (read the use sites; from prior
   analysis the only real n <= Dmax uses are at :6555 and :6633, of the form
   delaytimer > positiveRcExcept_card < n).
2. KEY simplification to exploit: our new fresh state has rc = 0 for ALL agents, so positiveRcExcept_card = 0
   wherever the input state is the fresh one — the delaytimer requirement collapses to > 0 (or a small
   constant). Re-derive (do not edit originals) log-versions of the affected lemmas, or better: prove the next
   phase directly from FreshResettingAt input where the old proof needed the messy partially-drained state.
3. Produce burmanConvergence_concrete_log and P_EM_solves_SSEM_log with parameter hypotheses
   (clog 2 n + 2 <= Rmax) AND (constants/clog bounds for Dmax, Emax — derive the minimal ones the proofs
   actually need; report exactly what they are). The protocol instance: protocolPEM n trank Rmax with whatever
   trank the correctness side uses (mirror the existing final theorem shape; if it hard-couples trank=Rmax=n,
   instantiate trank analogously at the log value and report).
4. If a later-phase lemma turns out to GENUINELY need n <= Dmax or n <= Emax even from the fresh state (not a
   schedule artifact), STOP on that lemma and report the exact file:line + why, instead of weakening the goal.

## HARD RULES (automode: NO effort cap)
New file only; do NOT edit existing files. Iterate lake build SSExactMajority.Convergence.LogRegimeConvergence
until clean. No sorry/axiom/native_decide. Decompose freely. Commit clean with [Xiang-proxy]. Report: the final
theorem names + file:line, the EXACT parameter hypotheses landed (this determines the paper-faithfulness
verdict), and any genuine n-dependence found, to HANDOFF/outbox/cxfix-report.md.
