# DOCTRINE — Optimal (explicit-poly) expected parallel-time bound

## Main goal (one sentence)
Close the 3 keystones in OptimalWindows.lean — OW_rankBound, OW_consensusBound,
PEM_expectedParallelTime_optimal — to 0 sorry / 0 axiom / faithful, via the renewal route.

## Settled facts (do not relitigate)
- Pathwise #resets <= poly is UNAVAILABLE (Case C verified: no reset-surviving counter). The
  pathwise-compensator / collisionBank-as-global route is DEAD. collisionBank/ResetBudget remain
  valid intra-epoch lemmas, off critical path.
- Correct route = renewal: window_mul_inv (E[T] <= K * p^-1, EXISTS) with Goal=consensus, p=CONSTANT
  per-epoch success via Markov on proven phase descents.
- NEW obstruction (e60567c): per-phase invariants are NOT all-pair-closed — disrupting resets fire
  WITHIN phases (e.g. two errorcount=0 Unsettled followers -> both Resetting+leader=L, escaping the
  awakening invariant AND all goal disjuncts). So variable_descent_until_goal fails per-phase.
- PROVEN+committed reusable: drift theorem, swap window (>=1/4 cons|CRS|exit), decision/timer windows,
  allR_to_phase1Goal_bound (<=Rmax*n^2), FreshRankingStart->endpoint (<=Rmax*n^2), awakening_step_descent
  witness/prob, rcLevelPotential descent, probReached_..._ge_mul5, ProbHitWithin_ge_half_of_E_le.

## Avenues (ranked; ChatGPT R3 will sharpen the choice)
(a) ESCAPE-TO-RESTART RENEWAL [primary]. window_mul_inv with Goal=consensus, p=const. Per-phase
    obligation relaxed to ProbHitWithin(phase-goal OR disruption-fired) >= const; a disruption is an
    EXIT handled by the OUTER renewal (re-applies p from the post-disruption bounded state). Need:
    (a1) each phase reaches (its goal OR disruption) within K_i with prob >= c_i — provable because
    "goal OR disruption" IS all-pair-closed (disruption is now in the target); (a2) compose phases
    via probReached_..._ge_mul5 into P(consensus OR disruption in K) >= const; (a3) window_mul_inv on
    the whole bounded region. Terminal: keystones proven, OR a phase where even (goal|disruption) is
    not reachable with const prob.
(b) DISRUPTION-FREE WINDOW. Bound P(no disrupting reset in K steps from clean entry) >= const
    (errorcount reset to Emax>=n on entry, decrements slowly => error-resets rare early), conditioned
    on which the good descent completes. Terminal: const lower bound proven, OR q*K forces it
    exp-small (then (a) wins).
(c) SUPERMARTINGALE UP TO STOPPING TIME. Potential is a supermartingale until the disruption stop
    time; optional-stopping gives the bound. Terminal: optional-stopping lemma applies, or not.
(d) FALLBACK decomposition. Split each keystone into the per-phase ProbHitWithin sub-lemmas +
    composition; grind each sub-lemma (Codex), assemble. Always available.

## Fallbacks if all fail
Surface to Xiang with the concrete per-avenue terminal verdicts (NOT "feels hard"). Method downgrade
(weaken the bound, drop a phase) is Xiang's call, not auto-taken.

## Collaboration
ChatGPT Pro (R3+ via bridge) for the canonical disruption-free-phase technique; Codex (tmux) for the
Lean proof-grind of each phase ProbHitWithin + the composition. No effort caps in briefs.

## R3 ARCHITECTURE (ChatGPT Pro, canonical — avenue (a) confirmed)
3 generic lemmas: (1) stopped_descent E[τ_{G∪D}]≤B (cxr2: awakening relaxed-goal); (2) disruption
tail via LOAD CERTIFICATE not (1-q)^K: Pr[τ_D≤K] ≤ n·Pr[Bin(K,2/n)≥Emax], Emax=Θ(n)⟹safe K=O(n²);
(3) RACE: E[τ_{G∪D}]≤B ∧ Pr[τ_D≤K]≤δ ∧ B/K≤η ⟹ Pr[G before D ≤K]≥1−η−δ (K=4B,δ≤1/4→≥1/2). Absorbing
wrapper (live/good/bad) for Lean. CORRECTION: sharpen awakening per-step 1/n²→k/n² (coupon O(n²log n));
but fit Emax=Θ(n) window ⟹ aim awakening goal EARLY (heap-prefix≥2, O(n²)), not wake-all. Compose
const phases → product const → window_mul_inv; disruption = failed attempt, strong-Markov restart,
geometric ≤1/p.
