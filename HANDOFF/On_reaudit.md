# Adversarial re-audit: is PEM_expectedParallelTime_On a GENUINE non-vacuous O(n)?

Context: prior audit found the OLD time keystone operationally VACUOUS (CRSResetDuration12.resetInv was a FALSE
∀-invariant: CorrectResetSeed→EpidemicRegion, but EpidemicRegion needs ALL agents Resetting). We rebuilt it.
Now audit the FIXED, instantiated theorem at commit 4262403 (xiangyazi24/SSExactMajority, pushed).

Target: `PEM_expectedParallelTime_On` in `SSExactMajority/UpperBound/Time/GenericKeystone.lean`.
Default stance: assume it has a hole; try to find it.

## Questions
1. NON-VACUITY: Are ALL hypotheses of PEM_expectedParallelTime_On SATISFIABLE and faithfully derivable from [12]?
   - h12ranking (expectedHittingTime to InSrank ≤ C_rank·n²), h12rank, h12reRank (ProbHitWithin ≥ 1/2 windows).
   - h12resetCompletion : CRSResetCompletion12Generic (trank=1) — its `resetReach` field: is it a genuine
     ProbHitWithin window (CorrectResetSeed → p_reset ≤ ProbHitWithin to EpidemicRegion within K_reset), i.e.
     SATISFIABLE, NOT a disguised false ∀-invariant like the old resetInv? Construct the satisfiability argument
     (a fresh CorrectResetSeed DOES reach all-Resetting w.h.p. within O(n²) — so p_reset>0 is achievable).
   - Could ANY hypothesis be unsatisfiable (making the theorem vacuous like before)?
2. GENUINE O(n): Does the conclusion bound give O(n) PARALLEL? Check OW_globalWindow_trank1_quadratic proves
   OW_globalWindow ≤ const·n² (with K_reset,T_rank,T_rerank = O(n²), timer=35=O(1), C_rank=O(1)), so the final
   bound = const·n²·(128/p_reset)/n = O(n). Any hidden factor (a window term not bounded by n², a non-constant
   multiplier, p_reset that must shrink with n)?
3. FAITHFUL TIMER: trank=1 ⇒ PEM_trank1_timer = 7·(1+4) = 35. Is the median timer genuinely O(1) and ≥ the
   required floor (decision needs MedianTimerAtLeast 35; 35 = exactly the floor)? Is the protocol PEMProtocol n 1
   Rmax … a faithful constant-trank instance (the paper says trank=O(1))?
4. REGRESSION: did genericizing CRSResetCompletion12 → CRSResetCompletion12Generic, or the generic keystone
   composition, reintroduce any vacuity / false invariant / over-strong hypothesis / parameter coupling that
   breaks the asymptotic?

## Verdict
Classify PEM_expectedParallelTime_On as: GENUINE non-vacuous O(n) (conditional on satisfiable+faithful [12]
windows, scope A) — or STILL HAS A HOLE (name it precisely with file:line). Full lake build is reported green
(3266 jobs); confirm or refute by inspecting the statements (mechanical-green does NOT verify non-vacuity).
