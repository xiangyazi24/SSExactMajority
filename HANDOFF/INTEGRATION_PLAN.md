# Integration plan: faithful reset (CRSResetCompletion12) + generic trank=O(1) → instantiated O(n)

## Where we are
- FIXED (uncommitted, OptimalWindows builds): `PEM_expectedParallelTime_optimal` now over PEMProtocolCoupled,
  NON-VACUOUS, using faithful `CRSResetCompletion12` (resetReach = ProbHitWithin to EpidemicRegion, K_reset ≤
  C_reset·n^2). Reset contribution O(n^2) seq. Renewal factor (p_reset·128⁻¹)⁻¹.
- DONE (committed a1cdbb1, pushed): cxg GenericTrank.lean — generic windows over PEMProtocol n trank Rmax
  (trank free, T_timer parametric): timer preservation, decision_window, short35, decision_before_timer_zero,
  timer_drain (bound T_timer·n·(n-1)), MAClive, swap_live. 30 thms, 0 sorry.
- BUT the keystone is over PEMProtocolCoupled (trank=Rmax) ⇒ at the Rmax=n instance the median timer is Θ(n)
  ⇒ timer-drain Θ(n^2) parallel. To get O(n) we must instantiate T_timer=O(1), which needs the GENERIC protocol.

## The gap to genuine O(n)
The faithful reset (this codex) is over COUPLED; cxg's O(1)-timer windows are over GENERIC. They must meet in
ONE keystone over the generic protocol PEMProtocol n trank Rmax, then instantiate trank=1 (T_timer=35).

## Steps
1. GENERICIZE the faithful reset contract: define CRSResetCompletion12 (or reuse) over PEMProtocol n trank Rmax
   instead of PEMProtocolCoupled. The reset dynamics (role/resetcount epidemic) are INDEPENDENT of the median
   timer scale trank ⇒ resetReach/stepAllResetting/etc. should transfer via the same InSrank/region step-equality
   cxg used (generic_step_eq_coupled_of_InSrank) or directly. Confirm no trank dependence in the reset region.
2. ASSEMBLE a generic keystone PEM_expectedParallelTime_optimal_generic over PEMProtocol n trank Rmax, consuming
   cxg's generic windows (GenericTrank.lean) + the generic faithful reset contract. Same renewal composition as
   the coupled keystone, but T_timer is now a free parameter (not 7(Rmax+4)).
3. INSTANTIATE: trank=1 ⇒ T_timer = 7·(1+4) = 35 = O(1); C_rank=O(1), K_reset≤C_reset·n^2, T_rank/T_rerank=O(n^2)
   cited [12]; p_reset=const. ⇒ OW_globalWindow = O(n^2) ⇒ E[parallel] ≤ O(n^2)·const/n = O(n). WIN 1 (Rmax=n).
4. WIN 2 (faithful paper Rmax=ceil 60 log n): weaken resetReach's precondition from CorrectResetSeed (needs Rmax≥n)
   to a reset-TRIGGERED state (1-2 resetting agents, Rmax=60 log n compatible). Then instantiate Rmax=ceil(60 log n),
   trank=1. Split: PEM_paper_expected_time (faithful) vs PEM_deterministicReset (Rmax=n variant).
5. RE-AUDIT (§3.3, push first): self + codex + ChatGPT on the instantiated O(n) theorem. Every hypothesis
   satisfiable + faithful; full lake build; #print axioms clean on the instantiated (discharged-where-possible)
   theorem; confirm the bound is genuinely O(n) parallel and NOT vacuous.

## Orchestration note
One-file-one-writer: generic reset contract + generic keystone likely go in GenericTrank.lean or a new
Integration file (NOT both codexes on OptimalWindows simultaneously). Build the full repo once after assembly.
