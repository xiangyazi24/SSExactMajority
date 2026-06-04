# Codex task (uisai1): quantitative phiCount macro-descent (the optimal-bound core)

The optimal bound = variable_descent on `phiCount` (BurmanConvergenceFinal.lean:3412,
= #agents with answer=.phi, ≤ n). Outer recursion is settled. The CORE inner bound:

NEW file `SSExactMajority/UpperBound/Time/PhiDescent.lean`. Prove the per-macro-step
expected-time bound that feeds `expectedHittingTime_le_of_variable_descent_until_goal`
(ExpectedTime.lean:4379) with φ = phiCount:

> From a reachable/bounded Pinv config C with `phiCount C = k > 0`, the expected time to
> reach `{D | phiCount D < k ∨ IsConsensusConfig D}` is ≤ a polynomial (e.g. c·Rmax·n²).

i.e. one `.phi` answer gets resolved (committed to a real answer) within poly expected time,
THROUGH the self-stabilization resets (collision/error/propagate). Combined with the variable
descent (≤ n levels) this gives E[T to phiCount=0] ≤ n·poly; then
`isConsensusConfig_of_InSswap_phiCount_zero` (BurmanConvergenceFinal:3443) finishes.

## Structure / building blocks
- `reach_zero_potential_macro` (PotentialReach.lean:90) — the QUALITATIVE analog (∃ schedule
  decreasing φ). Study its `hMacro` to see which interactions resolve a `.phi`.
- A `.phi` answer is set during recruitment (phi-wipe) and resolved on later interaction.
  Identify the resolving interaction; bound the per-step probability ≥ ~1/(n(n-1)); compose.
- The non-monotone resets (collision on same-rank Settled, error-monitoring on errorcount=0
  Unsettled, propagate) must be ABSORBED: a reset does NOT increase phiCount if it doesn't
  introduce new `.phi` — CHECK whether resetOSSR/collision/error set answer=.phi. If they
  preserve answers (resetOSSR_answer_preserved exists, RankDelta.lean:141), phiCount is
  NON-INCREASING under those resets — that is the key fact to establish (unlike #Resetting).
- Use the proven `ConvStep.lean`, the window/E[T] lemmas, `phiCount_eq_*` lemmas.

## FIRST sub-goal (most valuable, do this first)
Prove `phiCount` is NON-INCREASING under every protocol step in the Pinv region:
`∀ C, Pinv C → ∀ i j, phiCount (C.step P i j) ≤ phiCount C`.
KEY: resets preserve/clear answers (don't add .phi) except recruitment; in Pinv (post-seed,
correct) recruitment's phi-wipe is bounded. If phiCount IS non-increasing, the variable
descent applies cleanly (unlike the #Resetting potential which codex showed increases).
Report whether phiCount is non-increasing (with proof) or find the counterexample.

## HARD RULES
- NO sorry/axiom/native_decide. Blocked → exact goal+missing lemma to
  HANDOFF/outbox/codex-phicount-report.md. Don't weaken to trivial / reorganize.
- ONLY PhiDescent.lean. Self-verify lake env lean. NEVER lake build. Report status.
