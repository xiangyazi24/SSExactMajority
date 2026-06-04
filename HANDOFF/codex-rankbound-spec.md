# Codex task (uisai1): OW_rankBound via recruitment-descent + drift theorem

GOAL: prove `OW_rankBound` in SSExactMajority/UpperBound/Time/OptimalWindows.lean — currently
`sorry`. From any timer-bounded config, E[T to (InSrank ∧ MedianTimerAtLeast 35 ∧ bounded)]
≤ Rmax·n². (You MAY loosen the constant to any explicit poly c·Rmax·n² and adjust the
assembly constant later — report what you used. You may strengthen the START hypotheses to the
reachable invariant if needed, but keep the target faithful.)

## Tools (all PROVEN — use, don't reprove)
- `heapPrefix_recruit_step` (Convergence/BurmanProof.lean:10939): from `HeapPrefix C k`
  (1≤k<n) + `SettledMedianTimerStrong C`, ∃ parent child s.t. one step grows to
  `HeapPrefix C' (k+1)` + median-timer-good. THIS IS THE PER-STEP DESCENT WITNESS.
- `Probability.expectedHittingTime_le_of_drift` (Probability/DriftHittingTime.lean): additive
  drift ⟹ E[T] ≤ φ(C₀)/ε. Use for the descent on φ = n − (heap prefix length), absorbing the
  rare collision/error resets that shrink the prefix as transient increases (negative EXPECTED
  per-step drift: recruitment witness gives ≥1/(n(n-1)) growth; resets are rarer / bounded by rc).
- OR `Probability.expectedHittingTime_le_of_variable_descent_until_goal` (ExpectedTime.lean:4379)
  if a clean variable-descent closes it without the drift machinery.
- `HeapPrefix` (BurmanProof.lean:10200), `RankingEndpoint` (137), `FreshRankingStart` (3430),
  `IsTimerBoundedConfig`/`IsBoundedConfig`, `PEMProtocolCoupled_preserves_timer_bounded`.

## Approach
Define `heapPrefixLen C := ` the max k with `HeapPrefix C k` (or use Σ over Settled agents).
φ C := n − heapPrefixLen C. Goal reached when prefix complete (= ranking endpoint). Per-step:
recruitment pair grows prefix (φ−1, prob ≥1/(n(n-1))); collision/error reset pairs may shrink it
(φ+δ) but are dominated in expectation. Show `∑' D, stepDist·φ D + ε ≤ φ C` on the ranking region
with ε = 1/(n(n-1))·(net), apply the drift theorem.

## FIRST sub-goal (report before attempting the full bound)
Prove the per-step EXPECTED drift inequality on the ranking region (this is the crux). If the
reset terms can't be dominated, report the EXACT obstruction (which reset pairs, what region
strengthening would dominate them) to HANDOFF/outbox/codex-rankbound-report.md — Opus will
refine the region/potential. Do NOT weaken to a trivial/vacuous statement.

## HARD RULES
- NO sorry/axiom/native_decide in the final OW_rankBound. Blocked → exact obstruction to the
  report file. ONLY edit OptimalWindows.lean (+ a new helper file if you must, but NOT
  BurmanProof/Time/ExpectedTime). Self-verify `lake env lean OptimalWindows.lean`. NEVER lake build.
- Report status precisely (PROVED unconditionally / PROVED-modulo-X / BLOCKED-at-Y).
