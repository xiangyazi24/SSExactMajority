# Codex task (uisai1): sharpen awakening descent to k/n² (coupon-collector O(n²log n))

DOCTRINE avenue (a), R3 correction. The awakening E[T] is currently coarse card·n(n-1)=O(n³) because
the per-step witness extracts ONE good pair. There are k=card good ordered pairs (root, w) for each
w in awakeningResettingFollowers. Sharpen to k/(n(n-1)) per step ⟹ coupon-collector E[T]=O(n²log n),
which the variable-descent lemma's level-dependent pRate already supports.

Continue in EXISTING SSExactMajority/UpperBound/Time/EntryBound.lean (has awakening_step_descent_witness
/_prob, awakening_to_goal_or_exit_expected_le, all PROVEN).

## Step 1: sharp one-step bound
```
theorem awakening_step_descent_prob_sharp
  (hn4 : 4 ≤ n) (k : ℕ) (hk : 0 < k) (C) (hAwake : IsAwakeningConfig C)
  (hcard : (awakeningResettingFollowers C).card = k) :
  ((k : ENNReal) / ((n*(n-1):ℕ):ENNReal)) ≤
    Probability.ProbHitWithin (PEMProtocolCoupled' n Rmax Emax Dmax hn) (by omega:2≤n) C
      (fun D => FreshRankingStart D ∨ (IsAwakeningConfig D ∧ (awakeningResettingFollowers D).card < k)
                ∨ ¬ IsAwakeningConfig D) 1
```
Idea: the k ordered pairs {(root, w) : w ∈ awakeningResettingFollowers C} are DISTINCT, and each, by
the witness mechanism (transitionPEM_settled_meets_dormant_trace / the existing awakening_step_descent
_witness logic), takes C to a config with strictly smaller card (or to goal). Each has scheduler mass
1/(n(n-1)). Sum of k disjoint good pairs ⟹ one-step hit prob ≥ k/(n(n-1)). The existing
awakening_step_descent_witness already proves the (root,w) step lowers card for the witness w; lift to
"every w in the resetting-follower set gives such a pair" and sum the pair masses (they are distinct
ordered pairs ⟹ disjoint scheduler atoms). Look at how ProbHitWithin one-step lower bounds are summed
over disjoint good pairs elsewhere (e.g. rcLevelPotential_one_step_drop_prob, heapPrefix recruit, or
ProbHitWithin_one_lower_bound_of_pairSet in ExpectedTime.lean).

## Step 2: sharp E[T] bound
```
theorem awakening_to_goal_or_exit_expected_le_sharp ... :
  expectedHittingTime ... (the same 4-way goal) ≤ ((C_const * n * n * Nat.log? ... )) -- O(n² log n)
```
via expectedHittingTime_le_of_variable_descent_until_goal with pRate k := k/(n(n-1)). The bound is
Σ_{k<card} (pRate(k+1))⁻¹ = Σ n(n-1)/(k+1) = n(n-1)·H_card ≤ n(n-1)·H_n. Express the harmonic sum bound
in whatever closed ℕ/ENNReal form is cleanest (e.g. ≤ n(n-1)·(some Nat harmonic bound), or just keep
it as the explicit sum Finset.sum if a closed form is painful — the point is it is the coupon-collector
sum, NOT card·n(n-1)). Reuse hInvStep/hNonincrease/hZeroGoal from awakening_to_goal_or_exit_expected_le.

## FIRST sub-goal
Step 1 (the sharp one-step k/(n(n-1)) bound) — the real content (summing k disjoint good pairs). If the
disjoint-pair-sum is genuinely blocked, report the exact obstruction. Then Step 2 is mechanical.

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide. Grind or precise obstruction to HANDOFF/outbox/codex-sharp-report.md.
- ONLY EntryBound.lean. Self-verify lake env lean. NEVER lake build.
