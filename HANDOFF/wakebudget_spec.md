# Fix the one vacuity risk: weaken FreshResetSeedTarget to a reachable wake-budget target, generalize the drain certificate to charge only DORMANT agents

## Why (both independent reviewers flagged this)
FreshResetSeedTarget requires ALL agents to have delaytimer = Dmax SIMULTANEOUSLY. Under random scheduling that
is a synchronization coincidence, not a constant-probability stopping event, so freshSeedReach risks being
vacuous. KEY mechanism fact (verified in propagateReset/processAgent): processAgent decrements delaytimer ONLY
in the dormant branch (role=Resetting AND resetcount=0); a positive-resetcount agent does NOT decrement its
delaytimer and, when it later becomes dormant via the oldRc>0 branch, its delaytimer is reset to Dmax. Therefore
only dormant agents can ever wake, and the no-wake/drain certificate only needs to charge dormant agents.

## Goal
Replace the exact-fresh target by a reachable wake-budget target and generalize the drain bound to use a budget
d (instead of delaytimer = Dmax everywhere). With d = Theta(n) the final O(n) structure is unchanged.

## New target (OptimalWindowsFaithful.lean)
Replace FreshResetSeedTarget by:
  def ResetSeedWithWakeBudget (d : N) (m : Answer) (C) : Prop :=
    EpidemicRegion m C AND AllAgentsResetting C AND
    (forall a, (C a).1.resetcount = 0 -> d <= (C a).1.delaytimer)
(parametrized by budget d, charging only dormant agents). Keep a doc-comment: this is the reachable
post-reset condition the epidemic delivers (every dormant agent has remaining delay budget >= d), faithful to
the implementation, replacing the too-strong simultaneous delaytimer = Dmax.

## Generalize the drain certificate (DrainNoWake.lean / DrainNoWakeCert.lean / DrainNoWakeTrace.lean)
Restrict the wake-load certificate to dormant agents and parametrize by budget d (<= Dmax):
  WakeLoadCertificateAt d γ t C := forall a, (C a).1.role = .Resetting AND (C a).1.resetcount = 0 ->
                                     d <= (C a).1.delaytimer + selectionCount γ a t
Re-prove the step lemma WakeLoadCertificateAt.step with the four transition cases:
 - dormant agent (rc=0) selected: delaytimer decremented by 1, selectionCount +1 => sum preserved (>= d).
 - positive-rc agent selected, stays positive-rc: delaytimer unchanged (processAgent does NOT decrement in the
   rc>0 branch), so it is not yet charged; if/when it becomes dormant its delaytimer is Dmax >= d.
 - positive-rc agent becomes dormant (oldRc>0 branch): processAgent sets delaytimer := Dmax >= d, selectionCount
   >= 0 => d <= Dmax + sc. Need Dmax >= d (carry hd : d <= Dmax).
 - recruitment: a newly-Resetting agent gets delaytimer := Dmax, resetcount := 0 (dormant) => d <= Dmax + sc.
Then re-prove initial_wake_load_certificate from ResetSeedWithWakeBudget (dormant => d <= delaytimer = delaytimer
+ 0), and propagate to wake_load_certificate_PEM_on_no_wake_prefix and the final
drain_probHitWithin_le_choose_unconditional, whose conclusion becomes
  ProbHitWithin (PEMProtocol n 1 ...) C0 SomeAgentAwake K <= n * choose K d * (2/n)^d
with hypotheses: 0 < d, d <= Dmax, AllAgentsResetting C0, and forall dormant a, d <= delaytimer.
(The wake-needs-d-selections argument is the same as before, with d in place of Dmax; the high-load->wake step
already counts selections of the agent that wakes, which is necessarily dormant.)

## Thread through the bridge + faithful chain
- answer_epidemic_bridge_from_fresh_resetting: take the wake-budget hypothesis (AllAgentsResetting + dormant
  budget d) instead of all-delaytimer=Dmax; call the generalized drain bound with d; tail becomes
  drainNoWakeTail n K d. Conclusion (pE/2 <= ProbHitWithin (EpidemicPhiGoal AND AllAgentsResetting) K) unchanged.
- CRSReset12Faithful.freshSeedReach target -> ResetSeedWithWakeBudget d (majorityAnswer C); structure gains the
  budget parameter d (with d <= Dmax).
- faithful_reset_to_phiGoal, crsReset12Faithful_to_generic, PEM_expectedParallelTime_On_faithful: thread d;
  hTail becomes drainNoWakeTail n K_bridge d <= pE/2; keep d = Dmax allowed (so existing instantiations with
  d := Dmax still typecheck and the bound is identical). The O(n) keystone conclusion is otherwise UNCHANGED.

## HARD RULES (automode: NO effort cap)
Iterate lake build SSExactMajority.UpperBound.Time.OptimalWindowsFaithful until clean (this rebuilds the whole
DrainNoWake chain + bridge). No sorry/axiom/native_decide. Keep DrainTailBound.lean usable (drainNoWakeTail with
d). Confirm: (1) the exact-fresh target is gone, replaced by ResetSeedWithWakeBudget; (2) the O(n) keystone
conclusion is unchanged; (3) fresh #print axioms still {propext, Classical.choice, Quot.sound}. Commit clean with
[Xiang-proxy]. Report updated theorem/def names + file:line to HANDOFF/outbox/cxfix-report.md.
