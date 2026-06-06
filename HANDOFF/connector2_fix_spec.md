# Finish the drain bound: fix DrainNoWakeTrace.lean (mechanical Lean errors) + wire UNCONDITIONAL drain bound

State: the §5.2 wake-load core is PROVEN across DrainNoWake.lean (certificate), DrainNoWakeProtocol.lean (witness),
DrainNoWakeBound.lean (support-restricted bridge + conditional drain), DrainNoWakeCert.lean
(wake_load_certificate_PEM_on_no_wake_prefix). The LAST file, DrainNoWakeTrace.lean (trace-support reconstruction
+ final assembly drain_probHitWithin_le_choose), is drafted but fails to compile with MECHANICAL errors (no math gap).
Fix it by iterating lake build, then wire the unconditional bound.

## Fix these errors in SSExactMajority/UpperBound/Time/DrainNoWakeTrace.lean
1. selectionCount_eq_prefixSelectionCount_of_prefix (~:62-96): the Finset image/card proof is mis-shaped.
   - i.isLt has type (i:Fin K).val < K but used where range-membership was expected; use Finset.mem_range.
   - unfold selectedAt fails: use simp [selectedAt, prefixSelectedAt] or the defeq, not unfold.
   - card_image_of_injective application mis-shaped (rfl fails, No goals). Re-prove cleanly: show
     selectionCount gamma a K = prefixSelectionCount sigma a, given hgamma : forall i:Fin K, gamma i.val = sigma i.
     Easiest is a Finset.card congruence between {t in range K | selectedAt gamma a t} and the image of
     {i:Fin K | prefixSelectedAt sigma a i} under Fin.val; read the EXACT defs (SelectionCount.lean / DisruptionTail.lean)
     and match. Or induct on K.
2. schedulerTraceDist_support_spec base case (~:110, :123): add classical (Decidable for the Goal-or-exists Prop)
   and close the base decide goals.
3. hprefix Fin.snoc mismatch (~:176): fix the Fin.lastCases / use Fin.snoc_last and Fin.snoc_castSucc.
Keep the structure (support_spec by induction on K; exists_first_success_before_strong; the final
drain_probHitWithin_le_choose taking hLoadCert).

## Then WIRE the unconditional drain bound
Add a theorem (in DrainNoWakeTrace.lean; you MAY add `import SSExactMajority.UpperBound.Time.DrainNoWakeCert`):
  drain_probHitWithin_le_choose_unconditional : for C0 fresh (all role = Resetting and delaytimer = Dmax) and 0 < Dmax,
  ProbHitWithin (PEMProtocol n 1 Rmax Emax Dmax hn) hn2 C0 SomeAgentAwake K <= n * choose K Dmax * (2/n)^Dmax
by applying drain_probHitWithin_le_choose with the hLoadCert hypothesis discharged using the PROVEN
wake_load_certificate_PEM_on_no_wake_prefix from DrainNoWakeCert.lean (adapt to its exact signature: it gives the
certificate at the endpoint T of any no-wake prefix from the fresh start).

## HARD RULES
Iterate lake build SSExactMajority.UpperBound.Time.DrainNoWakeTrace until clean. No sorry/axiom/native_decide.
DrainNoWakeTrace.lean is yours; do NOT edit DrainNoWake / DrainNoWakeProtocol / DrainNoWakeBound / DrainNoWakeCert
(read-only). Commit when clean with a [Xiang-proxy] tag. Report theorem names + file:line to HANDOFF/outbox/cxfix-report.md.
