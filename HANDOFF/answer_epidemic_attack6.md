# ATTACK 6: drain-no-wake via the EXISTING high-load-choose tool + a certificate (mirror disruption)

KEY UNLOCK (verified): the probabilistic part is ALREADY DONE by an existing theorem. Do NOT build dormancy
invariants (attacks 2-4 proved that dead). Mirror the existing disruption pattern.

## The existing tool (use it, do not reprove)
`ProbHitWithin_le_schedulerPrefix_high_load_choose` (Probability/SchedulerBridge.lean:277):
  for ANY Goal, given hcert : ∀ S : SchedulerTraceState Q X n K, S.1.2 = true → PrefixHighLoad S.2 r,
  it gives  ProbHitWithin P hn C0 Goal K ≤ n * choose K r * (2/n)^r.
`disruption_ProbHitWithin_le_choose` (315) is a ONE-LINE application of it — your TEMPLATE. Mirror it exactly with
Goal := SomeAgentAwake, r := Dmax.

## The ONLY genuine new lemma: the certificate (deterministic, protocol induction)
Prove hcert for Goal = SomeAgentAwake (∃ agent with role ≠ Resetting), r = Dmax:
  ∀ S : SchedulerTraceState ... K, S.1.2 = true → PrefixHighLoad S.2 Dmax
i.e. "if the trace HIT SomeAgentAwake within K (hit flag S.1.2 = true), then the prefix is high-load: some agent
was selected ≥ Dmax times." Proof = induction on the prefix up to the first hit, maintaining the invariant:
  for every agent a, (selectedCount of a so far < Dmax) → role a stays Resetting.
Contrapositive: an agent leaves Resetting (wakes) only after ≥ Dmax of its own endpoint-selections. Use
processAgent semantics (RankDelta.lean:50-60): a Resetting rc=0 agent wakes only via the dormant branch after its
delaytimer drains, and delaytimer (starting = Dmax on fresh-caught, with hDmax: n ≤ Dmax) decrements only when the
agent is a selected endpoint; ALSO handle the !partnerResetting branch (along an all-Resetting prefix the partner
is still Resetting, so that branch does not fire). Start config: all-Resetting fresh (role=Resetting, resetcount=0,
delaytimer ≥ Dmax for the caught ones; or seeds resetcount=Rmax — either way ≥ Dmax selections to wake).

## Then assemble
1. drain_no_wake_bound := apply ProbHitWithin_le_schedulerPrefix_high_load_choose with the certificate ⇒
   ProbHitWithin SomeAgentAwake K_fast ≤ n*choose(K_fast,Dmax)*(2/n)^Dmax.
2. Numeric: with K_fast = c*n*clog n and Dmax ≥ n, this ≤ 1/2 (REUSE the disruption numeric estimate in
   SchedulerBridge/DisruptionTail if one exists; else a small helper — defer as a hypothesis hTail if needed).
3. h_epidemic_fast (CITED standard epidemic, SEPARATE clearly-labeled field, NOT [12]): EpidemicRegion ⇒
   ProbHitWithin EpidemicPhiGoal K_fast ≥ p_e (constant), K_fast = O(n log n).
4. bridge := combine 1+3 (ProbHitWithin of "EpidemicPhiGoal AND no-wake" ≥ const) via the or/complement bounds.
5. resetReach restored FAITHFUL: target EpidemicRegion (all-Resetting), [12] Lemma 3.2. NOT EpidemicPhiGoal.
6. Compose to silence; WellFormed/MajInv; bound ≤ K*n.

## HARD
The certificate (deterministic protocol induction) is the genuine work — WRITE AND PROVE it, mirror the disruption
proof structure. The probabilistic bound is one application of the existing theorem. resetReach faithful. Only
h_epidemic_fast is cited-standard. No sorry/axiom, full lake build. Report theorem names+file:line.

## DIRECT TEMPLATE for the certificate (this makes it tractable — mirror, do not invent)
DisruptionTail.lean already proves the SAME-SHAPE certificate for the disruption/errorcount case:
- `ErrorLoadCertificateAt.step` (DisruptionTail.lean:90) — the reusable step-invariant maintaining the load
  certificate across one protocol step. MIRROR this for the wake/delaytimer case (define a WakeLoadCertificateAt
  analog: an agent that has left Resetting must have been selected ≥ Dmax times; maintained by processAgent step).
- `initial_error_load_certificate` (109) — base case to mirror.
- `disruption_before_K_implies_high_load` (144) — THE analog of your target: "disruption before K ⟹ high-load".
  Your goal is the identical statement with SomeAgentAwake/Dmax in place of disruption/errorcount.
- `prefix_agent_high_load_mass_le_choose` (228), `prefix_high_load_mass_le_union_choose` (275),
  `disruption_event_mass_le_union_choose` (321) — the mass→choose conversions, already general.
So the certificate proof = mirror `disruption_before_K_implies_high_load` + its `ErrorLoadCertificateAt.step`,
swapping the errorcount/disruption semantics for delaytimer/wake (processAgent) semantics. Selection-count
primitives selectionCount_mono/_succ/_succ_of_selected (36-61) are shared.
