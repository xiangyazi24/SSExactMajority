# Codex task (uisai1): lemma 2 — disruption tail via LOAD CERTIFICATE (R3 structure)

DOCTRINE avenue (a) lemma 2. Needed for BOTH Emax regimes (only final numbers differ). Bound the
probability that a DISRUPTION (error-timeout reset) fires within K steps. R3's certificate route
(NOT (1-q)^K). NEW file SSExactMajority/UpperBound/Time/DisruptionTail.lean.

## The disruption event
D = an error-timeout reset fires (rankDeltaOSSR Part 4: an Unsettled endpoint's errorcount, decremented
to 0, becomes Resetting). Concretely D C := ∃ w, (C w).1.role = .Resetting ∧ <woke from Unsettled via
error timeout this step> — but for the TAIL bound, define D structurally as "left the awakening
invariant via an error reset", i.e. reuse ¬IsAwakeningConfig or a dedicated Disruption predicate.

## Load certificate (the key structural fact — protocol-specific)
errorcount decrements ONLY in Part 4 (Unsettled endpoint, not recruit/collision/reset). errorcount
starts at Emax (resetOSSR .F) and decrements ≤1 per interaction in which the agent is a selected
endpoint. So:
  a disruption (some Unsettled hit errorcount 0) before time K  ⟹  some agent a was a selected
  endpoint in ≥ Emax steps before K.
Prove: `disruption_before_K_implies_high_load`:
  (execution hits D within K) → ∃ a, (selectionCount a over the K steps) ≥ Emax,
where selectionCount a = #{t < K : a ∈ {γ_t.1, γ_t.2}}. This needs tracking errorcount over the chain:
errorcount_a(t) ≥ Emax − (selections of a in Part-4 up to t) ≥ Emax − selectionCount_a(t); reaching 0
forces selectionCount ≥ Emax.

## Probabilistic tail (general — can be its own Probability lemma)
Under the uniform ordered-pair scheduler, for fixed a, P(a selected at step t) = 2/n. selectionCount a
~ Binomial(K, 2/n) (sum of indicators; they ARE independent across steps under the product scheduler
measure — the scheduler picks each step's pair independently). Then UNION bound:
  P[disruption before K] ≤ P[∃ a, selectionCount a ≥ Emax] ≤ n · P[Bin(K, 2/n) ≥ Emax].
Provide `binomial_upper_tail`: P[Bin(K,p) ≥ r] ≤ choose(K,r)·p^r ≤ (e·K·p/r)^r (the crude bound R3
suggested — easier than full Chernoff). Mathlib: `Mathlib.Probability.Distributions.Binomial` or
sum over `Finset.range`; if Mathlib's binomial PMF is awkward, define selectionCount tail directly
from the scheduler product measure.

## FIRST sub-goal
The LOAD CERTIFICATE `disruption_before_K_implies_high_load` (errorcount-drain ⟹ selection-count ≥
Emax) — the protocol-specific heart. Report precisely if the errorcount-over-trajectory tracking
blocks. The binomial tail can be a separate parallel sub-lemma (crude choose-bound is fine).

## HARD RULES (automode — NO effort cap, no "if Mathlib lacks X stop")
- NO sorry/axiom/native_decide. Grind or precise obstruction to HANDOFF/outbox/codex-distail-report.md.
- ONLY DisruptionTail.lean. Self-verify lake env lean. NEVER lake build. Report status precisely.
