# Codex task (uisai1): GENERIC race lemma — "good before bad with constant probability"

DOCTRINE avenue (a), ChatGPT R3's canonical structure. This is the reusable, protocol-INDEPENDENT
probability lemma that lets a phase succeed despite disrupting resets (treats disruption as a killed
outcome). NEW file SSExactMajority/Probability/PhaseRace.lean (import the Probability layer:
expectedHittingTime, ProbHitWithin, stepDist — see ExpectedTime.lean / DriftHittingTime.lean).

## Target (R3's race lemma)
For a protocol P, start C, predicates G (good exit) and D (bad/disruption), window K:
```
theorem probHit_good_before_bad_ge
  (P) (hn) (C) (G D : Config → Prop) (K : ℕ) (B : ENNReal) (δ : ENNReal)
  (hExp : expectedHittingTime P hn C (fun X => G X ∨ D X) ≤ B)
  (hBad : ProbHitWithin P hn C D K ≤ δ) :
  -- conclusion: prob of reaching G within K WITHOUT having hit D first
  (1 - B / K - δ) ≤ ProbGoodBeforeBad P hn C G D K
```
where ProbGoodBeforeBad is "reach G by time K and D not reached by time K". Proof (R3):
Pr[G before D, ≤K] ≥ Pr[τ_{G∪D} ≤ K] − Pr[τ_D ≤ K] ≥ (1 − E[τ_{G∪D}]/K) − δ ≥ 1 − B/K − δ.
First step: if G∪D reached by K and D not reached by K, the reached state is G.
Markov: ProbHitWithin(G∪D) K ≥ 1 − E[τ_{G∪D}]/K.

## Implementation choice (R3's recommendation — pick the cleaner for our framework)
Option A (absorbing wrapper): define an absorbing 3-state lift (live C / good / bad) with transitions
live→good if G, live→bad if D, else live→live; good/bad self-loop. Then "ProbHitWithin good K" in the
lift = "G before D within K" in P. Prove the equivalence + the race inequality there.
Option B (direct): if our ProbHitWithin/probReached calculus can express "G by K and ¬D by K"
directly (e.g. via probReached on G ∧ a never-D-so-far predicate), prove the inequality directly.
Check ExpectedTime.lean for the cleanest primitive. Use whichever is provable with our API.

## Sub-lemma likely needed (prove it if missing)
General Markov: `ProbHitWithin P hn C Goal K ≥ 1 − expectedHittingTime P hn C Goal / K`.
(We have ProbHitWithin_ge_half_of_expectedHittingTime_le = the K=2·E case; generalize, or derive
the race bound from the existing 1/2 version with K chosen = 4B so B/K = 1/4.)

## FIRST sub-goal
Prove the general Markov sub-lemma (ProbHitWithin ≥ 1 − E/K) OR adapt the existing 1/2 version, then
the race inequality. If the absorbing-wrapper equivalence is heavy, do Option B. Report which.

## HARD RULES (automode — no effort cap)
- NO sorry/axiom/native_decide. Grind or report precise obstruction to
  HANDOFF/outbox/codex-race-report.md. ONLY PhaseRace.lean. Self-verify lake env lean. NEVER lake build.
