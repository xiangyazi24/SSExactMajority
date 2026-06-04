# ATTACK 3: corrected dormancy predicate + PROBABILISTIC (constant-prob) answer-epidemic bridge

Your attack-2 BLOCKER was CORRECT and valuable: you proved processAgent decrements delaytimer THEN tests, so
"¬(resetcount=0 ∧ delaytimer=0)" is NOT a one-step no-wake condition (rc=0,dt=1 still wakes). My predicate was
wrong. Here is the corrected attack — proceed and WRITE LEAN.

## 1. Derive the EXACT one-step no-wake predicate yourself
From processAgent (RankDelta.lean:50-60), derive the exact predicate `NoWake s` (for role=Resetting,
partnerResetting=true) such that processAgent does NOT fire resetOSSR this step. Likely `resetcount ≥ 1 ∨
delaytimer ≥ 2` (rc≥1 ⇒ the rc=0 branch is not entered; rc=0 ⇒ dt decrements, wakes only if it hits 0, i.e. only
if dt was ≤1). PROVE NoWake → processAgent keeps role=Resetting. Use the exact condition the code gives, not my
guess. Note newly-caught agents have (rc=0, dt=Dmax) — they are dormant via dt, and Dmax≥n by hDmax.

## 2. DormantEpidemicRegion := EpidemicRegion m ∧ (∀ v, role=Resetting → NoWake (C v))
One-step lemma: in DormantEpidemicRegion, a step (a) wakes no one (all stay Resetting), (b) phiCount nonincreasing,
strictly down on a phi/non-phi meet — reuse PROVEN epidemicRegion_step_closed / _phiCount_nonincrease /
_phiPair_descent. Show the step stays in EpidemicRegion (already have _step_closed); the new part is NoWake-preservation.

## 3. PROBABILISTIC bridge (do NOT require deterministic dormancy through the whole epidemic — that is a genuine
race; handle it the renewal way). Prove: from DormantEpidemicRegion, with CONSTANT probability p_epi, the answer
epidemic reaches EpidemicPhiGoal within K_epi (= epidemic_coupon_sum_le_nsq quadratic window) WHILE staying
DormantEpidemicRegion (no wake) the whole time. If a wake happens first (counters drain before the epidemic
finishes), that path just fails this attempt — the OUTER renewal already retries the whole reset cycle with
constant per-cycle success prob, so a CONSTANT p_epi suffices. So the bridge is:
  DormantEpidemicRegion → p_epi ≤ ProbHitWithin (EpidemicPhiGoal m) K_epi   (constant p_epi, no-wake maintained on the hit paths)
Assemble from: per-step phiCount-descent probability (epidemicRegion_phiPair_descent gives the productive pairs) +
the no-wake-maintenance + the quadratic hitting bound. The dormancy window need only outlast the epidemic with
CONSTANT prob, not w.p.1.

## 4. resetReach (CITED [12], faithful): change target to DormantEpidemicRegion (all-Resetting, FRESH counters:
seeds rc=Rmax≥1 ⇒ NoWake; this is reach-all-Resetting = [12] Lemma 3.2/Cor 3.5). NOT EpidemicPhiGoal.

## 5. Compose: resetReach → DormantEpidemicRegion → (bridge, step 3) → EpidemicPhiGoal → (proven silence link) →
OW_silenceEndpoint. Thread WellFormed/MajInv; the two finite windows compose (K_reset + K_epi, both O(n^2)); keep
bound <= K*n; renewal factor carries p_reset*p_epi (both constant).

## HARD: WRITE AND PROVE LEAN. No analysis-only. No sorry/axiom. Full lake build. resetReach MUST be faithful
(target DormantEpidemicRegion, NOT answer-done). The answer epidemic MUST be locally proven (constant-prob bridge),
not cited. Stop only on a SPECIFIC false sublemma (### BLOCKER + Lean counterexample), not on "hard". Report what
you PROVED (theorem names + file:line) to HANDOFF/outbox/cxreset-report.md.
