# ATTACK (no punt): prove the answer-epidemic bridge at Rmax=n via DormantEpidemicRegion

Your last pass only ANALYZED and stopped ("no candidate patch"). That is the banned anti-pattern. This pass you
WRITE LEAN and prove the bridge. It IS tractable at the Rmax=n regime — here is the concrete attack:

## Why it is provable at Rmax = n (the key the analysis missed)
processAgent wakes an agent only when resetcount=0 ∧ delaytimer=0. When two Resetting agents meet, resetcount
syncs to max(rc-1,rc-1) — i.e. an agents resetcount only decreases on meets IT participates in. Over the whole
answer epidemic (~quadratic interactions, epidemic_coupon_sum), any fixed agent participates in only a small
fraction, so its resetcount falls from Rmax=n by far less than n. Hence with Rmax=n the dormancy window (length
~n in per-agent meets) DOMINATES the answer-epidemic cost ⇒ no agent wakes during the answer epidemic ⇒ dormancy
is MAINTAINED throughout. This is the lever; use it.

## Concrete steps (write the Lean)
1. Define `DormantEpidemicRegion C := EpidemicRegion m C ∧ (∀ v, ¬((C v).resetcount = 0 ∧ (C v).delaytimer = 0))`
   (no agent is in the about-to-wake state). Pick the minimal dormancy predicate that processAgent provably does
   NOT wake from.
2. One-step lemma: in DormantEpidemicRegion, a step (a) does not wake anyone (stays all-Resetting), and (b) the
   answer epidemic descends (phiCount nonincreasing; strictly decreasing on a phi/non-phi meet) — reuse the
   PROVEN EpidemicMechanics one-step facts. Show DormantEpidemicRegion is preserved for the epidemics duration
   (resetcount stays >0 because Rmax=n dominates; make this a clean invariant, e.g. carry a lower bound
   resetcount ≥ Rmax - (steps so far)/something, or simpler: bound total per-agent decrements below Rmax).
3. ProbHitWithin: from DormantEpidemicRegion, reach EpidemicPhiGoal m within K_epi (= the epidemic_coupon_sum
   quadratic bound) with prob ≥ p_epi (constant), staying dormant. Assemble from step 2 + the coupon hitting bound.
4. resetReach (CITED [12]): change its target BACK to DormantEpidemicRegion (all-Resetting with FRESH counters
   resetcount=Rmax>0 ⇒ dormant), NOT EpidemicPhiGoal. This is faithful to [12] Lemma 3.2/Cor 3.5 (role epidemic to
   all-Resetting). 
5. Compose: resetReach → DormantEpidemicRegion → (your proven answer-epidemic ProbHitWithin) → EpidemicPhiGoal →
   (proven silence link) → OW_silenceEndpoint. Thread WellFormed/MajInv. Keep bound <= K*n.

## HARD RULES
WRITE LEAN AND PROVE IT — do not produce another analysis-only report. resetReach MUST be faithful (target
DormantEpidemicRegion, not answer-done). The answer epidemic MUST be locally proven from EpidemicMechanics, not
cited, not assumed. No sorry/axiom. Full lake build. Only if a SPECIFIC sublemma is mathematically false (not
"hard") may you stop — then write ### BLOCKER with the exact false statement + counterexample. Report to
HANDOFF/outbox/cxreset-report.md with what you PROVED (theorem names + file:line).
