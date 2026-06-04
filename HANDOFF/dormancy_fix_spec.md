# Fix round-5 hole: dormancy lower-bound on epidemic-step fields + discharge from EpidemicMechanics

Hole: CRSResetCompletion12Generic.epidemicStep / epidemicNonincrease / epidemicPairDescent are quantified over
ALL EpidemicRegion configs. But processAgent (RankDelta.lean) wakes an agent OUT of .Resetting when
resetcount=0 ∧ (delaytimer=0 ∨ !partnerResetting). So an EpidemicRegion config with drained counters leaves
EpidemicRegion next step => these fields are unsatisfiable there. WellFormed (upper bounds only) does not exclude it.

## Key structural insight
These epidemic-step fields are NOT [12] citations — they are meant to be DISCHARGED from the already-PROVEN
EpidemicMechanics theorems. Only resetReach is the genuine [12] citation. So the right fix is to make these
fields PROVEN, not assumed-and-over-strong.

## Fix
1. Add a DORMANCY condition to the epidemic-region step assumptions: the one-step epidemic facts hold while the
   resetting agents are still dormant, i.e. resetcount > 0 (or the precise predicate under which processAgent does
   NOT wake: ¬(resetcount=0 ∧ (delaytimer=0 ∨ partner-not-resetting))). Either (a) strengthen EpidemicRegion /
   the epidemic invariant to include dormancy, or (b) add a Dormant precondition to epidemicStep/epidemicPairDescent.
2. Under that dormancy condition, DISCHARGE epidemicStep/epidemicNonincrease/epidemicPairDescent from the PROVEN
   EpidemicMechanics theorems (turn them from CRSResetCompletion12Generic hypothesis FIELDS into internally-proven
   lemmas), so the contract no longer EXPOSES them as potentially-over-strong assumptions. If they cannot be fully
   discharged and must remain fields, then they MUST be satisfiable under the dormancy condition (state the
   condition so a real EpidemicRegion-dormant config satisfies them) — and document why.
3. The RACE (epidemic must complete before counters drain / agents wake) is the job of resetReach (the cited [12]
   window: reach EpidemicRegion-completed/silence within K_reset w.p. p_reset). Confirm resetReach target +
   K_reset<=C_reset*n^2 still covers this; do not weaken it.
4. Re-thread: ensure the dormancy invariant (if added to the region/targets) is preserved and supplied by the
   renewal chain alongside WellFormed + MajInv. Keep the conclusion <= K*n.

## Verify
Full lake build, forbidden-token scan, update the per-hypothesis satisfiability table (now: which epidemic-step
facts are PROVEN vs which remain [12]-cited; confirm every remaining hypothesis satisfiable+faithful). Report to
HANDOFF/outbox/cxreset-report.md. HARD: no sorry/axiom; do not weaken O(n); if a fact genuinely cannot be proven
from EpidemicMechanics nor faithfully cited, write ### BLOCKER with the precise obstruction.
