# Fix the round-5 faithfulness regression: prove the answer-epidemic bridge locally (do NOT over-cite [12])

Round-5 regression (independent re-audit): the fix folded Kanayas answer-propagation timing into the
[12]-cited resetReach window — resetReach now targets EpidemicPhiGoal (majorityAnswer fully propagated) directly.
But Burman [12] Lemma 3.2 / Cor 3.5 only give the RESETTING-ROLE epidemic (reach all-Resetting / no-Resetting).
The MAJORITY-ANSWER propagation is Kanaya §5.2, NOT [12]. So citing [12] for answer completion is over-citing.

## Correct faithful decomposition
1. resetReach (CITED [12], faithful): from CorrectResetSeed (+WellFormed), ProbHitWithin to EpidemicRegion
   (all-Resetting, majority answer PRESENT on >=1 agent) within K_reset, prob >= p_reset. Target = EpidemicRegion,
   NOT EpidemicPhiGoal. This matches [12] Lemma 3.2/Cor 3.5 (the role epidemic). Restore this faithful target.
2. answer-epidemic bridge (PROVEN locally — Kanaya part, NOT cited): from EpidemicRegion while DORMANT
   (resetcount>0, agents not yet woken), ProbHitWithin to EpidemicPhiGoal (all answers = majority) within
   K_epi, prob >= p_epi. PROVE this from the already-proven EpidemicMechanics one-step facts + the
   epidemic_coupon_sum-style quadratic hitting bound, gated on the dormancy condition. The answer rides on the
   SAME epidemic dynamics as the role, so this is assemblable from existing machinery, not new theory.
3. dormancy / race: the answer epidemic must finish while agents are dormant (before counters drain & wake).
   Handle it the faithful way: either (a) prove completion-within-the-dormancy-window with constant prob from
   the counter-drain bound, OR (b) if it does not finish in one reset window, agents wake and the protocol
   RE-RESETS — the renewal already retries with constant per-cycle success prob, so a constant-prob
   answer-epidemic per cycle suffices (do NOT need deterministic completion). Use whichever is sound; document.
4. Compose: resetReach (-> EpidemicRegion) THEN answer-epidemic bridge (-> EpidemicPhiGoal) THEN the proven
   silence link (EpidemicPhiGoal+InSswap -> OW_silenceEndpoint) => CRS_to_silence. Keep WellFormed/MajInv
   threading and the final bound <= K*n.

## HARD
This is the genuine math core (Kanaya §5.2 answer-propagation timing), NOT a domain-restriction patch — give it
real effort, no cap. resetReach MUST be faithful to [12] (target = all-Resetting EpidemicRegion, not answer-done).
The answer-epidemic bridge MUST be PROVEN (from EpidemicMechanics), not assumed and not cited. No sorry/axiom.
Full lake build. Report per-hypothesis: which facts are [12]-cited vs locally-proven, and confirm resetReach no
longer over-cites. If the answer-epidemic timing genuinely needs machinery that does not exist, write
### BLOCKER with the precise missing lemma. Report to HANDOFF/outbox/cxreset-report.md.
