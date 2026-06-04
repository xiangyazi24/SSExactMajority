# ATTACK 4: the answer-epidemic bridge is a PROBABILISTIC RACE — prove it as a joint ProbHitWithin (no deterministic invariant exists)

Your attack-2 and attack-3 counterexamples were both correct and decisive — thank you. They PROVED:
- the one-step no-wake predicate is `NoWakeAgent := 0<resetcount ∨ 1<delaytimer` (processAgent_noWake_role);
- but `NoWakeAgent` is NOT preserved (processAgent_noWake_not_preserved): dormancy DECAYS, so there is NO
  deterministic "stays dormant" invariant. Waking is a MULTI-STEP drain (delaytimer must reach 0).

CONCLUSION (accepted): the answer-epidemic bridge is inescapably a PROBABILISTIC TIMING RACE. Do NOT try to
maintain any one-step dormancy invariant — that path is proven dead. Prove the race directly.

## Key structural facts to exploit
- An agent WAKES (role Resetting -> not Resetting) only after processAgent drains ITS delaytimer (rc=0 case) to 0
  — i.e. only after >= (its current delaytimer) of its OWN processAgent steps. Newly-caught agents start at
  delaytimer = Dmax, seeds at resetcount = Rmax. With hDmax: n <= Dmax and Rmax = n, the FIRST wake is >= ~n of
  some agents own steps away.
- So "role stays Resetting for everyone" (NOT the decaying NoWakeAgent predicate) is what holds for a long time:
  a global potential Phi = min over Resetting agents of (steps-until-it-could-wake) decreases by at most 1 per
  interaction (only the processed agents counter drops), and role-all-Resetting holds while Phi > 0. Phi_initial
  >= ~n. Track THIS, not NoWakeAgent.
- The answer epidemic (majority answer overwriting phi) descends while all-Resetting (proven EpidemicMechanics:
  epidemicRegion_phiPair_descent etc.), and reaches EpidemicPhiGoal within the quadratic coupon window
  (epidemic_coupon_sum_le_nsq).

## What to prove (the bridge)
A JOINT finite-window hit with CONSTANT probability:
  from all-fresh-Resetting (DormantStart), p_epi <= ProbHitWithin P C
      (fun D => EpidemicPhiGoal (majorityAnswer C) D AND <all still Resetting>) K_epi
with p_epi a positive CONSTANT and K_epi = O(n^2) sequential. The "all still Resetting" conjunct is maintained on
the hit paths via the Phi potential (drain has not reached 0 within K_epi). If proving constant prob for the tight
race is too hard with the coupon bound, you MAY instead: (a) lean on the renewal — failure (epidemic not done
before a wake) just re-enters the reset cycle, so a constant per-attempt p_epi suffices and the OUTER renewal
retries; or (b) use an expected-time form if it composes. Use whatever is SOUND.

## Faithfulness constraints (hard)
- resetReach (CITED [12]) MUST target only all-Resetting reach (EpidemicRegion / DormantStart), NOT EpidemicPhiGoal.
  Change it back. That is [12] Lemma 3.2/Cor 3.5.
- The answer epidemic (EpidemicRegion -> EpidemicPhiGoal) MUST be LOCALLY PROVEN (this attack), not cited, not
  assumed.
- No sorry/axiom. Full lake build. Keep final bound <= K*n; renewal carries p_reset * p_epi (both constant).

## Latitude
This is genuine §5.2 probabilistic timing — real work, no effort cap. You have latitude on the PROOF TECHNIQUE
(potential argument, coupling, expected-time, or renewal-retry) as long as resetReach stays faithful and the
answer epidemic is locally proven. WRITE LEAN. Stop only on a SPECIFIC false sub-fact (### BLOCKER + counterexample).
Report proved theorem names + file:line to HANDOFF/outbox/cxreset-report.md.
