# Codex task (uisai1): ranking-init expected-time bound

## Goal (ONE bounded theorem)
In a NEW file `SSExactMajority/UpperBound/Time/RankingInit.lean`, prove a polynomial
expected-hitting-time bound for the ranking-initialization phase:

From an all-Resetting, correct, rc-drained configuration, the protocol reaches a
`FreshRankingStart` (equivalently `HeapPrefix 1` with a settled root + all-Unsettled)
in polynomial expected time. Target statement (adjust the exact predicate/constant to
what is provable, but keep it an E[T] ≤ explicit-poly bound — NOT `< ⊤`):

```
theorem allR_rc0_to_freshRankingStart_expected_le
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hDmaxN : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hAllR : ∀ w, (C w).1.role = .Resetting)
    (hRc0  : ∀ w, (C w).1.resetcount = 0)
    (hLead : ∃! r, (C r).1.leader = .L)        -- single L-leader seed; adjust if needed
    (hAllCorrect : ∀ w, (C w).1.answer = majorityAnswer C)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C)  -- bounds delaytimer too :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C
      (fun D => FreshRankingStart D ∨ IsConsensusConfig D ∨ InSrank D)
      ≤ ((c * Dmax * n * n : ℕ) : ENNReal)   -- pick a concrete poly c·Dmax·n²
```

## Proof approach (the math is settled — this is a coupon-collector descent)
- Potential φ(D) = number of still-`.Resetting` agents (decreasing as agents convert).
- `processAgent` (Protocol/RankDelta.lean:50) fires `resetOSSR` when
  `role=.Resetting ∧ rc=0 ∧ (delaytimer=0 ∨ ¬partnerResetting)`; `.L`→Settled root,
  `.F`→Unsettled. So a scheduled interaction touching a convertible Resetting agent
  decreases φ by 1.
- Per-step descent: from a φ=k>0 state in the invariant, ∃ a pair whose step converts
  one agent, with selection probability ≥ 1/(n(n-1)). Use
  `expectedHittingTime_le_of_variable_descent_until_goal`
  (Probability/ExpectedTime.lean:4379) with this φ and pRate.
- The hard sub-lemma you must build: the PER-STEP conversion lemma — characterize the
  scheduled pair that decreases φ, by unfolding `Config.step → transitionPEM →
  propagateReset/processAgent → resetOSSR`. Model it on `heapPrefix_recruit_step`
  (Convergence/BurmanProof.lean:10939), which does the analogous per-step heap-growth.
- delaytimer is now bounded by M=7(Rmax+4)+Emax+Dmax via IsBoundedConfig (it bounds timer/rc/errorcount/delaytimer/children all ≤ M); use IsBoundedConfig.delaytimer_le. Account for delaytimer drain (≤ M) in the constant.

## Available building blocks (already proven — USE them, don't reprove)
- `expectedHittingTime_le_of_variable_descent_until_goal` (ExpectedTime.lean:4379)
- `PEMProtocolCoupled_preserves_timer_bounded` (Time.lean:5412)
- resetOSSR/processAgent lemmas in Protocol/RankDelta.lean (rc_preserved, answer_preserved,
  settled_rank_zero, leader/follower) and Time.lean (processAgent_preserves_*)
- `heapPrefix_recruit_step`, `dormant_to_RankingEndpoint`, `phase34_rerank` (qualitative
  — for structure reference, BurmanProof.lean)
- `FreshRankingStart` def (BurmanProof.lean:3430), `HeapPrefix`, `RankingEndpoint`

## HARD RULES (audit standard — 以通过 audit 为准)
- **NO `sorry`, NO `axiom`, NO `native_decide`** in the final file. If you genuinely
  cannot close a sub-goal, STOP and write exactly what blocks (the goal state + which
  lemma is missing) to `HANDOFF/outbox/codex-ranking-init-report.md`. Do NOT fake it,
  do NOT reorganize files to dodge the proof, do NOT weaken the statement to trivial.
- Touch ONLY your new file `RankingInit.lean`. Do NOT edit any other `.lean` file.
- Self-verify with `lake env lean SSExactMajority/UpperBound/Time/RankingInit.lean`
  (the import closure is already built; this type-checks fast). NEVER run `lake build`.
  Use `export PATH=$HOME/.elan/bin:$PATH` for lake.
- Append progress + the final status (PROVED / BLOCKED-at-X) to
  `HANDOFF/outbox/codex-ranking-init-report.md` as you go.

## Done when
`lake env lean RankingInit.lean` is error-free and `allR_rc0_to_freshRankingStart_expected_le`
is `sorry`/`axiom`-free, OR you report a precise blocker. Report exactly what you proved.

## UPDATE (master): your delaytimer blocker is correct. Fix: use `IsBoundedConfig (7*(Rmax+4)+Emax+Dmax)` (Time.lean:81 — bounds timer/rc/errorcount/delaytimer/children all ≤ M). It is preserved by PEMProtocolCoupled_preserves_bounded. Continue from your existing RankingInit.lean and prove the now-provable theorem.
