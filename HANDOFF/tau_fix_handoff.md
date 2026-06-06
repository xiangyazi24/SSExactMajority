# LogRegimeFinal τ-generalization — progress + remaining blocker

## Goal
Make `LogRegimeFinal.lean` compile so `P_EM_solves_SSEM_log` (and hence
`P_EM_solves_SSEM_log_trank1`, τ=1) is τ-parametric. The file was machine-generated
as τ-clones but many helper calls were left pointing at the trank=Rmax originals,
and many τ-result-lemma calls omitted `(τ := τ)`.

## Root cause taxonomy (84 errors, single-file `lake env lean`)
All errors are the SAME family: helper conclusions hardcoded
`protocolPEM n Rmax Rmax` colliding with the surrounding `protocolPEM n τ Rmax`,
or τ-result-lemmas called without `(τ := τ)` so τ can't be synthesized.
`trank` only feeds the wake-timer `7*(trank+4)` in `transitionPEM_prePhase4`;
it does NOT change role/resetcount/leader outcomes — so the trace/step lemmas
ARE trank-polymorphic (proved via `transitionPEM_prePhase4_structural`,
which is `{trank : ℕ}`).

## DONE (clusters 1–4 + Group-1, ~60/84 errors) — all in LogRegimeFinal.lean

New τ-clones added (faithful trank-generalizations of BurmanConvergenceFinal /
BurmanProof originals; only change is `Rmax`→`τ` in the trank slot + `(trank:=τ)`):
- `transitionPEM_prePhase4_dormant_leader_roles_trank`
- `transitionPEM_dormant_leader_nonresetting_bounce_or_nonresetting_trank`
- `transitionPEM_dormant_leader_low_dt_L_partner_wakes_trank`
  (NOTE: `transitionPEM_dormant_leader_with_unsettled_follower_wakes_trank`
   already exists in LogRegimeConvergence.lean:194 — do NOT re-add, it collides.)

Call-site fixes:
- thm `dormant_leader_nonresetting_step_resetFuel_lt_or_seed_trank`: use
  `..._bounce_or_nonresetting_trank (τ:=τ)`.
- thm `transitionPEM_settled_meets_dormant_L_trace_trank`: local `p` was defined
  with `transitionPEM_prePhase4 n Rmax`; changed to `n τ` (8 occurrences incl. the
  `show ... = p from rfl` blocks).
- thm `ranking_from_all_resetting_zero_with_leader_log`: swapped
  `step_leader_dedup_resetLeaderCount_lt` → `_trank (τ:=τ)`,
  `transitionPEM_dormant_leader_low_dt_L_partner_wakes` (×2) → `_trank (τ:=τ)`.
- thm single_pos_follower (F-partner): swapped
  `transitionPEM_dormant_leader_with_unsettled_follower_wakes` → `_trank (τ:=τ)`,
  `drain_pair_rc_FF` → `drain_pair_rc_FF_trank (τ:=τ)`.
- Added `(τ := τ)` to ~60 call sites of LogRegimeFinal-local τ-result lemmas
  (`ranking_from_settled_root_zero_resetting_log`, `ranking_from_all_resetting_zero_log`,
   `ranking_of_no_reset_by_parity_log`, `follower_dormant_or_nonresetting_to_ranking_goal_log`,
   `correctResetSeedStrong_of_*`, `med_correct_live_*`, `reservoir_*`,
   `ranking_field_proof_log`, `*_holds`, `P_EM_solves_SSEM_log_with_strong_seed_prefixes`,
   `burmanConvergence_concrete_log_with_strong_seed_prefixes`, etc.).

Single-file check on the corrected file: **0 errors through line ~7600** (all the
above regions elaborate; the check is just slow on the 64M-heartbeat first-half
proofs — was the silent-death cause the orchestrator flagged).

## REMAINING BLOCKER (Group 2, ~24 errors) — upstream BurmanConvergenceFinal

The post-reset RANKING / SWAP phase entry points are hardcoded
`protocolPEM n Rmax Rmax` and have NO τ-version. Their RESULTS
(`runPairs (n Rmax Rmax) …`) are consumed in `n τ Rmax` contexts in the
strong-seed `_log` theorems, so `simpa [..., hP]` fails. The blocking entries:
- `fresh_start_to_InSrank_ResAns_by_parity_BCF`  (BCF:13609)
- `InSrank_to_InSswap_ResAns_with_inv`            (BCF:10714)
- `even_upper_only_wrong_decision_InSswap_ResAns` (BCF:14572)
- `epidemic_timer_branch_to_consensus`            (BCF:11102)
- `insswap_drain_median_timer_one_step`, `hMedCorrectExit_from_reservoir_entry_and_reset_leaf`,
  `majorityAnswer_runPairs_eq`, and the even/odd decision-decrease lemmas.

These bottom out in `private heapPrefix_ranking_with_ResAns_even_BCF` (BCF:13352)
and the swap-misorder induction in `InSrank_to_InSswap_ResAns_noPhi_with_swapInv`
(BCF:10589) — ~442 `n Rmax Rmax` occurrences in BCF. The leaf step lemmas
(BCF:11207+, the `*_explicit*` descent lemmas) ARE already `{trank Rmax : ℕ}`,
but the composition layers above them are not.

### Required to finish
τ-generalize the BCF ranking/swap composition layers (statements: `Rmax`→`trank`
in the protocol's first slot; thread `trank` through; the leaf lemmas already take
it). This is correct in principle — `FreshRankingStart`/`SwapInv` do NOT constrain
the timer, and the ranking phase re-establishes `timer ≥ 2` itself, so the wake-seed
value `7*(trank+4)` is irrelevant to the conclusions — but it is a multi-thousand-line
edit to the 14000-line BCF file plus a full rebuild. Recommend doing it bottom-up
(clone the private workhorses to `_trank`, then the `*_BCF`/`*_with_inv` entries),
verifying each layer compiles before moving up.

## Verification commands
Single-file (fast iteration, capped threads):
  ssh uisai1 "cd ~/repos/SSExactMajority && LEAN_NUM_THREADS=4 nohup \
    /data/home/xhuan5/.elan/bin/elan run leanprover/lean4:v4.30.0 lake env lean \
    SSExactMajority/Convergence/LogRegimeFinal.lean > /tmp/lrf.log 2>&1 & echo ok"
Full integrated (only at the very end):
  lake build SSExactMajority.Convergence.LogTrank1  (LEAN_NUM_THREADS=4)

No sorry/axiom/native_decide introduced anywhere.
