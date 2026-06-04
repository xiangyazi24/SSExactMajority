
## Run 2026-06-03 ~23:40 (automode)
- doctrine: docs/DOCTRINE.md @ dce6e30
- approval msg_id: 3580 ("继续")
- starting avenue: (a) escape-to-restart renewal
- first concrete step (R3-independent): relaxed-goal per-phase descents
  (goal includes ¬invariant ⟹ all-pair closure trivial)
- end: <open>
- final result: <open>

## Run 2026-06-04 — genuine O(n) via generic-trank re-param (path confirmed)
- ChatGPT Pro R4 (SHA b0bee4b): verdict (c) generic re-param; (a) downward timer-cap rescale UNSOUND, (b) trank-monotonicity UNSOUND. Both load-bearing claims source-verified:
  - timer is a transition semantic: state literally gets `{ a₀ with timer := 7*(trank+4) }` (BurmanConvergenceFinal.lean:2609) → cannot shrink cap without changing kernel.
  - 35 is a real correctness floor: OW_consensusBound needs MedianTimerAtLeast 35; 7*(1+4)=35 exactly → trank=1 is the minimal sound choice (T_timer=35=O(1)).
- Path: re-state window stack + keystones over PEMProtocol n trank Rmax (cap K, 7(trank+4)≤K), instantiate trank=1/T_timer=35 → O(n). All lake-build verified. b0bee4b (O(n log n)) kept as base until O(n) verified.
- cxg (uisai1 tmux): GenericTrank.lean — generic_transitionPEM_preserves_timer_bound DONE (0 sorry); probing first window for timer-cap-uniformity.

### Path audit complete (all-green) — Xiang-proxy, source-verified
- Q1 n<=Rmax: Rmax = rank-value range (Theta(n)), required as n<=Rmax in keystone; satisfiable (Rmax=n), only enters rank range + cited [12] windows; does NOT break O(n).
- Q2 correctness at trank=1: P_EM_solves_SSEM_master/_concrete (Final.lean:55,141) take {trank Rmax} generic, NO lower-bound on trank. trank=Rmax in BurmanConvergenceFinal is incidental. trank=1 => correct protocol; timer 7*(1+4)=35 hits the MedianTimerAtLeast 35 time-floor exactly.
- Q3 window formula: OW_globalWindow = (2*C_rank*n^2 + T_rerank) + 128*OW_consensusCycleWindow; decisionWindow=2n(n-1)=O(n^2); all blocks O(n^2) when C_rank=O(1),T_timer=O(1),T_reset/T_rank/T_rerank=O(n^2). => OW_globalWindow=O(n^2) sequential; keystone concludes <= OW_globalWindow*8/n = O(n) parallel. No hidden log/extra-n.
Conclusion: genuine O(n) expected is honest at trank=1/T_timer=35, contingent only on honest [12] expected-window values (scope A). Remaining work is mechanical porting (cxg).

### Faithfulness findings (Xiang-proxy, source+axiom verified) — 2 items
1. FORMALIZED vs CITED (Xiang asked): Burman ranking CORRECTNESS is FORMALIZED, not cited.
   - ranking_field_proof (BurmanConvergenceFinal:2262) proves exists-scheduler reaching InSrank from any C0.
   - burmanConvergence_concrete (15941) proves the full BurmanConvergence structure for rankDeltaOSSR.
   - P_EM_solves_SSEM_final (16052): SolvesSSEM, NO external hyps. #print axioms = [propext, Classical.choice, Quot.sound] ONLY. 0 sorry (35 grep hits all comments).
   - ONLY [12]-cited thing: ranking EXPECTED-TIME srank=O(n) ([12] Thm 4.3 = Kanaya Lemma 3), as h12* hyps in the PARALLEL-TIME keystone. We formalize the renewal/window composition; cite ranking expected-time.
2. Rmax DEVIATION (escalated to Xiang, awaiting decision): formalized protocol uses Rmax=n, NOT paper 60 log n.
   - P_EM_solves_SSEM_final => protocolPEM n n n ...; burmanConvergence_concrete requires n<=Rmax (60 log n cannot instantiate).
   - Root: CorrectResetSeed requires nonResettingCount < resetcount, resetcount:=Rmax, nonResettingCount up to n-1 => Rmax>=n. Deterministic reset model vs paper probabilistic (epidemic w.h.p. O(log n) => 60 log n suffices).
   - Preserves: correctness + O(n) EXPECTED time. Sacrifices: space-optimality (resetcount O(log n) bit vs O(log log n)), maybe w.h.p. O(n log n).
   - Decision pending: (i) accept Rmax=n variant (honest, audit-passable), or (ii) reprove reset probabilistically for faithful 60 log n.
   - INDEPENDENCE: trank (median timer) _|_ Rmax (reset counter). cxg trank=1 O(n)-time work is valid under either Rmax choice.

### Adversarial reset-faithfulness audit (dispatched ChatGPT c2d1dea3 + codex cxaudit; my independent analysis)
Mechanism (verified):
- SolvesSSEM (Defs/Execution.lean:48) is EXISTENCE-based: forall C0, exists schedule reaching safe config.
- resetcount: set to Rmax on trigger (RankDelta.lean:205); syncs max(rc-1,rc-1) on resetting-resetting meet (131).
- CorrectResetSeed needs nonResettingCount < resetcount => existence proof needs Rmax >= n (worst-case convert n-1 agents before counter drains). Paper uses probabilistic O(log n)-round epidemic => 60 log n suffices.
My preliminary verdict (HOLD pending reviewers): leans (a)/(c). Rmax=n is a SOUND instance of the parameterized
protocol. Preserves stated asymptotics: O(n) states (sum-over-roles 2n+n=O(n), rank dominates), O(n) expected
time. Deterministic reset = proof-strategy choice avoiding the probabilistic epidemic-speed analysis. NOT a
weaker result; the full O(n)-expected/O(n)-states holds for the Rmax=n instance.
Sharpest OPEN risk for reviewers: are the h12* timing hyps faithfully citable from [12] at Rmax=n (where [12]
Lemma 1/2/Thm 4.3 were stated for resetcount=60 log n)? And does Rmax=n preserve the w.h.p. O(n log n) tail?

### Audit verdict CONSOLIDATED (codex + ChatGPT c2d1dea3 + my source-verification all converge): case (a)
Paper is correct; Lean chain proves a SOUND-BUT-UNFAITHFUL deterministic-reset variant, NOT the paper Rmax=60 log n protocol. Three independent findings, cross-checked:
1. CorrectResetSeed (nonResettingCount < resetcount) is STRICTLY STRONGER than paper reset. All 3 agree; ChatGPT independently derived the counterexample n-2 < 60 log n fails at Rmax=60 log n.
2. Time keystone operationally VACUOUS: resetInv field of h12resetDuration is FALSE (EpidemicRegion requires ALL resetting; CorrectResetSeed allows nonResettingCount>0; counterexample 1 seed + n-1 non-resetting). VERIFIED against EpidemicMechanics.lean:18 + BurmanConvergenceFinal:13787. => h12resetDuration UNSATISFIABLE => keystone is a well-formed conditional theorem with an unsatisfiable premise, can never be discharged to a real bound.
3. Even ignoring (2): resetWindow forces T_reset >= 2n^3 (OptimalWindows:476), additive in window => O(n^2) parallel, not O(n)/O(n log n). [codex+my verification; ChatGPT lacked repo access, guessed O(n) parallel.]
4. Final qualitative theorem uses protocolPEM n n n (trank=Rmax=n) => median timer 7(n+4)=Theta(n) => timer-drain Theta(n^2) (ChatGPT). cxg trank=1 fixes THIS but inherits false resetInv.
5. Correctness P_EM_solves_SSEM_final SOUND (clean axioms) but proves the Rmax=n deterministic variant.
FIX (reviewer consensus): demote CorrectResetSeed to post-success target; prove/cite faithful reset window reset_trigger->good-reset w.h.p. via [12] Lemma 3.2/Cor 3.5 at Rmax=60 log n (K_reset=O(n^2) seq); fix n^3 window; keep trank=O(1) (cxg, valid). Split theorems: faithful-paper (trank=O(1), Rmax=ceil 60 log n) vs deterministic-variant (n<=Rmax).
