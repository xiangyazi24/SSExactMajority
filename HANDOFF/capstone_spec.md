# CAPSTONE: faithful O(n) keystone at trank=1 — remove the over-citation, reuse all machinery

## Situation
GenericKeystone.lean already PROVES genuine O(n) at trank=1:
  PEM_expectedParallelTime_On (parametric p_reset) and PEM_expectedParallelTime_On_explicit
  give expectedParallelTimeToConsensus (PEMProtocol n 1 ...) C0 <= O(n).
BUT they take CRSResetCompletion12Generic (trank:=1) whose resetReach OVER-CITES [12]: its ProbHitWithin
target is EpidemicPhiGoal (majorityAnswer C) directly (folding the PEM dormancy drain into the citation).

We have already PROVEN the drain + the faithful composition:
  faithful_reset_to_phiGoal (OptimalWindowsFaithful.lean): from CRSReset12Faithful (fresh-seed citation) +
  epidemicFast + hTail, gives CorrectResetSeed -> ProbHitWithin (EpidemicPhiGoal (majorityAnswer C) AND
  AllAgentsResetting) (K_reset+K_bridge) >= p_reset*(pE/2), over PEMProtocol n 1.

## Task — append to OptimalWindowsFaithful.lean (you own it). Add: import GenericKeystone.
Reuse ALL existing machinery; do NOT re-prove the renewal / window / constant.

### Lemma 1 — construct the generic contract from the faithful pieces
Prove crsReset12Faithful_to_generic:
  hypotheses: h12reset : CRSReset12Faithful (n)(Rmax)(Emax)(Dmax) hn p_reset C_reset K_reset;
    epidemicFast : StandardEpidemicFastHypothesisPEM n Rmax Emax Dmax K_bridge hn hn2 pE;
    hTail : drainNoWakeTail n K_bridge Dmax <= pE/2;
    hpE_pos : 0 < pE; hpE_le_one : pE <= 1; hDmax : n <= Dmax;
    C_bridge : N with hBridgeWindow : K_bridge <= C_bridge * n * n;
  conclusion: CRSResetCompletion12Generic (n:=n)(trank:=1)(Rmax:=Rmax)(Emax:=Emax)(Dmax:=Dmax) hn
                (p_reset * (pE/2)) (C_reset + C_bridge) (K_reset + K_bridge).
  Fields:
   - resetProb_pos: 0 < p_reset*(pE/2) from h12reset.resetProb_pos and hpE_pos (ENNReal.mul_pos; pE/2>0).
   - resetProb_le_one: p_reset*(pE/2) <= 1 from resetProb_le_one and pE/2 <= 1 (pE<=1).
   - resetConstant_pos: 0 < C_reset + C_bridge from h12reset.resetConstant_pos.
   - resetWindow_quadratic: K_reset+K_bridge <= (C_reset+C_bridge)*n*n from h12reset.resetWindow_quadratic +
     hBridgeWindow (nlinarith / ring + omega; (C_reset+C_bridge)*n*n = C_reset*n*n + C_bridge*n*n).
   - resetReach: intro hn2 C hWF hSeed. From faithful_reset_to_phiGoal (using hWF.1 : IsTimerBoundedConfig
     (7*(1+4)) C — note WellFormed 1 unfolds to IsTimerBoundedConfig (7*(1+4)) C AND ...; 7*(1+4)=35; and
     hSeed) get p_reset*(pE/2) <= ProbHitWithin ... (EpidemicPhiGoal (majorityAnswer C) AND AllAgentsResetting)
     (K_reset+K_bridge). Then Probability.ProbHitWithin_mono_goal drops the AllAgentsResetting conjunct to land
     on target EpidemicPhiGoal (majorityAnswer C). (mono_goal needs the pointwise implication
     EpidemicPhiGoal m D AND AllAgentsResetting D -> EpidemicPhiGoal m D, i.e. And.left.)

### Lemma 2 — the faithful O(n) keystone
Prove PEM_expectedParallelTime_On_faithful with the SAME cited window hypotheses as
PEM_expectedParallelTime_On (h12ranking, h12rank, h12reRank, over PEMProtocol n 1) PLUS the faithful reset
pieces (h12reset, epidemicFast, hTail, hpE_pos, hpE_le_one, hDmax, C_bridge, hBridgeWindow), concluding:
  for all C0, WellFormed 1 Rmax Emax Dmax C0 ->
    expectedParallelTimeToConsensus (PEMProtocol n 1 Rmax Emax Dmax hn0) hn2 C0 <=
      OW_globalWindow n C_rank PEM_trank1_timer (K_reset+K_bridge) T_rank T_rerank
        * ((p_reset*(pE/2)) * (128)inv)inv / n
  by calling PEM_expectedParallelTime_On with p_reset := p_reset*(pE/2), C_reset := C_reset+C_bridge,
  K_reset := K_reset+K_bridge, and h12resetCompletion := (crsReset12Faithful_to_generic ...). Everything else
  passes through unchanged.

### Optional Lemma 3 (do if Lemma 2 builds cleanly) — explicit linear constant
Mirror PEM_expectedParallelTime_On_explicit but with the faithful reset, giving an explicit O(n) bound
(linear coefficient as a Nat times n). If the product probability p_reset*(pE/2) is not a clean 1/2, keep
it parametric (a positive-constant factor in the linear coefficient) and just show the bound is
(some explicit Nat expression in C_rank, C_reset, C_bridge, ... and (p_reset*(pE/2))inv) * n. Don't force 1/2.

## HARD RULES
Append to OptimalWindowsFaithful.lean; do NOT edit GenericKeystone / OptimalWindows / AnswerEpidemicBridge /
DrainNoWake* (read-only, import them). Iterate lake build SSExactMajority.UpperBound.Time.OptimalWindowsFaithful
until clean. No sorry/axiom/native_decide. The cited window hypotheses + p_reset/pE/hTail/hBridgeWindow stay
labeled hypotheses. Commit clean with [Xiang-proxy]. Report theorem names + file:line to
HANDOFF/outbox/cxfix-report.md, and state explicitly whether PEM_expectedParallelTime_On_faithful is O(n)
(window O(n^2) over /n, prob factor positive constant).
