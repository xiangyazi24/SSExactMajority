# Next: the answer-epidemic bridge (numeric drain<=1/2 + cited standard epidemic + combine)

The unconditional drain bound is PROVEN: drain_probHitWithin_le_choose_unconditional (DrainNoWakeTrace.lean) gives,
from a fresh all-Resetting start (role=Resetting, delaytimer=Dmax) with 0<Dmax,
  ProbHitWithin (PEMProtocol n 1 Rmax Emax Dmax hn) hn2 C0 SomeAgentAwake K <= n*choose(K,Dmax)*(2/n)^Dmax.

Build the answer-epidemic bridge in a NEW file SSExactMajority/UpperBound/Time/AnswerEpidemicBridge.lean.

## Step 1 — numeric / no-wake probability
Produce: from a fresh start with 0<Dmax, and with the window K and Dmax chosen so that the binomial tail is small,
  no_wake_prob_ge_half : 1/2 <= probNotHitBy (PEMProtocol ...) hn2 C0 SomeAgentAwake K
i.e. the complement of the drain bound. The cleanest: take the numeric tail bound
  hTail : (n:ENNReal)*choose K Dmax*(2/n)^Dmax <= 1/2
as an EXPLICIT hypothesis for now (the asymptotic choose-tail estimate at K=ceil(c*n*clog n), Dmax>=n is standard
but fiddly; defer it as hTail and we instantiate later), then derive no_wake_prob_ge_half via the repo complement
API (ProbHitWithin + probNotHitBy = 1, or ProbHitWithin_ge_one_sub_of_probNotHitBy_le / the existing complement
lemmas in Probability/ExpectedTime.lean).

## Step 2 — cite standard epidemic (clearly labeled, NOT [12], NOT Kanaya)
Introduce a clearly-named hypothesis (a contract field or theorem hypothesis), e.g.
  epidemicFast : from EpidemicRegion m C, p_e <= ProbHitWithin P hn2 C (EpidemicPhiGoal m) K
with p_e a positive constant. This is the standard one-rumor epidemic O(log n)-time result; label it clearly as
the standard epidemic-speed citation, distinct from [12]. Keep it as a hypothesis (scope A: cite standard building block).

## Step 3 — combine into the answer-epidemic bridge
Prove: from a fresh all-Resetting start C0 (which is in EpidemicRegion for m = the spread answer), within K,
  p_e/2 <= ProbHitWithin P hn2 C0 (fun D => EpidemicPhiGoal m D AND <all still Resetting>) K
by combining epidemicFast (epidemic reaches EpidemicPhiGoal w.p. >= p_e) with no_wake_prob_ge_half (no wake w.p.
>= 1/2): on the intersection both hold. Use the repo ProbHitWithin AND/intersection or or-complement lemmas
(ProbHitWithin_or_le_add etc.) — P(A and B) >= P(A) - P(not B) >= p_e - 1/2 if p_e>1/2, OR use a cleaner
intersection bound. If the clean intersection bound needs a missing lemma, state it precisely.

## HARD RULES
New file AnswerEpidemicBridge.lean is yours. Iterate lake build until clean. No sorry/axiom/native_decide.
hTail and epidemicFast may remain HYPOTHESES (clearly labeled). Commit clean with [Xiang-proxy]. Report theorem
names+file:line to HANDOFF/outbox/cxfix-report.md.
