# Adversarial faithfulness audit: deterministic-reset (Rmax≥n) vs paper's probabilistic-reset (Rmax=60 log n)

## Context
We are formalizing in Lean 4 the self-stabilizing exact-majority population protocol PEM of Kanaya,
Eguchi, Sasada, Ooshita, Inoue (2025, arXiv:2503.17652). Scope: we CITE reference [12] (Burman et al.,
optimal silent self-stabilizing ranking) as hypotheses and formalize Kanaya's contribution on top.
Repo HEAD = 292401d (uisai1:~/repos/SSExactMajority).

## What the PAPER does (verified from the PDF)
- Algorithm 1 line 24: on triggering a reset, every agent sets `(role, leader, resetcount) := (Resetting, L, Rmax)`,
  with **Rmax = 60 log n**.
- The Resetting role spreads by epidemic; "all agents are reset within O(log n) time WITH HIGH PROBABILITY."
- Lemma 1 (= Lemma 3.2 in [12]): roles become Resetting within 4 log n time w.h.p.
- Lemma 2 (= Cor 3.5 in [12]): reach a no-Resetting config within O(n) time w.h.p.
- These reset-completion facts are CITED from [12], not reproved by Kanaya.
- Upper bound (Table 2) is a probabilistic RENEWAL: each phase (Call→Srank, Srank→Tswap∪Stim, Tswap→Sdec,
  Sdec→Stim, Stim→Sem) succeeds with a CONSTANT probability in O(n) time; on failure the protocol restarts
  via Propagate-Reset. Expected total O(n); w.h.p. O(n log n). "these transitions are probabilistic."
- timer ∈ [0, 7(trank+4)], trank = O(1) with srank ≤ trank·n. So the median timer is O(1)-bounded.
- State count O(n): "the SUM of the states required for each role"; ranking vars contribute O(n) (rank ∈ [1,n]).

## What OUR FORMALIZATION does (verified from the Lean source)
- `CorrectResetSeed C` (BurmanConvergenceFinal.lean:13787) requires, for the reset seed agent r:
  `(C r).role = Resetting ∧ nonResettingCount C < (C r).resetcount ∧ (C r).leader = L ∧ (C r).answer = majorityAnswer C`
  and for every Resetting agent w: `0 < (C w).resetcount ∧ (C w).answer = majorityAnswer C`.
- The CRS-construction lemmas (CRSEven.lean etc.) discharge `nonResettingCount < resetcount` by setting
  `resetcount := Rmax` and proving `nonResettingCount ≤ n-2 < n ≤ Rmax`, i.e. they REQUIRE the hypothesis
  `hRmax : n ≤ Rmax`.
- `burmanConvergence_concrete` REQUIRES `n ≤ Rmax`. The ultimate theorem `P_EM_solves_SSEM_final` instantiates
  `Rmax := n` (concludes `SolvesSSEM (protocolPEM n n n (rankDeltaOSSR n Emax Dmax hn))`).
  `#print axioms P_EM_solves_SSEM_final = [propext, Classical.choice, Quot.sound]` (no sorry, no custom axiom).
- The parallel-time keystone `PEM_expectedParallelTime_optimal` also assumes `n ≤ Rmax` and cites [12] timing
  as hypotheses (h12ranking expected-hitting ≤ C_rank·n², h12rank/h12reRank ProbHitWithin ≥ 1/2, h12resetDuration).
- So the ENTIRE chain (correctness + time) holds only for Rmax ≥ n. Rmax = 60 log n cannot be instantiated
  (n ≤ 60 log n is false for large n).

## The suspected hole
Our formalization seems to have replaced the paper's PROBABILISTIC reset (resetcount=60 log n, epidemic covers
all agents w.h.p. in O(log n)) with a DETERMINISTIC over-condition (`nonResettingCount < resetcount`, which a
reset seed of size ≥ n satisfies against up to n-1 non-resetting agents), and to make that hold it set
Rmax = n instead of 60 log n.

## Questions (please reason adversarially; the default suspicion is that we have a faithfulness hole)
1. Is `CorrectResetSeed`'s `nonResettingCount < resetcount` a faithful rendering of the paper's reset
   mechanism, or is it a STRICTLY STRONGER deterministic condition that lets us avoid the paper's w.h.p.
   epidemic argument? In the paper, does a single reset seed need to deterministically "dominate" all
   non-resetting agents, or does it only need the epidemic to cover them w.h.p.?
2. Does the paper's O(n)-expected / O(n log n)-w.h.p. result actually HOLD for the instantiation Rmax = n,
   or does any part of it specifically require Rmax = Θ(log n)? Concretely: (a) state count — is it still
   O(n) with resetcount ∈ [0,n] (n values) given rank already needs n values? (b) reset duration — with a
   counter of size n vs 60 log n, does a single reset still complete in O(n) time, and does the EXPECTED
   total stay O(n)? (c) the w.h.p. O(n log n) bound — does Rmax=n break it?
3. Is there a CIRCULARITY or vacuity risk: by making the reset deterministic (Rmax≥n) and citing [12]'s
   reset/ranking TIMING as separate hypotheses (h12*), could our `SolvesSSEM` correctness be "too easy"
   in a way that hides a genuine difficulty the paper handles, OR could the time keystone's hypotheses be
   unsatisfiable / not actually provable from [12] at Rmax=n (since [12]'s Lemma 1/2 are stated for 60 log n)?
4. Bottom line: classify our situation as (a) the paper is correct and we took a sound-but-unfaithful
   shortcut that should be redone at Rmax=Θ(log n) by citing [12]'s probabilistic reset; (b) the paper has
   a gap we are implicitly fixing; or (c) Rmax=n is actually fine and faithful (the protocol is parameterized
   by Rmax, and the paper's bounds survive Rmax=n). Give the strongest argument for your classification.
