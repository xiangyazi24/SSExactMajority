# Structural fix: WellFormed step-invariant precondition to close the pathological-config class

Round-3 re-audit hole: cited windows (h12ranking, h12reRank, h12rank, resetReach) quantify over configs with
only a TIMER bound, but AgentState has UNBOUNDED ℕ counter fields (resetcount, errorcount, delaytimer). A config
with huge resetcount is timer-bounded but cannot reach InSswap/consensus in O(n²) => windows unsatisfiable for it
(such configs are unreachable in the real protocol, but the hypotheses quantify over ALL configs). This is the
SAME class as the earlier holes (over-strong universal quantification over pathological/unreachable configs).

## Fix (structural — close the whole class at once)
1. Define WellFormed (n Rmax Emax Dmax) C := IsTimerBoundedConfig (PEM_trank1_timer / 35) C ∧ counter-bounded,
   where counter-bounded = (∀ v, (C v).resetcount ≤ Rmax) ∧ (∀ v, (C v).errorcount ≤ Emax) ∧
   (∀ v, (C v).delaytimer ≤ Dmax) — include exactly the unbounded-ℕ fields the windows need (determine minimal set;
   resetcount≤Rmax is definitely required; add errorcount/delaytimer bounds if a window needs them).
2. Prove WellFormed is a STEP-INVARIANT: WellFormed C → ∀ i j, WellFormed (C.step (PEMProtocol n trank Rmax …) i j).
   The protocol sets each counter to ≤ its max and decrements, so bounds are preserved (analogous to
   generic_timer_preservation, which already handles the timer field).
3. Add WellFormed as a PRECONDITION to the cited window hypotheses (h12ranking, h12reRank, h12rank, resetReach):
   each window only asserted for WellFormed C. Now satisfiable+faithful ([12] windows hold for well-formed
   reachable configs; pathological huge-counter configs no longer demanded).
4. THREAD WellFormed through the renewal exactly like MajInv was threaded (define it as a renewal invariant,
   prove step-preservation, strengthen the hit-targets / use expectedParallelTime_le_window_mul_inv_of_invariant
   with Inv := WellFormed ∧ (existing invariants)). The final window calls invoke the cited windows only at
   WellFormed configs.
5. Keystone: assume WellFormed C₀ for the initial config (faithful — the protocol starts well-formed; the
   paper assumes counters in range). PEM_expectedParallelTime_On / _On_explicit take WellFormed C₀ as a hypothesis
   (a shape-only, satisfiable domain assumption — like hRmax).

## Verify
Full lake build, forbidden-token scan. Report to HANDOFF/outbox/cxreset-report.md: WellFormed defined + proven
step-invariant + threaded; updated per-hypothesis table showing every cited window now has WellFormed precondition
and is satisfiable. HARD: no sorry/axiom; do not weaken the O(n) conclusion; WellFormed C₀ is acceptable as a
domain hypothesis but the cited windows must be satisfiable UNDER WellFormed. If blocked write ### BLOCKER.
