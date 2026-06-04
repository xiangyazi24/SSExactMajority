# Codex task (uisai1): OW_rankBound under (A) — cite [12] ranking time (should be straightforward)

OW_rankBound (OptimalWindows.lean, currently `sorry`): from any timer-bounded config, E[T to ranked
endpoint (InSrank ∧ MedianTimerAtLeast 35 ∧ bounded)] ≤ Rmax·n². Under scope (A), this IS [12]'s
Optimal-Silent-SSR ranking time (Lemma 3) — CITE it as an explicit hypothesis, don't re-derive.

## Restate OW_rankBound to take the [12] ranking-time hypothesis
```
theorem OW_rankBound (hn4 : 4 ≤ n) (hRmax ...) 
  (h12ranking :  -- [12] Lemma 3 (Theorem 4.3 of [12]): Optimal-Silent-SSR stabilizes to a ranked
                 -- endpoint in expected ≤ Rmax·n² (= O(n) parallel, srank ≤ trank·n)
    ∀ C, IsTimerBoundedConfig (7*(Rmax+4)) C →
      expectedHittingTime P hn C (fun D => InSrank D ∧ MedianTimerAtLeast 35 D ∧
        IsTimerBoundedConfig (7*(Rmax+4)) D) ≤ ((Rmax*n*n:ℕ):ENNReal)) :
  <same conclusion> := h12ranking   -- the citation IS the bound
```
i.e. OW_rankBound becomes a direct consequence of the cited [12] hypothesis. Replace the `sorry` with
this. Keep the conclusion EXACTLY as currently stated. The whole point: [12]'s ranking time is not
Kanaya's contribution, so under (A) it is a cited premise (faithful to how the paper uses Lemma 3).

## Also update PEM_expectedParallelTime_optimal
to thread h12ranking through (it already threads hRank12; add h12ranking similarly so the final
theorem cites [12]'s ranking + the consensus keystone's [12] hypotheses).

## HARD RULES (automode)
- h12ranking = explicit [12] citation (hypothesis), NOT sorry/axiom. NO sorry/axiom/native_decide left.
  Edit OptimalWindows.lean. Self-verify lake env lean. NEVER lake build. Append to HANDOFF/outbox/codex-rankA-report.md.
