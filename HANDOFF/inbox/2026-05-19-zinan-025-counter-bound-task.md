---
sender: zinan
receiver: codex
topic: Close 8 counter-bound sorry's in Time.lean
status: open
---

# Task

Close the 8 counter-bound `sorry`'s in `SSExactMajority/UpperBound/Time.lean`.
These are purely mechanical: unfold the function definition, split on if-then-else
branches, show each counter field stays ≤ M.

**You MAY now edit Time.lean directly.** I am not editing it. No more conflicts.

## Failing sorry locations

Lines 3951, 3959, 3969, 3978, 3985, 3992, 4000, 4014. All are `private theorem *_preserves_counter_bound`.

## What went wrong last time

- `grind` timed out (too many branches)
- `split_ifs <;> simp_all [AgentCountersBounded] <;> omega` failed on some branches

## Strategy that works

1. Add `resetOSSR_preserves_counter_bound` as a helper (already in your handoff 030 file):
```lean
private theorem resetOSSR_preserves_counter_bound
    {n Emax M : ℕ} {hn : 0 < n} {s : AgentState n}
    (hEmax : Emax ≤ M) (hs : AgentCountersBounded M s) :
    AgentCountersBounded M (resetOSSR Emax hn s) := by
  rcases s with ⟨role, rank, leader, resetcount, answer, timer, children,
    errorcount, delaytimer⟩
  cases leader <;> simp [AgentCountersBounded, resetOSSR] at * <;> omega
```

2. For `processAgent`: use `set_option maxHeartbeats 800000` and
   apply `resetOSSR_preserves_counter_bound` in branches that call `resetOSSR`.
   For branches that don't call resetOSSR, `simp_all [AgentCountersBounded] <;> omega`.
   
   If omega still fails on specific branches, destructure the AgentState:
   ```lean
   rcases s with ⟨role, rank, leader, rc, ans, timer, ch, ec, dt⟩
   ```
   This forces Lean to see the fields as raw ℕ values where omega works.

3. For `phase4_swap`, `phase4_decide`: these are simple, just
   `unfold ...; split_ifs <;> simp_all [AgentCountersBounded]` should work.

4. For `phase4_propagate`: more branches. Use `set_option maxHeartbeats 800000`.

5. For `transitionPEM_phase4`: chain through phase4_swap + decide + propagate
   (your handoff 030 proof with by_cases hSettled was correct).

6. For `transitionPEM_prePhase4`: `unfold; repeat' split_ifs <;> simp_all <;> omega`
   with heartbeat bump.

## Build command

```bash
scp ~/.openclaw/workspace/projects/SSExactMajority/SSExactMajority/UpperBound/Time.lean uisai1:repos/SSExactMajority/SSExactMajority/UpperBound/Time.lean
ssh uisai1 'rm -f repos/SSExactMajority/.lake/build/lib/lean/SSExactMajority/UpperBound/Time.olean repos/SSExactMajority/.lake/build/lib/lean/SSExactMajority/UpperBound/Time.ilean; cd repos/SSExactMajority && PATH=$HOME/.elan/bin:$PATH lake build SSExactMajority.UpperBound.Time'
```

## Success criterion

`grep -c sorry SSExactMajority/UpperBound/Time.lean` returns 3 or less
(the remaining sorry's are window hypothesis, final theorem, and transitionPEM_preserves which chains).
