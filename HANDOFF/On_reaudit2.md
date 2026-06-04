# Re-audit ROUND 2: fixed PEM_expectedParallelTime_On / _explicit at commit e8c864c

Prior round (you) found 2 holes in PEM_expectedParallelTime_On: (1) h12ranking/h12reRank vacuity (targets
needed MedianTimerAtLeast 35, unsatisfiable from silent InSem configs); (2) p_reset not uniform. They were
FIXED: targets now have OR IsConsensusConfig escape; new theorem PEM_expectedParallelTime_On_explicit concludes
<= PEM_On_explicit_linearConstant * n (explicit K*n). Re-audit the FIXED version adversarially.

Questions (default stance: still has a hole):
1. Did the OR IsConsensusConfig escape make h12ranking/h12reRank GENUINELY satisfiable AND keep the renewal
   composition SOUND+FAITHFUL? Specifically: does the renewal correctly treat "hit IsConsensusConfig" as done
   vs "hit InSrank-and-timer" as continue? Could the escape let a non-progress config trivially satisfy and
   break the time bound? Is reaching the OR-target still O(n^2)-expected and faithfully [12]-derivable?
2. PEM_expectedParallelTime_On_explicit: is the bound GENUINELY <= K*n with K a constant independent of n?
   Check PEM_On_explicit_linearConstant is constant in the window constants (not secretly n-dependent), and that
   p_reset was pinned to an absolute constant (no residual 1/p_reset with p_reset shrinking in n).
3. Any NEW hole introduced by the fix? Any remaining unsatisfiable/over-strong hypothesis? Re-scan ALL hypotheses
   of both theorems for satisfiability+faithfulness.
Classify: GENUINE non-vacuous explicit O(n), or STILL-HAS-HOLE (file:line). READ-ONLY, do not edit, do not lake build.
