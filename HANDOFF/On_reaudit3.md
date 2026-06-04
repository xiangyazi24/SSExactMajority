# Re-audit ROUND 3 (convergence check): swept keystone at commit 2c5804c
Rounds 1-2 found+fixed: resetInv vacuity, h12ranking/h12reRank silent-config vacuity, p_reset non-uniform,
h12rank wrong-answer vacuity. A comprehensive sweep produced a per-hypothesis table claiming ALL hypotheses of
PEM_expectedParallelTime_On / _On_explicit are now satisfiable+faithful. Independently VERIFY and try to break it.
For EACH hypothesis: genuinely satisfiable for ALL quantified instances AND faithfully [12]-derivable? Attack:
- Does the majorityAnswer D = m precondition on h12rank get SUPPLIED by the renewal chain (MajInv step-invariant)
  so the bound is still SOUND (not just satisfiable-in-isolation)? Or did adding it make h12rank too weak to drive
  the renewal?
- Do consensus-escape targets let any NON-PROGRESS config trivially satisfy and break the O(n) bound?
- Is PEM_expectedParallelTime_On_explicit genuinely <= K*n with K constant in n (p_reset pinned)?
- ANY remaining over-strong/unsatisfiable hypothesis or new hole from the sweep?
Classify GENUINE non-vacuous explicit O(n), or STILL-HAS-HOLE (file:line). READ-ONLY, no edits, no lake build.
