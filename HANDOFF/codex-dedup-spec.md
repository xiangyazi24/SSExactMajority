# Codex task (uisai1): fix pre-existing duplicate blocking full-repo build (audit blocker)

The FULL `lake build` (needed for audit / #print axioms across the repo) fails:
`SSExactMajority.lean: import ... BurmanProperties failed, environment already contains
'SSEM.P_EM_solves_SSEM_concrete' from ... Final`. P_EM_solves_SSEM_concrete is defined as a `theorem`
in BOTH Convergence/Final.lean:141 AND Convergence/BurmanProperties.lean:338, and the root import
closure pulls in both → name clash. PRE-EXISTING (since b252f05), in the correctness proof, NOT the
time-bound work — but it must be fixed for the repo to fully build (audit).

## TASK
1. Determine the relationship: are the two P_EM_solves_SSEM_concrete theorems the same statement, or
   different? (Final.lean's is the "concrete instantiation" end result; BurmanProperties.lean's is
   described as "concrete instantiation with rankDeltaStable".)
2. Fix the clash MINIMALLY without weakening either: e.g. RENAME the BurmanProperties one (e.g.
   P_EM_solves_SSEM_concrete_burman) and update its few call sites, OR if one is strictly redundant,
   remove it and redirect references. Prefer rename (safest). Do NOT delete a genuinely-used theorem.
3. Verify the FULL repo builds: `lake build` (no target) must succeed (modulo the long DrainProductive
   olean — that is fine, let it build). Confirm no other duplicate clashes.

## HARD RULES (automode, no effort cap)
- NO sorry/axiom/native_decide introduced. Do NOT weaken statements. Verify via full `lake build`.
  Commit [Xiang-proxy] + push if the full build succeeds. Report precisely.
  Append to HANDOFF/outbox/codex-dedup-report.md.
