# codex-entry report

## 2026-06-04

Status: PROVED first-subgoal witness; BLOCKED for reducing entry to rc-level alone.

Touched only:
- `SSExactMajority/UpperBound/Time/EntryBound.lean`
- `HANDOFF/outbox/codex-entry-report.md`

Self-check:
- `lake env lean SSExactMajority/UpperBound/Time/EntryBound.lean` passed.

Progress measure identified:
- Phase 3a dormant -> awakening is not controlled by `rcLevelPotential` after `rc=0`; it is controlled by delaytimer progress. Existing nearby measure: `followerDormantMeasure` in `BurmanProof.lean`, with per-step lemmas for dormant follower delaytimer/wake progress. The qualitative `phase3a_to_awakening` uses a fixed leader/follower pair and strong induction on the leader delaytimer.
- Phase 3bc awakening -> FreshRankingStart is controlled by
  `(awakeningResettingFollowers C).card`.

Formal facts added:
- `rcLevelPotential_eq_zero_of_awakening`:
  `IsAwakeningConfig C -> rcLevelPotential C = 0`.
- `freshRankingStart_iff_awakeningResettingFollowers_card_zero_of_awakening`:
  under `IsAwakeningConfig`, `FreshRankingStart C` iff the awakening resetting-follower set has card `0`.
- `awakening_step_descent_witness`:
  if `IsAwakeningConfig C` and `(awakeningResettingFollowers C).card > 0`, then there is an ordered pair `(root,w)` such that one PEM step preserves `IsAwakeningConfig` and strictly decreases the card.
- `awakening_step_descent_prob`:
  the deterministic witness gives one-step hit probability at least
  `((n * (n - 1) : Nat) : ENNReal)⁻¹` for
  `FreshRankingStart ∨ (IsAwakeningConfig ∧ smaller card)`.

Exact obstruction to the proposed rc-level reduction:
- `rcLevelPotential = 0 + IsAwakeningConfig` does not imply `FreshRankingStart`.
  In fact, `IsAwakeningConfig` already implies `rcLevelPotential = 0`; the rc-level potential ignores dormant followers with `resetcount=0`, while `IsAwakeningConfig` explicitly permits followers still in
  `Resetting ∧ resetcount=0`.
- The missing information is exactly absence of resetting followers, captured by
  `(awakeningResettingFollowers C).card = 0`.

Closest existing machinery:
- `RecoveryBound.lean`: `rcLevelPotential_*` handles resetcount drain to rc-level zero.
- `BurmanProof.lean`: `phase3bc_from_awakening` already contains the same card-decrease induction now factored as a one-step witness; `followerDormantMeasure` is the closest existing delaytimer measure for the dormant/follower part.
