# Zinan → Codex (inbox/2026-05-13-zinan-009)

Sender: Zinan
Receiver: Codex
Topic: Fill leader dedup trace + dormant dt decrease (two mechanical traces)

## Two sorry'd traces to fill

Both are `rankDeltaOSSR` traces with hypothesis (both R, both rc=0). Diff is leader combo.

### 1. `rankDeltaOSSR_leader_dedup_step` (line ~709)

NEW. Both L → second becomes F (dedup fires). Structure:

```
unfold rankDeltaOSSR propagateReset
simp only [hs, ht, hs_rc, ht_rc, hs_L, ht_L,
  show ¬(0 < (0:ℕ)) from by omega, show Nat.max 0 0 = 0 from rfl,
  show (Role.Resetting == Role.Resetting) = true from rfl,
  -- dedup condition: both L + both R → true
  true_or, or_true, ite_true, ite_false, false_and, and_false, and_self,
  true_and, and_true, not_false_eq_true, Bool.true_eq_true, Bool.not_true,
  show s.delaytimer - 1 = 0 → False from by omega,
  show t.delaytimer - 1 = 0 → False from by omega]
-- processAgent:  rc=0 + oldRc=0 → dt := dt-1. dt-1 ≠ 0 → stays Resetting.
-- Then dedup: both R + both L → b.leader := .F
exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
```

Try that shape. If simp doesn't close, unfold processAgent too and add the dt simp lemmas from existing proofs.

### 2. `rankDeltaOSSR_dormant_dt_decrease` (line ~695)

EXISTING sorry from codex's mass-sorry pass. Same shape but s.L + t.F (dedup doesn't fire). The OLD proof was:

```
unfold rankDeltaOSSR propagateReset resetOSSR
simp only [hs, ht, hs_rc, ht_rc, hs_L, ht_F,
  show ¬(0 < (0:ℕ)) from by omega, show Nat.max 0 0 = 0 from rfl,
  show (Role.Resetting == Role.Resetting) = true from rfl,
  show ¬(Leader.F = Leader.L) from Leader.noConfusion,
  true_or, or_true, ite_true, ite_false, false_and, and_false, and_self,
  true_and, and_true, not_false_eq_true, Bool.true_eq_true, Bool.not_true,
  show s.delaytimer - 1 = 0 → False from by omega,
  show t.delaytimer - 1 = 0 → False from by omega]
exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
```

This was PROVEN before the processAgent refactor (commit 073f398c). After refactor it may need `unfold processAgent` too. Try restoring the old proof + adding `unfold processAgent` if needed.

## Protocol

- Lock BurmanProof.lean
- 2 attempts each; file blocker if stuck
- outbox + tmux signed ping `Codex: outbox 009 ready` + Enter
- Co-Authored-By tag

— Zinan
