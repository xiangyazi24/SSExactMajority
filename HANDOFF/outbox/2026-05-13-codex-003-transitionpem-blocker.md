# Codex -> Zinan (outbox/2026-05-13-codex-003)

Sender: Codex (GPT-5.5)
Receiver: Zinan
Topic: inbox 003 transitionPEM Phase 4 helper still blocked

## Status

I read inbox 003 and took the `BurmanProof.lean` lock while working. I did not
commit any Lean code in this round, because every attempted `transitionPEM`
helper either timed out or hit `simp` max-steps.

The lock was removed before this outbox.

## Attempt 1: focused both-Settled helper

Target:

```lean
transitionPEM_both_rankDelta_settled_role_stays_settled_or_resetting
```

I tried the exact shape from the inbox:

```lean
generalize hrd : rankDelta (s₀, s₁) = rd at h_both ⊢
obtain ⟨r₀, r₁⟩ := rd
obtain ⟨hr₀, hr₁⟩ := h_both
unfold transitionPEM
rw [hrd]
...
```

`rw [hrd]` does not see the `rankDelta (s₀, s₁)` occurrence after unfolding in
my stdin reproduction. Moving `rw [hrd]` before `unfold transitionPEM` also does
not work because the occurrence is hidden inside the opaque `transitionPEM`.

Replacing `rw [hrd]` with:

```lean
simp only [hrd, hr₀, hr₁, AgentState.role_with_answer,
  AgentState.role_with_timer, ...]
```

hits whnf timeout at default heartbeat. With `maxHeartbeats 20000000`, it still
ran for two minutes with no output, and I killed it.

## Attempt 2: smaller reset-role wrapper

Target:

```lean
theorem transitionPEM_second_rankDelta_resetting_role
    (h : (rankDelta (s₀, s₁)).2.role = .Resetting) :
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).2.role = .Resetting
```

This would directly discharge `propagate_reset_one_step` after
`rankDeltaOSSR_propagate_reset`.

The same pattern:

```lean
generalize hrd : rankDelta (s₀, s₁) = rd at h
obtain ⟨r₀, r₁⟩ := rd
unfold transitionPEM
simp only [hrd, h, AgentState.role_with_answer, AgentState.role_with_timer, ...]
split_ifs <;> simp_all
```

times out at default heartbeat. With `maxHeartbeats 16000000`, it reaches
`simp` max-steps.

## Diagnosis

The hard part is not the number of Phase 4 cases. It is getting Lean to rewrite
or reduce the `rankDelta` call under `transitionPEM` without unfolding the whole
nested Algorithm 1 term into a massive expression.

The existing `transitionPEM_structural_passthrough` in the file uses the same
`generalize ...; unfold transitionPEM; rw [hrd]` pattern, but I could not
reproduce that pattern in stdin for either a role-only focused helper or an
errorcount sibling. It may depend on exact local elaboration context, or that
the existing theorem has not been reached in a fresh successful build since the
current cascade started.

## Suggested next move

I would not keep trying to prove new transitionPEM helpers by unfolding
`transitionPEM` directly.

Better options:

1. Move reusable transition-shape lemmas into `Protocol/Transition.lean`, close
   to the definition, and prove them with private local abbreviations for each
   phase (`rankDelta`, clear-answer, median-timer, epidemic, phase4). This may
   make rewrite points explicit before the term explodes.

2. Refactor `transitionPEM` itself into named phase functions. Then phase lemmas
   become small definitional equalities instead of one large nested `let`.

3. For the current compile-cascade objective, leave
   `transitionPEM_unsettled_one_step_progress` as the localized `sorry` from
   outbox 001 and continue with the processAgent-refactor fallout below it.

No Lean/lake process is left running.

— Codex
