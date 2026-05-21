Yes: do not unfold everything in the main theorem. Use small “trace API” lemmas, then the main 4 sorries become orchestration.
1. unsettled_one_step_progress
Cleanest structure:
leanlemma unsettled_rankDelta_trace    (P) (C : Config P) (w v : Agent)    (hw : (C w).role = Role.Unsettled)    (hNoReset : ∀ a, (C a).role ≠ Role.Resetting) :    let C' := rankDeltaOSSR P C w v    (C' w).role = Role.Settled ∨    (C' w).role = Role.Resetting ∨    potential C' < potential C := by  -- unfold only rankDeltaOSSR here  unfold rankDeltaOSSR  simp [hw, hNoReset]  split_ifs <;> simp_all <;> omega
Then handle PEM separately:
leanlemma transitionPEM_preserves_or_resets_or_decreases    (P) (C C' : Config P)    (h : C' = transitionPEM P C) :    IsResetConfig C' ∨ potential C' ≤ potential C := by  subst h  unfold transitionPEM  split_ifs <;> simp_all <;> omega
Then the target should become:
leanlemma unsettled_one_step_progress ... := by  let C₁ := rankDeltaOSSR P C w v  have hrd := unsettled_rankDelta_trace P C w v hw hNoReset  let C₂ := transitionPEM P C₁ w v  rcases hrd with hsettled | hreset | hdec  · -- recruitment succeeded; PEM phase 4 either does nothing or resets/decreases    have hpem :=      transitionPEM_preserves_or_resets_or_decreases P C₁ C₂ rfl    rcases hpem with hR | hle    · exact Or.inl hR    · exact Or.inr (lt_of_le_of_lt hle hdec_or_recruit_measure)  · -- already resetting    exact Or.inl ...  · -- rankDelta already decreased    have hpem :=      transitionPEM_preserves_or_resets_or_decreases P C₁ C₂ rfl    exact ...
The main theorem should not know the internal branch conditions of recruitment/errorcount. It should only consume:
leanrankDelta gives: reset ∨ recruited ∨ measure decreasestransitionPEM gives: reset ∨ measure nonincreases
That is the robust Lean design.

2. phase3a_to_awakening
Use these two API lemmas:
leanlemma positive_reset_window    (P) (C : Config P)    (hAll : ∀ a, (C a).role = Role.Resetting)    (hLeader : ∃ a, (C a).isLeader = true)    (hRpos : 0 < P.Rmax) :    ∃ t γ C',      C' = execution P C γ t ∧      (∀ a, (C' a).role = Role.Resetting) ∧      UniqueLeader C' ∧      ∀ a, (C' a).resetcount ≤ P.Rmax := by  -- schedule leader-vs-leader cleanup / max-resetcount synchronization  sorry
leanlemma countdown_to_dormant    (P) (C : Config P)    (hAll : ∀ a, (C a).role = Role.Resetting)    (hUnique : UniqueLeader C)    (hRpos : 0 < P.Rmax)    (hDpos : 0 < P.Dmax) :    ∃ t γ C',      C' = execution P C γ t ∧      IsAwakeningConfig P C' := by  -- schedule resetcount countdown to 0,  -- then dormant timer countdown to 0,  -- then leader awakens to Settled rank 0, followers to Unsettled  sorry
Then:
leanlemma phase3a_to_awakening    (P) (C : Config P)    (hAll : ∀ a, (C a).role = Role.Resetting)    (hLeader : ∃ a, (C a).isLeader = true)    (hRpos : 0 < P.Rmax)    (hDpos : 0 < P.Dmax) :    ∃ t γ, IsAwakeningConfig P (execution P C γ t) := by  rcases positive_reset_window P C hAll hLeader hRpos with    ⟨t₁, γ₁, C₁, hC₁, hAll₁, hUnique₁, hBound₁⟩  rcases countdown_to_dormant P C₁ hAll₁ hUnique₁ hRpos hDpos with    ⟨t₂, γ₂, C₂, hC₂, hAwake⟩  refine ⟨t₁ + t₂, concatSchedule γ₁ γ₂, ?_⟩  -- rewrite execution concatenation  simpa [execution_append, hC₁, hC₂] using hAwake

3. heapPrefix_recruit_step
Your timer reasoning is correct if Phase 4 decrements only when the two agents are both settled and one has max-rank/median-trigger condition. During heap construction, max rank n-1 first appears at the final recruitment step, so for k < n-1 no decrement; at k = n-1, one decrement from ≥ 56 is still ≥ 3.
Add this lemma:
leanlemma medianTimerStrong_after_recruit    (P) (C C' : Config P) (k : ℕ)    (hHP : HeapPrefix P C k)    (hStrong : SettledMedianTimerStrong P C)    (hInit : ∀ a, (C a).timer ≥ 7 * (P.Rmax + 4))    (hstep : C' = recruitStep P C k)    (hk : k < P.n) :    SettledMedianTimerStrong P C' := by  subst C'  unfold recruitStep transitionPEM rankDeltaOSSR  -- cases:  -- 1. k < n-1: max-rank absent, so phase 4 condition false  -- 2. k = n-1: timer decrements once, lower bound still ≥ 3  by_cases hlast : k + 1 = P.n  · -- final recruitment    intro a ha    specialize hStrong a ?_    omega  · -- non-final recruitment    simp [hlast] at *    exact hStrong
For Phase 4 not triggering reset, isolate:
leanlemma no_phase4_reset_during_recruit    (P) (C : Config P) (k : ℕ)    (hHP : HeapPrefix P C k)    (hStrong : SettledMedianTimerStrong P C)    (hk : k < P.n) :    ¬ Phase4ResetCondition P (rankDeltaOSSR P C parent child) := by  -- Either not both final settled-with-expired-timer,  -- or timer ≥ 3 prevents errorcount hitting zero.  intro h  have ht := hStrong ...  omega
Then rebuild the five HeapPrefix fields separately:
leanlemma heapPrefix_recruit_step ... :    HeapPrefix P C' (k+1) := by  constructor  · -- field 1: settled prefix grows    intro a ha    by_cases haold : a.rank < k    · exact old_settled_field ...    · -- new child      simp [recruitStep, rankDeltaOSSR, haold, ha]  constructor  · -- field 2: ranks unique in prefix    intro a b ha hb hr    -- old-old by previous uniqueness;    -- old-new impossible by fresh rank;    -- new-new trivial    omega  constructor  · -- field 3: parent/child heap relation    -- new child rank = 2*parent+childIdx+1    simp [rankDeltaOSSR]  constructor  · -- field 4: outsiders unsettled/reset-free    intro a ha    simp [recruitStep, rankDeltaOSSR, ha]  · -- field 5: median timer strong    exact medianTimerStrong_after_recruit P C C' k hHP hStrong hInit rfl hk
The important trick: do not prove “Phase 4 does nothing.” Prove the weaker thing you need: Phase 4 does not cause reset and preserves SettledMedianTimerStrong.

4. burmanConvergence_concrete
Strengthen phase 1. Do not patch this in the final theorem.
Use:
leanstructure Phase1Output (P) (C : Config P) : Prop where  existsResetting : ∃ a, (C a).role = Role.Resetting  resetcount_eq_Rmax :    ∀ a, (C a).role = Role.Resetting → (C a).resetcount = P.Rmax
Then:
leanlemma phase1_to_resetting_strong ... :    ∃ t γ C',      C' = execution P C γ t ∧      Phase1Output P C' := by  ...
For phase 2:
leanstructure Phase2Output (P) (C : Config P) : Prop where  allResetting : ∀ a, (C a).role = Role.Resetting  leaderExists : ∃ a, (C a).isLeader = true
Then:
leanlemma phase2_to_all_resetting_strong    (P) (C : Config P)    (h : Phase1Output P C)    (hn : P.n ≤ P.Rmax) :    ∃ t γ C',      C' = execution P C γ t ∧      Phase2Output P C' := by  -- use h.resetcount_eq_Rmax to satisfy old n ≤ rc API  ...
Then final threading is clean:
leanlemma burmanConvergence_concrete ... := by  rcases phase1_to_resetting_strong P C₀ ... with    ⟨t₁, γ₁, C₁, hC₁, hP1⟩  rcases phase2_to_all_resetting_strong P C₁ hP1 hnRmax with    ⟨t₂, γ₂, C₂, hC₂, hP2⟩  rcases phase3a_to_awakening P C₂      hP2.allResetting hP2.leaderExists hRpos hDpos with    ⟨t₃, γ₃, hAwake⟩  -- continue heap construction  refine ⟨t₁ + t₂ + t₃ + ..., concatSchedule4 γ₁ γ₂ γ₃ ..., ?_⟩  simpa [execution_append_assoc, hC₁, hC₂] using ...
So: yes, strengthen phase 1 and phase 2 outputs. That is cleaner than adding ad-hoc API lemmas later.
