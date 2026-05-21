Here is the next `sorry` in `SSExactMajority/Convergence/BurmanProof.lean`. It is about Phase 3a, reducing the resetcount and delaytimers to 0 for Resetting agents.

```lean
/-- Phase 3a: countdown delaytimers to 0 for all Resetting agents. -/
theorem phase3a_to_awakening
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hLeader : ∃ ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      IsAwakeningConfig (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  sorry

/-! ### Awakening step helpers

When all agents are dormant (Resetting, rc=0, dt=0), scheduling the leader
with any follower fires resetOSSR on both: leader → Settled(rank 0),
follower → Unsettled. After the first step, scheduling the now-Settled root
with remaining dormant followers converts them to Unsettled one by one. -/

set_option maxHeartbeats 64000000 in
/-- RankDeltaOSSR on two dormant agents (leader + follower): both fire resetOSSR. -/
theorem rankDeltaOSSR_both_dormant
```

Please generate the replacement block for `phase3a_to_awakening`. Let me know if you need to see `IsAwakeningConfig` or other helpers. Note that `IsAwakeningConfig` is likely defined above as:
```lean
def IsAwakeningConfig (C : Config (AgentState n) Opinion n) : Prop :=
  (∃ ℓ : Fin n, (C ℓ).1.role = .Settled ∧ (C ℓ).1.rank = ⟨0, hn⟩ ∧ (C ℓ).1.leader = .L) ∧
  (∀ w, (C w).1.leader = .F → (C w).1.role = .Unsettled)
```
Wait, the comment says: "countdown delaytimers to 0 for all Resetting agents." It might just be two induction sweeps (one for resetcount, one for delaytimer), then finally we can use `rankDeltaOSSR_both_dormant` on the unique leader.

Wait, if you look at the previous dialogue, ChatGPT mentioned:
```
leanlemma countdown_to_dormant (P) (C : Config P) ...
  -- schedule resetcount countdown to 0,
  -- then dormant timer countdown to 0,
  -- then leader awakens to Settled rank 0, followers to Unsettled
  sorry
```
Please provide the Lean 4 proof for `phase3a_to_awakening`. If it's too long, you can break it into smaller lemmas or give me the high-level steps first.