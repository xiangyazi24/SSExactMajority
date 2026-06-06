import SSExactMajority.Convergence.Sets
import SSExactMajority.Probability.ExpectedTime
import SSExactMajority.Protocol.RankDelta

namespace SSEM

open scoped ENNReal

/-!
Restart-recovery statement for the even-`n` wrong-restart branch.

The earlier broad recovery shape, starting from an arbitrary state with a
Resetting agent, is too weak: unrelated counters, especially `delaytimer`,
can be unbounded.  This statement records the usable post-wrong-restart
contract instead.  The configuration is globally counter-bounded and contains
a fresh leader reset seed with full reset count.

The predicates below mirror the corresponding time-layer predicates without
importing `UpperBound.Time`; this keeps the dependency direction usable for
eventually importing this theorem into `Time.lean`.
-/

def RecoveryBoundedConfig (M : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n,
    (C μ).1.timer ≤ M ∧
    (C μ).1.resetcount ≤ M ∧
    (C μ).1.errorcount ≤ M ∧
    (C μ).1.delaytimer ≤ M ∧
    (C μ).1.children ≤ M

def RecoveryTimerBoundedConfig (K : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n, (C μ).1.timer ≤ K

def RecoveryMedianTimerAtLeast (k : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n,
    (C μ).1.rank.val + 1 = ceilHalf n →
      k ≤ (C μ).1.timer

theorem wrong_restart_to_InSswap_timer_bound
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmaxN : n ≤ Dmax)
    (hDmax_le_Rmax : Dmax ≤ 2 * Rmax)
    (D : Config (AgentState n) Opinion n)
    (hBounded :
      RecoveryBoundedConfig (max Rmax (max Dmax (7 * (Rmax + 4)))) D)
    (hAllRcFull :
      ∀ w : Fin n,
        (D w).1.role = .Resetting →
          (D w).1.resetcount = Rmax ∧ (D w).1.leader = .L)
    (hSomeR : ∃ r : Fin n, (D r).1.role = .Resetting) :
    Probability.expectedHittingTime
      (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0))
      (by exact Nat.le_trans (by decide : 2 ≤ 4) hn4 : 2 ≤ n) D
      (fun C =>
        IsConsensusConfig C ∨
          (InSswap C ∧
            RecoveryMedianTimerAtLeast 1 C ∧
            RecoveryTimerBoundedConfig (7 * (Rmax + 4)) C)) ≤
      ((8 * Rmax * n * n : ℕ) : ENNReal) := by
  sorry

end SSEM
