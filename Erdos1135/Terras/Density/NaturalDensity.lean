import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Order.Basic

namespace Erdos1135

namespace Terras

open Filter

open scoped Topology

theorem nat_count_eq_count_classical (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    @Nat.count p (fun n => Classical.propDecidable (p n)) N = Nat.count p N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.count_succ, Nat.count_succ, ih]
      by_cases h : p N <;> simp [h]

noncomputable def natCount (s : Set ℕ) (N : ℕ) : ℕ :=
  @Nat.count (fun n => n ∈ s) (fun n => Classical.propDecidable (n ∈ s)) N

theorem natCount_eq_count (s : Set ℕ) (N : ℕ) [DecidablePred (fun n => n ∈ s)] :
    natCount s N = N.count (fun n => n ∈ s) := by
  exact nat_count_eq_count_classical (fun n => n ∈ s) N

theorem natCount_mono {s t : Set ℕ} (hsub : s ⊆ t) (N : ℕ) :
    natCount s N ≤ natCount t N := by
  unfold natCount
  exact @Nat.count_mono_left (fun n => n ∈ s) (fun n => Classical.propDecidable (n ∈ s))
    (fun n => n ∈ t) (fun n => Classical.propDecidable (n ∈ t)) N
    (fun _k _hk hks => hsub hks)

end Terras

end Erdos1135
