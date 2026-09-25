import Erdos1135.Tao.Syracuse.Basic

namespace Erdos1135

namespace ND

namespace PositiveDensity

def ndA5PreviousPhysicalCollapseSource : ℕ → ℕ
  | 0 => 0
  | m + 1 => 4 * ndA5PreviousPhysicalCollapseSource m + 1

@[simp] theorem ndA5PreviousPhysicalCollapseSource_succ (m : ℕ) :
    ndA5PreviousPhysicalCollapseSource (m + 1) =
      4 * ndA5PreviousPhysicalCollapseSource m + 1 := rfl

theorem three_mul_ndA5PreviousPhysicalCollapseSource_add_one (m : ℕ) :
    3 * ndA5PreviousPhysicalCollapseSource m + 1 = 4 ^ m := by
  induction m with
  | zero => norm_num [ndA5PreviousPhysicalCollapseSource]
  | succ m ih =>
      rw [ndA5PreviousPhysicalCollapseSource_succ, pow_succ]
      omega

theorem ndA5PreviousPhysicalCollapseSource_odd (m : ℕ) :
    Odd (ndA5PreviousPhysicalCollapseSource (m + 1)) := by
  refine ⟨2 * ndA5PreviousPhysicalCollapseSource m, ?_⟩
  rw [ndA5PreviousPhysicalCollapseSource_succ]
  omega

theorem syracuse_ndA5PreviousPhysicalCollapseSource_succ (m : ℕ) :
    Tao.syracuse (ndA5PreviousPhysicalCollapseSource (m + 1)) = 1 := by
  rw [Tao.syracuse_eq_ordCompl_two]
  rw [three_mul_ndA5PreviousPhysicalCollapseSource_add_one]
  rw [show (4 : ℕ) ^ (m + 1) = 2 ^ (2 * (m + 1)) by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]]
  exact Nat.ordCompl_self_pow Nat.prime_two

end PositiveDensity

end ND

end Erdos1135
