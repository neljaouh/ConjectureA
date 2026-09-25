import Mathlib.Tactic

namespace Erdos1135

namespace Tao

open scoped BigOperators

noncomputable section

def taoSection7IntIccWindow (R : ℕ) (c : ℤ) : Finset ℤ :=
  Finset.Icc (c - (R : ℤ)) (c + (R : ℤ))

theorem mem_taoSection7IntIccWindow {R : ℕ} {c x : ℤ} :
    x ∈ taoSection7IntIccWindow R c ↔ c - (R : ℤ) ≤ x ∧ x ≤ c + (R : ℤ) := by
  simp [taoSection7IntIccWindow]

end

end Tao

end Erdos1135
