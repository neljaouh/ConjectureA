import ThreeXMinusOne.ShellIncidence
import ThreeXMinusOne.UnitChildExt

/-!
# The `3x−1` source tariff

`Geom2ShiftedWideSymmetricRootSideUniformFloorTerminalSourceTariff`, mirrored.

Two-sided bounds on how far a child root can be from its parent root, in the uniform-floor case.
These are what the window layer runs on: the lower bound keeps the generational family from
collapsing, the upper bound keeps it from outrunning the interval.

Every one of the four reduces to `ShellIncidence.sourceM_shell` by cancelling the common factor
`2 ^ r`, `r = ndGeom2ShiftedWideSymmetricShiftRadius b`, so this file has no new content beyond
Layer 13 — it is the shell, divided through.

**The one constant that moves.**  The lower bound is the `+1` lower bound unchanged.  The upper
bound is `2 ^ (K + 2)` where `+1` has `2 ^ (K + 1)`: the minus shell's upper constant is
`4 · 2 ^ K` rather than `2 · 2 ^ K`, so the source window is twice as wide and nothing else
differs.  That factor of two is the same one that took the count's window constant from
`32 X` to `64 X` at Layer 13, and it is tracked, not absorbed.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

variable {Label : Type*} {Labels : Finset Label} {root : Label → ℕ} {b K : ℕ}

/-- **Lower tariff, physical form.**  A child root cannot be much smaller than its parent. -/
theorem fourPow_mul_root_le_four_mul_threePow_mul_sourceM
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b) (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (z : IncidenceM Label root (fun _ => b) (fun _ => ndGeom2ShiftedWideSymmetricShiftRadius b) K) :
    4 ^ b * root (labelM z) ≤ 4 * 3 ^ b * sourceM z := by
  have hshell := sourceM_shell hrootOdd (fun _ => hb) hrootLower z
  have hscaled :
      2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * (4 ^ b * root (labelM z)) ≤
        2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * (4 * 3 ^ b * sourceM z) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hshell.1
  exact Nat.le_of_mul_le_mul_left hscaled (by positivity)

/-- **Upper tariff, physical form.**  A child root cannot be much larger than its parent.
`2 ^ (K + 2)`, against `+1`'s `2 ^ (K + 1)`. -/
theorem threePow_mul_sourceM_le_twoPow_capTwo_mul_fourPow_mul_root
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b) (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (z : IncidenceM Label root (fun _ => b) (fun _ => ndGeom2ShiftedWideSymmetricShiftRadius b) K) :
    3 ^ b * sourceM z ≤ 2 ^ (K + 2) * 4 ^ b * root (labelM z) := by
  have hshell := sourceM_shell hrootOdd (fun _ => hb) hrootLower z
  have hscaled :
      2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * (3 ^ b * sourceM z) ≤
        2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b *
          (2 ^ (K + 2) * 4 ^ b * root (labelM z)) := by
    simpa only [pow_add, pow_one, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hshell.2
  exact Nat.le_of_mul_le_mul_left hscaled (by positivity)

/-- **Lower tariff at a unit child.** -/
theorem fourPow_mul_parent_le_four_mul_threePow_mul_ucSourceM
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b) (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (z : UnitChildIncidenceM Labels root b (ndGeom2ShiftedWideSymmetricShiftRadius b) K) :
    4 ^ b * root (ucLabelM z) ≤ 4 * 3 ^ b * ucSourceM z := by
  simpa only [toPhysicalM_label, ucSourceM] using
    fourPow_mul_root_le_four_mul_threePow_mul_sourceM hrootOdd hb hrootLower (toPhysicalM z)

/-- **Upper tariff at a unit child.** -/
theorem threePow_mul_ucSourceM_le_twoPow_capTwo_mul_fourPow_mul_parent
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b) (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (z : UnitChildIncidenceM Labels root b (ndGeom2ShiftedWideSymmetricShiftRadius b) K) :
    3 ^ b * ucSourceM z ≤ 2 ^ (K + 2) * 4 ^ b * root (ucLabelM z) := by
  simpa only [toPhysicalM_label, ucSourceM] using
    threePow_mul_sourceM_le_twoPow_capTwo_mul_fourPow_mul_root hrootOdd hb hrootLower
      (toPhysicalM z)

end

end ThreeXMinusOne
