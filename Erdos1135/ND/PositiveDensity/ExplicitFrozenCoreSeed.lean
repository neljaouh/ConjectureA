import Erdos1135.ND.PositiveDensity.ExplicitTerminalVariation
import Erdos1135.ND.PositiveDensity.ExplicitVariationBudgets
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalDepthShiftMarkedLoss

namespace Erdos1135.ND.PositiveDensity

noncomputable section

def explicitSeedFloor (b : ℕ) : ℕ → ℕ
  | 0 => b
  | n + 1 => explicitSeedFloor b n + explicitSeedFloor b n / 100

theorem explicitSeedFloor_bounds (b n : ℕ) :
    b ≤ explicitSeedFloor b n ∧ explicitSeedFloor b n ≤ b * 2 ^ n := by
  induction n with
  | zero => simp [explicitSeedFloor]
  | succ n ih =>
    have hd := Nat.div_le_self (explicitSeedFloor b n) 100
    simp only [explicitSeedFloor, pow_succ]
    constructor
    · omega
    · nlinarith [ih.2]

theorem NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.explicit_forward_floor
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    (U.forwardIterate cap n).floor = explicitSeedFloor U.floor n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [U.forwardIterate_succ_eq_next cap n]
    change (U.forwardIterate cap n).floor + (U.forwardIterate cap n).floor / 100 = _
    rw [ih]
    rfl

end

end Erdos1135.ND.PositiveDensity
