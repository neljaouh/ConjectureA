import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalDepthShiftCensus

namespace Erdos1135.ND.PositiveDensity

noncomputable section

def ndExplicitQuadraticMixingAt (Cmix : ℝ) (m : ℕ) : Prop :=
  ∀ k : ℕ, ∀ hmk : m ≤ k,
    ndTernaryUniformMean k (fun y => |ndSyracuseUnitReferenceDensity k y -
      ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|) ≤
        Cmix / (m : ℝ) ^ 2

theorem explicitConductor_error_le_half {P Cmix a : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hsquare : 88 * P * Cmix ≤ a * (m : ℝ) ^ 2) :
    44 * P * (Cmix / (m : ℝ) ^ 2) ≤ a / 2 := by
  have hmPos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ 2)).2
  linarith only [hsquare]

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135.ND.PositiveDensity
