import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricBalancedCrossingAffineDensity
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricFirstCrossingOvershootRate
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricOutwardBaseGrowth

namespace Erdos1135

namespace ND

namespace PositiveDensity

open scoped BigOperators

noncomputable section

universe u

structure NDGeom2ShiftedWideSymmetricRegenerativeState where
  Label : Type u
  [labelFintype : Fintype Label]
  root : Label → ℕ
  base : Label → ℕ
  outerWeight : Label → ℝ
  weight_nonneg : ∀ i, 0 ≤ outerWeight i
  root_odd : ∀ i, Odd (root i)
  base_eq : ∀ i, base i = ndA5QOneRootDyadicBase (root i)
  base_twoHundred : ∀ i, 200 ≤ base i

theorem NDGeom2ShiftedWideSymmetricRegenerativeState.rootLower
    (S : NDGeom2ShiftedWideSymmetricRegenerativeState)
    (i : S.Label) :
    16 ^ S.base i ≤ S.root i := by
  rw [S.base_eq i]
  exact (rootDyadicBase_bounds (Odd.pos (S.root_odd i))).1

noncomputable def NDGeom2ShiftedWideSymmetricRegenerativeState.denominator
    (S : NDGeom2ShiftedWideSymmetricRegenerativeState) : ℝ := by
  letI := S.labelFintype
  exact ndGeom2PredictableOuterDenominator
    (Finset.univ : Finset S.Label) S.outerWeight

end

end PositiveDensity

end ND

end Erdos1135
