import Erdos1135.ND.PositiveDensity.ExplicitExactSeedConductor
import Erdos1135.ND.PositiveDensity.ExplicitLogarithmicConductorRoom
import Erdos1135.ND.PositiveDensity.ExplicitLogarithmicFrozenSeed
import Erdos1135.ND.PositiveDensity.ExplicitOnePeriodSuccessfulRoot
import Erdos1135.ND.PositiveDensity.ExplicitPositiveDensityPair
import Erdos1135.ND.PositiveDensity.ExplicitSeedToCount
import Erdos1135.ND.PositiveDensity.ExplicitSixthRootSeedToCount

namespace Erdos1135.ND.PositiveDensity

noncomputable section

theorem explicitBackwardConductor_ge (b k n : ℕ) :
    k ≤ ndRootCoreBackwardConductor b k n := by
  induction n generalizing b with
  | zero => simp [ndRootCoreBackwardConductor]
  | succ n ih =>
    have h := ih (b + b / 100)
    simp only [ndRootCoreBackwardConductor]
    omega

@[irreducible] def explicitOnePeriodSeedRootBound (b N : ℕ) : ℕ :=
  explicitOnePeriodSuccessfulRootBound b (explicitExactSeedConductor b N)

theorem explicitOnePeriodSeedRootBound_pos (b N : ℕ) :
    0 < explicitOnePeriodSeedRootBound b N := by
  unfold explicitOnePeriodSeedRootBound
  exact explicitOnePeriodSuccessfulRootBound_pos _ _

theorem explicitSeedFloor_monotone (b : ℕ) : Monotone (explicitSeedFloor b) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [explicitSeedFloor]
  omega

end

end Erdos1135.ND.PositiveDensity
