import Erdos1135.ND.PositiveDensity.ExplicitLogarithmicFrozenSeed
import Erdos1135.ND.PositiveDensity.ExplicitSixthRootSeedToCount

namespace Erdos1135.ND.PositiveDensity

noncomputable section

@[irreducible] def explicitExactSeedConductor (b N : ℕ) : ℕ :=
  ndRootCoreBackwardConductor b (explicitSeedFloor b N / 4) N

end

end Erdos1135.ND.PositiveDensity
