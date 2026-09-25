import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricRegenerativeState
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideBoundedOvershootPhysicalIncidence

namespace Erdos1135

namespace ND

namespace PositiveDensity

noncomputable section

def ndGeom2RootSideCapTail (cap : ℕ → ℕ) : ℕ → ℕ :=
  fun n => cap (n + 1)

end

end PositiveDensity

end ND

end Erdos1135
