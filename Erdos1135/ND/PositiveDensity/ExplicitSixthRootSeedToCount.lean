import Erdos1135.ND.PositiveDensity.ExplicitLogarithmicConductorRoom
import Erdos1135.ND.PositiveDensity.ExplicitPositiveDensityPair
import Erdos1135.ND.PositiveDensity.ExplicitSeedToCount
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

namespace Erdos1135.ND.PositiveDensity

noncomputable section

theorem explicitLogarithmicRoomStart_mono : Monotone explicitLogarithmicRoomStart := by
  intro m k hmk
  unfold explicitLogarithmicRoomStart
  exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.clog_mono_right 2 hmk) 78)

end

end Erdos1135.ND.PositiveDensity
