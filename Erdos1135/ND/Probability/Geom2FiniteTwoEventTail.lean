import Erdos1135.Tao.Probability.FullL1
import Erdos1135.Tao.Probability.Geom2CenteredMoment
import Erdos1135.Tao.Probability.Geom2ListProjectivity

namespace Erdos1135

namespace ND

open scoped BigOperators

noncomputable section

theorem geom2PNatListPMF_take_event_outerMeasure_toReal
    {r m : ℕ} (hrm : r ≤ m) (A : Set (List ℕ+)) :
    ((Tao.geom2PNatListPMF m).toOuterMeasure
      ((fun bs => bs.take r) ⁻¹' A)).toReal =
    ((Tao.geom2PNatListPMF r).toOuterMeasure A).toReal := by
  rw [← Tao.geom2PNatListPMF_map_take_low_eq_of_le hrm]
  rw [PMF.toOuterMeasure_map_apply]

end

end ND

end Erdos1135
