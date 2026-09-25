import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricBoundedOvershootPhysicalIncidence

namespace Erdos1135

namespace ND

namespace PositiveDensity

open scoped BigOperators

noncomputable section

theorem ndGeom2ShiftedWideSymmetricHit_reverse_of_length
    {b a s : ℕ} {rootSide : List ℕ+}
    (hlen : rootSide.length = s)
    (hhit : ndGeom2ShiftedWideSymmetricHit b a s rootSide) :
    ndGeom2ShiftedWideSymmetricHit b a s rootSide.reverse := by
  have htake : rootSide.take s = rootSide := by
    rw [← hlen]
    exact List.take_length
  have htakeReverse : rootSide.reverse.take s = rootSide.reverse := by
    rw [← hlen, ← List.length_reverse]
    exact List.take_length
  unfold ndGeom2ShiftedWideSymmetricHit at hhit ⊢
  rw [htake] at hhit
  rw [htakeReverse, Tao.taoTupleWeight_reverse]
  exact hhit

theorem ndGeom2ShiftedWideSymmetricBoundedOvershoot_reverse
    (b a s K : ℕ) (rootSide : List ℕ+) :
    ndGeom2ShiftedWideSymmetricBoundedOvershoot b a s K rootSide.reverse ↔
      ndGeom2ShiftedWideSymmetricBoundedOvershoot b a s K rootSide := by
  unfold ndGeom2ShiftedWideSymmetricBoundedOvershoot
  rw [Tao.taoTupleWeight_reverse]

end

end PositiveDensity

end ND

end Erdos1135
