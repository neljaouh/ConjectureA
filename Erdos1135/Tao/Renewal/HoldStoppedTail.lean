import Erdos1135.Tao.Renewal.HoldIID
import Erdos1135.Tao.Renewal.QFiniteApprox

open scoped BigOperators

namespace Erdos1135

namespace Tao

theorem taoSection7HoldListMass_append
    (pre tail : List TaoSection7RenewalPoint) :
    taoSection7HoldListMass (pre ++ tail) =
      taoSection7HoldListMass pre * taoSection7HoldListMass tail := by
  simp [taoSection7HoldListMass, List.map_append, List.prod_append]

theorem taoSection7HoldListPMF_append_toReal
    (pre tail : List TaoSection7RenewalPoint) :
    (taoSection7HoldListPMF (pre.length + tail.length)
      (pre ++ tail)).toReal =
      (taoSection7HoldListPMF pre.length pre).toReal *
        (taoSection7HoldListPMF tail.length tail).toReal := by
  have hlen : (pre ++ tail).length = pre.length + tail.length := by
    simp [List.length_append]
  rw [← hlen]
  rw [taoSection7HoldListPMF_apply_length_toReal]
  rw [taoSection7HoldListPMF_apply_length_toReal]
  rw [taoSection7HoldListPMF_apply_length_toReal]
  simp [taoSection7HoldListMass_append]

theorem taoSection7HoldListPMF_append_toReal_of_lengths
    {K p : ℕ} {pre tail : List TaoSection7RenewalPoint}
    (hpre : pre.length = K) (htail : tail.length = p) :
    (taoSection7HoldListPMF (K + p) (pre ++ tail)).toReal =
      (taoSection7HoldListPMF K pre).toReal *
        (taoSection7HoldListPMF p tail).toReal := by
  subst K
  subst p
  exact taoSection7HoldListPMF_append_toReal pre tail

theorem taoSection7HoldListPMF_singleton_toReal
    (last : TaoSection7RenewalPoint) :
    (taoSection7HoldListPMF 1 [last]).toReal =
      (taoSection7HoldPMF last).toReal := by
  simpa [taoSection7HoldListMass] using
    (taoSection7HoldListPMF_apply_length_toReal [last])

theorem taoSection7HoldListPMF_snoc_toReal
    (pre : List TaoSection7RenewalPoint) (last : TaoSection7RenewalPoint) :
    (taoSection7HoldListPMF (pre.length + 1) (pre ++ [last])).toReal =
      (taoSection7HoldListPMF pre.length pre).toReal *
        (taoSection7HoldPMF last).toReal := by
  simpa [taoSection7HoldListPMF_singleton_toReal] using
    (taoSection7HoldListPMF_append_toReal pre [last])

end Tao

end Erdos1135
