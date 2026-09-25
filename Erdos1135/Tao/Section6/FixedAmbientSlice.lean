import Erdos1135.Tao.Section6.FixedSliceCollision
import Erdos1135.Tao.Section6.HeadEntropyScalar
import Erdos1135.Tao.Section6.HeadGateIndex

namespace Erdos1135

namespace Tao

noncomputable section

noncomputable def taoSection6FixedAmbientGate
    (CA : ℝ) (n k l : ℕ) (full : List ℕ+) : Prop :=
  full.length = n ∧
    taoSection6HeadGate CA n k l (full.take (k + 1))

noncomputable def taoSection6FixedAmbientPMF
    (CA : ℝ) (n k l : ℕ) : PMF (Option (ZMod (3 ^ n))) :=
  taoGatedOptionPMF
    (geom2PNatListPMF n)
    (taoSection6FixedAmbientGate CA n k l)
    (taoSection7OffsetZMod n)

noncomputable def taoSection6FixedAmbientSubmass
    (CA : ℝ) (n k l : ℕ) (x : ZMod (3 ^ n)) : ℝ :=
  (taoSection6FixedAmbientPMF CA n k l (some x)).toReal

theorem taoSection6FixedAmbientPMF_add_eq_gatedSourcePMF
    (CA : ℝ) (T k l : ℕ) :
    taoSection6FixedAmbientPMF CA (T + (k + 1)) k l =
      taoSection6GatedSourcePMF CA T k l := by
  apply PMF.ext
  intro y
  unfold taoSection6FixedAmbientPMF taoSection6GatedSourcePMF
  unfold taoGatedOptionPMF
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro full
  by_cases hlength : full.length = T + (k + 1)
  · by_cases hgate :
        taoSection6HeadGate CA (T + (k + 1)) k l
          (full.take (k + 1))
    · simp [taoSection6FixedAmbientGate, taoGatedOptionKey, hlength, hgate]
    · simp [taoSection6FixedAmbientGate, taoGatedOptionKey, hlength, hgate]
  · have hzero : geom2PNatListPMF (T + (k + 1)) full = 0 :=
      geom2PNatListPMF_apply_eq_zero_of_length_ne _ _ hlength
    simp [hzero]

theorem taoSection6FixedAmbientSubmass_add_eq_gatedSourceSubmass
    (CA : ℝ) (T k l : ℕ) (x : ZMod (3 ^ (T + (k + 1)))) :
    taoSection6FixedAmbientSubmass CA (T + (k + 1)) k l x =
      taoSection6GatedSourceSubmass CA T k l x := by
  unfold taoSection6FixedAmbientSubmass taoSection6GatedSourceSubmass
  rw [taoSection6FixedAmbientPMF_add_eq_gatedSourcePMF]

end

end Tao

end Erdos1135
