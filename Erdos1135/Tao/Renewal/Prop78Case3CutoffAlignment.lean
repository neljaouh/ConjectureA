import Erdos1135.Tao.Renewal.GeometryBridge
import Erdos1135.Tao.Renewal.Prop78Case3Event
import Erdos1135.Tao.Renewal.SourceActualQ

namespace Erdos1135

namespace Tao

open Finset

def taoSection7Case3SourceCutoffPointW
    (pointAt : ℕ → TaoSection7Point)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (J : ℕ) (p : ℕ) : Prop :=
  taoSection7SourcePointInDomain J (pointAt p) ∧
    taoSection7SourceWhitePoint n xi epsilon (pointAt p)

theorem taoSection7Case3WindowWhiteCount_congr_range
    (W W' : ℕ → Prop) [DecidablePred W] [DecidablePred W']
    {P : ℕ}
    (halign : ∀ p : ℕ, p < P → (W p ↔ W' p)) :
    taoSection7Case3WindowWhiteCount W P =
      taoSection7Case3WindowWhiteCount W' P := by
  unfold taoSection7Case3WindowWhiteCount
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hp_lt : p < P := Finset.mem_range.mp hp
  by_cases hW : W p
  · have hW' : W' p := (halign p hp_lt).mp hW
    simp [hW, hW']
  · have hW' : ¬ W' p := by
      intro h'
      exact hW ((halign p hp_lt).mpr h')
    simp [hW, hW']

theorem taoSection7Case3_sourceActualW_iff_sourceCutoffPointW_toPoint
    (renewalAt : ℕ → TaoSection7RenewalPoint)
    {n p : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ} :
    taoSection7SourceActualW n xi epsilon (renewalAt p) ↔
      taoSection7Case3SourceCutoffPointW
        (fun q => (renewalAt q).toPoint) n xi epsilon (n / 2) p := by
  simpa [taoSection7SourceActualW, taoSection7Case3SourceCutoffPointW] using
    (taoSection7SourceWhiteRenewal_cutoff_iff_toPoint
      (n := n) (J := n / 2) (xi := xi) (epsilon := epsilon)
      (p := renewalAt p))

end Tao

end Erdos1135
