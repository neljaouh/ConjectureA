import Erdos1135.Tao.Renewal.QEndpointFreshOutsideEprimeBudget

namespace Erdos1135

namespace Tao

noncomputable section

open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

noncomputable def lemma79OutsideEprimeNativeConstant
    (C32 c32 : ℝ) : ℝ :=
  30 + lemma79OutsideEprimeMassConstant C32 c32

theorem lemma79OutsideEprimeNativeConstant_nonneg
    {C32 c32 : ℝ} (hC32 : 0 ≤ C32) (hc32 : 0 < c32) :
    0 ≤ lemma79OutsideEprimeNativeConstant C32 c32 := by
  unfold lemma79OutsideEprimeNativeConstant
  exact add_nonneg (by norm_num)
    (lemma79OutsideEprimeMassConstant_nonneg hC32 hc32)

theorem lemma79OutsideEprimeCoefficient_le_native
    {C32 c32 coefficient X sMin : ℝ}
    (hcoefficient :
      coefficient ≤ lemma79OutsideEprimeNativeConstant C32 c32)
    (hX : 0 ≤ X) (hsMin : 0 ≤ sMin) :
    ENNReal.ofReal (coefficient * X / sMin) ≤
      ENNReal.ofReal
        (lemma79OutsideEprimeNativeConstant C32 c32 * X / sMin) := by
  apply ENNReal.ofReal_le_ofReal
  calc
    coefficient * X / sMin = coefficient * (X / sMin) := by ring
    _ ≤ lemma79OutsideEprimeNativeConstant C32 c32 * (X / sMin) :=
      mul_le_mul_of_nonneg_right hcoefficient (div_nonneg hX hsMin)
    _ = lemma79OutsideEprimeNativeConstant C32 c32 * X / sMin := by
      ring

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135
