import Erdos1135.Tao.Renewal.QEndpointFreshOutsideEprimeSourceWidth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Erdos1135

namespace Tao

noncomputable section

open Filter Topology

open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

theorem lemma79OutsideEprimeErrorMargin_of_split_absorption
    {Aweight p : ℕ} {S : ℝ}
    (hJ :
      2 * S ^ (3 / 5 : ℝ) ≤
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) / 2)
    (hL :
      (Real.log 2 / Real.log 9) *
          (2 * lemma79OutsideEprimeScale Aweight p) + 1 ≤
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) / 2) :
    2 * S ^ (3 / 5 : ℝ) +
        ((Real.log 2 / Real.log 9) *
          (2 * lemma79OutsideEprimeScale Aweight p) + 1) ≤
      S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) := by
  linarith

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135
