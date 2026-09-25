import Erdos1135.Tao.Renewal.QFiniteIteration
import Erdos1135.Tao.Renewal.SourceActualQ

open scoped BigOperators

namespace Erdos1135

namespace Tao

noncomputable section

theorem taoSection7SourceActualQ_eq_holdListContinuation_master_of_le
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    {P J : ℕ} (hPJ : P ≤ J)
    (start : TaoSection7RenewalPoint) :
    taoSection7SourceActualQ n xi epsilon start =
      ∑' full : List TaoSection7RenewalPoint,
        (taoSection7HoldListPMF J full).toReal *
          (taoSection7QPrefixFactor epsilon
              (taoSection7SourceActualW n xi epsilon)
              start (full.take P) *
            taoSection7SourceActualQ n xi epsilon
              (taoSection7RenewalPathPoint start full P)) := by
  exact taoSection7ActualQ_eq_holdListQContinuationExpectation_master_of_le
    hPJ hepsilon (taoSection7SourceActualQ_finiteLimit hepsilon) start

end

end Tao

end Erdos1135
