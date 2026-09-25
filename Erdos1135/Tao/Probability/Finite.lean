import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open scoped BigOperators

namespace Erdos1135

namespace Tao

theorem pmf_sum_toReal {α : Type*} [Fintype α] (p : PMF α) :
    (∑ a, (p a).toReal) = 1 := by
  have htsum := congrArg ENNReal.toReal (PMF.tsum_coe p)
  rw [ENNReal.tsum_toReal_eq (PMF.apply_ne_top p)] at htsum
  rw [tsum_fintype] at htsum
  simpa using htsum

end Tao

end Erdos1135
