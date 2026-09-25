import Erdos1135.Tao.Probability.Finite
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring

open scoped BigOperators

namespace Erdos1135

namespace Tao

theorem taoPMF_summable_toReal {α : Type*} (p : PMF α) :
    Summable fun a : α => (p a).toReal := by
  refine ENNReal.summable_toReal ?_
  rw [PMF.tsum_coe p]
  norm_num

theorem pmfOuterMass_toReal_eq_tsum_indicator
    {α : Type*} (p : PMF α) (E : Set α) :
    (p.toOuterMeasure E).toReal =
      ∑' a : α, E.indicator (fun a => (p a).toReal) a := by
  classical
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro a
    by_cases h : a ∈ E <;> simp [Set.indicator, h]
  · intro a
    by_cases h : a ∈ E <;>
      simp [Set.indicator, h, PMF.apply_ne_top p a]

end Tao

end Erdos1135
