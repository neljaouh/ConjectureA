import Erdos1135.Tao.Section6.AdjacentOneStep
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators

namespace Erdos1135

namespace Tao

noncomputable section

theorem syracFineScaleOscillation_le_sum_adjacent
    {m n : ℕ} (hmn : m ≤ n) :
    syracFineScaleOscillation m n ≤
      ∑ r ∈ Finset.Ico m n,
        syracFineScaleOscillation r (r + 1) := by
  induction n, hmn using Nat.le_induction with
  | base =>
      simp
  | succ n hmn ih =>
      calc
        syracFineScaleOscillation m (n + 1) ≤
            syracFineScaleOscillation m n +
              syracFineScaleOscillation n (n + 1) :=
          syracFineScaleOscillation_succ_le_add hmn
        _ ≤ (∑ r ∈ Finset.Ico m n,
              syracFineScaleOscillation r (r + 1)) +
              syracFineScaleOscillation n (n + 1) :=
          add_le_add ih (le_refl _)
        _ = ∑ r ∈ Finset.Ico m (n + 1),
              syracFineScaleOscillation r (r + 1) := by
          rw [Finset.sum_Ico_succ_top hmn]

end

end Tao

end Erdos1135
