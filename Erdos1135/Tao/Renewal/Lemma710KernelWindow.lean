import Erdos1135.Tao.Fourier.Section7Geometry
import Erdos1135.Tao.Probability.Finite
import Erdos1135.Tao.Renewal.HoldStoppedTail
import Erdos1135.Tao.Renewal.SeparatedWindowSum

namespace Erdos1135

namespace Tao

open scoped BigOperators

noncomputable section

namespace TaoSection7Lemma710

theorem j_mem_intWindow_of_distSq_le
    {R : ℕ} {p q : TaoSection7Point}
    (h : p.distSq q ≤ (R : ℝ) ^ 2) :
    (((p.j : ℕ) : ℤ) ∈
      taoSection7IntIccWindow R (((q.j : ℕ) : ℤ))) := by
  rw [mem_taoSection7IntIccWindow]
  have hsq_horiz :
      (p.jReal - q.jReal) ^ 2 ≤ (R : ℝ) ^ 2 := by
    have hv : 0 ≤ (p.lReal - q.lReal) ^ 2 := sq_nonneg _
    dsimp [TaoSection7Point.distSq] at h
    nlinarith
  have hR : 0 ≤ (R : ℝ) := by positivity
  have hbounds := abs_le_of_sq_le_sq' hsq_horiz hR
  constructor
  · have hleft_real :
        ((q.j : ℕ) : ℝ) - (R : ℝ) ≤ ((p.j : ℕ) : ℝ) := by
      dsimp [TaoSection7Point.jReal] at hbounds
      linarith
    exact_mod_cast hleft_real
  · have hright_real :
        ((p.j : ℕ) : ℝ) ≤ ((q.j : ℕ) : ℝ) + (R : ℝ) := by
      dsimp [TaoSection7Point.jReal] at hbounds
      linarith
    exact_mod_cast hright_real

end TaoSection7Lemma710

end

end Tao

end Erdos1135
