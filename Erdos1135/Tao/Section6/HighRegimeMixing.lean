import Erdos1135.Tao.Section6.FixedAmbientSlice
import Erdos1135.Tao.Section6.Geom2IntervalConcentration

open scoped BigOperators

namespace Erdos1135

namespace Tao

noncomputable section

theorem taoSection6_box_mul_div_pow_eq
    (A n : ℕ) (D : ℝ) (hn : 1 ≤ n) :
    (((n * (2 * n) : ℕ) : ℝ) *
        (D / (n : ℝ) ^ (A + 3))) =
      (2 * D) / (n : ℝ) ^ (A + 1) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [show A + 3 = (A + 1) + 2 by omega, pow_add]
  push_cast
  field_simp [hnR]

theorem taoSection6FixedAmbientOscillation_sum_le
    {CA D : ℝ} {A n m : ℕ} (hn : 1 ≤ n)
    (hslice : ∀ k : Fin n, ∀ l : Fin (2 * n),
      taoZModPowOscillation m n
          (taoSection6FixedAmbientSubmass CA n k l) ≤
        D / (n : ℝ) ^ (A + 3)) :
    (∑ k : Fin n, ∑ l : Fin (2 * n),
      taoZModPowOscillation m n
        (taoSection6FixedAmbientSubmass CA n k l)) ≤
      (2 * D) / (n : ℝ) ^ (A + 1) := by
  let B : ℝ := D / (n : ℝ) ^ (A + 3)
  calc
    (∑ k : Fin n, ∑ l : Fin (2 * n),
        taoZModPowOscillation m n
          (taoSection6FixedAmbientSubmass CA n k l)) ≤
        ∑ _k : Fin n, ∑ _l : Fin (2 * n), B := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      exact hslice k l
    _ = (((n * (2 * n) : ℕ) : ℝ) * B) := by
      simp [Nat.cast_mul]
      ring
    _ = (2 * D) / (n : ℝ) ^ (A + 1) := by
      exact taoSection6_box_mul_div_pow_eq A n D hn

end

end Tao

end Erdos1135
