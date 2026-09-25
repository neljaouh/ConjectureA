import Erdos1135.Tao.Syracuse.Basic
import Mathlib.Algebra.BigOperators.Field

namespace Erdos1135

namespace ND

namespace PositiveDensity

open scoped BigOperators

noncomputable section

structure NDCommonZReverseEdge where
  source : ℕ
  target : ℕ
  exponent : ℕ
  source_pos : 0 < source
  target_pos : 0 < target
  affine : 2 ^ exponent * target = 3 * source + 1

def ndCommonZEdgeSourceWeight (q : ℕ) (e : NDCommonZReverseEdge) : ℝ :=
  (3 : ℝ) ^ q / (e.source : ℝ)

def ndCommonZEdgeTransportedWeight (q : ℕ)
    (e : NDCommonZReverseEdge) : ℝ :=
  (3 : ℝ) ^ (q + 1) /
    ((2 : ℝ) ^ e.exponent * (e.target : ℝ))

def ndCommonZEdgeDefect (q : ℕ) (e : NDCommonZReverseEdge) : ℝ :=
  (3 : ℝ) ^ q /
    ((e.source : ℝ) * (3 * (e.source : ℝ) + 1))

theorem ndCommonZEdgeDefect_nonneg
    (q : ℕ) (e : NDCommonZReverseEdge) :
    0 ≤ ndCommonZEdgeDefect q e := by
  unfold ndCommonZEdgeDefect
  positivity

theorem ndCommonZEdge_source_eq_transport_add_defect
    (q : ℕ) (e : NDCommonZReverseEdge) :
    ndCommonZEdgeSourceWeight q e =
      ndCommonZEdgeTransportedWeight q e +
        ndCommonZEdgeDefect q e := by
  have haffine :
      (2 : ℝ) ^ e.exponent * (e.target : ℝ) =
        3 * (e.source : ℝ) + 1 := by
    exact_mod_cast e.affine
  unfold ndCommonZEdgeSourceWeight ndCommonZEdgeTransportedWeight
    ndCommonZEdgeDefect
  rw [haffine]
  have hsv : (e.source : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt e.source_pos)
  have hden : 3 * (e.source : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hsv, hden]
  ring

def ndCommonZActualReverseEdge (v : ℕ) (hv : 0 < v) :
    NDCommonZReverseEdge where
  source := v
  target := Tao.syracuse v
  exponent := Tao.syracuseExponent v
  source_pos := hv
  target_pos := Tao.syracuse_pos v
  affine := Tao.two_pow_syracuseExponent_mul_syracuse v

end

end PositiveDensity

end ND

end Erdos1135
