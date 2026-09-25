import ThreeXMinusOne.CoreCapacity
import ThreeXMinusOne.Window
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalShiftImageRate

/-!
# The adaptive pairing bound

`abs_core_adaptive_pairing_le_image_capacity`, mirrored, and the shift-image bound it needs.

The loss term pairs the core histogram against a kernel whose *shift index varies with the
label*.  That is more than Layer 55's fixed-`g` bound gives, so the sum is first dominated by a
sum over the whole image of the shift map, and the image is small: Layer 32's span bound makes
all the shift indices lie within `e` of each other.

**Two things need no porting.**  `fullTerminalShift`, `fullTerminalShiftImage` and
`fullTerminalShiftImage_card_le` are indexed only by the state wrapper and never mention an
incidence or a map — and `rootSpan`, which the card bound consumes, is literally the same
proposition as the `rootSpanM` I defined at Layer 32.  Both are used here as the artifact's own,
with `rootSpanM_iff_rootSpan` (which is `Iff.rfl`) as the only glue.

**The negation.**  The minus kernels are read at `−(root)`, while the histogram is indexed by
`root`.  Negation is a bijection of `ZMod (3^q)`, so it preserves the uniform mean; that is
`ndTernaryUniformMean_neg`, and it is the only place the residue flip shows up in this file.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

/-- My Layer 32 `rootSpanM` is the artifact's `rootSpan`. -/
theorem rootSpanM_iff_rootSpan (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (e : ℕ) : rootSpanM U e ↔ U.rootSpan e := Iff.rfl

/-- Negation permutes `ZMod (3^q)`, so the uniform mean is unchanged. -/
theorem ndTernaryUniformMean_neg (q : ℕ) (f : ZMod (3 ^ q) → ℝ) :
    ndTernaryUniformMean q (fun y => f (-y)) = ndTernaryUniformMean q f := by
  unfold ndTernaryUniformMean
  congr 1
  exact Fintype.sum_equiv (Equiv.neg (ZMod (3 ^ q))) _ _ (fun y => rfl)

variable (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ) (n : ℕ)

/-- The pairing bound at the negated residue. -/
theorem abs_coreHistogramM_pairing_neg_le_capacity (q : ℕ)
    (hq : q ≤ 2 * (forwardIterateM U cap n).floor) (g : ZMod (3 ^ q) → ℝ) :
    letI := (forwardIterateM U cap n).state.labelFintype
    |∑ i, forwardCoreOuterWeightM U cap width n i *
        g (-(((forwardIterateM U cap n).state.root i : ℕ) : ZMod (3 ^ q)))| ≤
      coreCapacityBudgetM U cap width n * ndTernaryUniformMean q (fun y => |g y|) := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  have hpair := forwardCoreHistogramM_pairing U cap width n q (fun y => g (-y))
  have hbd := abs_coreHistogramM_pairing_le_capacity U cap width n q hq (fun y => g (-y))
  rw [ndTernaryUniformMean_neg q (fun y => |g y|)] at hbd
  rw [← hpair]
  exact hbd

/-- **The adaptive pairing bound.**  The shift index may vary with the label. -/
theorem abs_core_adaptive_pairingM_le_image_capacity (q : ℕ)
    (hq : q ≤ 2 * (forwardIterateM U cap n).floor)
    (S : Finset ℕ) (sigma : (forwardIterateM U cap n).state.Label → ℕ)
    (hS : ∀ i, sigma i ∈ S) (F : ℕ → ZMod (3 ^ q) → ℝ)
    {u : ℝ} (_hu : 0 ≤ u) (hF : ∀ a ∈ S, ndTernaryUniformMean q (fun y => |F a y|) ≤ u) :
    letI := (forwardIterateM U cap n).state.labelFintype
    |∑ i, forwardCoreOuterWeightM U cap width n i *
        F (sigma i) (-(((forwardIterateM U cap n).state.root i : ℕ) : ZMod (3 ^ q)))| ≤
      (S.card : ℝ) * coreCapacityBudgetM U cap width n * u := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  have hw (i) : 0 ≤ forwardCoreOuterWeightM U cap width n i :=
    forwardCoreOuterWeightM_nonneg U cap width n i
  calc |∑ i, forwardCoreOuterWeightM U cap width n i *
          F (sigma i) (-(((forwardIterateM U cap n).state.root i : ℕ) : ZMod (3 ^ q)))|
      ≤ ∑ i, forwardCoreOuterWeightM U cap width n i *
          |F (sigma i) (-(((forwardIterateM U cap n).state.root i : ℕ) : ZMod (3 ^ q)))| := by
        simpa only [abs_mul, abs_of_nonneg (hw _)] using Finset.abs_sum_le_sum_abs
          (fun i => forwardCoreOuterWeightM U cap width n i * F (sigma i)
            (-(((forwardIterateM U cap n).state.root i : ℕ) : ZMod (3 ^ q)))) Finset.univ
    _ ≤ ∑ i, forwardCoreOuterWeightM U cap width n i *
          ∑ a ∈ S, |F a (-(((forwardIterateM U cap n).state.root i : ℕ) : ZMod (3 ^ q)))| := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hw i)
        exact Finset.single_le_sum
          (f := fun a => |F a (-(((forwardIterateM U cap n).state.root i : ℕ) : ZMod (3 ^ q)))|)
          (fun a _ => abs_nonneg _) (hS i)
    _ = ∑ a ∈ S, ∑ i, forwardCoreOuterWeightM U cap width n i *
          |F a (-(((forwardIterateM U cap n).state.root i : ℕ) : ZMod (3 ^ q)))| := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
    _ ≤ ∑ _a ∈ S, coreCapacityBudgetM U cap width n * u := by
        refine Finset.sum_le_sum fun a ha => ?_
        refine (le_abs_self _).trans ?_
        refine (abs_coreHistogramM_pairing_neg_le_capacity U cap width n q hq
          (fun y => |F a y|)).trans ?_
        simpa only [abs_abs] using
          mul_le_mul_of_nonneg_left (hF a ha) (coreCapacityBudgetM_nonneg U cap width n)
    _ = _ := by simp; ring

end

end ThreeXMinusOne
