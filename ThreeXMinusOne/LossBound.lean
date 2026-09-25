import ThreeXMinusOne.AdaptivePairing
import ThreeXMinusOne.DepthShiftSplit

/-!
# The depth-shift loss is small

`forwardCoreTerminalBadDepthShiftUnitMass_le`, mirrored.

Layer 49 split the terminal mass into the part inside the depth-shift band and the loss.  This
bounds the loss.  Layer 49's kernel form turns it into a pairing of the core histogram against
the bad-filter kernel, with the shift index varying by label; Layer 56 bounds such a pairing by
(image size) × (capacity budget) × (kernel mean); the image is at most `e + 1` wide by Layer 32's
span bound; and the kernel's own mean is exponentially small in the floor.

**That last input needs no porting.**  `terminalDepthShift_badKernel_fullMean_le` bounds the mean
of the bad-filter kernel by `(2/3)·(4b+4)·exp(−b/16384)`, and it is a statement about the kernel
and the word-only bad filter — no root, no source, no residue.  It is used here verbatim, which
is why the whole exponential-smallness of the loss carries over to `3x−1` unexamined.

What the minus side adds is only the generation excess inside `coreCapacityBudgetM`.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

/-- **The loss is exponentially small in the floor.** -/
theorem forwardCoreTerminalBadDepthShiftUnitMassM_le
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ)
    (n K k e : ℕ) (he : rootSpanM (forwardIterateM U cap n) e) (hk : 1 ≤ k)
    (hq : ndGeom2ShiftedWideSymmetricHorizon (forwardIterateM U cap n).floor + k ≤
      2 * (forwardIterateM U cap n).floor)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) :
    forwardCoreTerminalBadDepthShiftUnitMassM U cap width n K k X hX hi ≤
      (e + 1 : ℝ) * coreCapacityBudgetM U cap width n *
        ((2 / 3 : ℝ) * ((4 * ((forwardIterateM U cap n).floor : ℝ) + 4) *
          Real.exp (-((forwardIterateM U cap n).floor : ℝ) / 16384))) := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  set q := ndGeom2ShiftedWideSymmetricHorizon (forwardIterateM U cap n).floor + k with hqdef
  set S := (forwardIterateM U cap n).fullTerminalShiftImage X hX hi with hSdef
  set F : ℕ → ZMod (3 ^ q) → ℝ := fun a =>
    ndRootCoreFilteredKernel (forwardIterateM U cap n).floor a K k
      (ndTerminalDepthShiftBadFilter (forwardIterateM U cap n).floor a)
      (ndSyracuseUnitReferenceDensity k) with hFdef
  set u : ℝ := (2 / 3 : ℝ) * ((4 * ((forwardIterateM U cap n).floor : ℝ) + 4) *
    Real.exp (-((forwardIterateM U cap n).floor : ℝ) / 16384)) with hudef
  have hu : 0 ≤ u := by rw [hudef]; positivity
  have hF : ∀ a ∈ S, ndTernaryUniformMean q (fun y => |F a y|) ≤ u := by
    intro a _
    have hn (y) : 0 ≤ F a y :=
      rootCoreFilteredKernel_nonneg (forwardIterateM U cap n).floor a K k _
        (terminalDepthShiftBadFilter_nonneg _ _) _ (ndSyracuseUnitReferenceDensity_nonneg _) y
    simp_rw [abs_of_nonneg (hn _)]
    exact terminalDepthShift_badKernel_fullMean_le
      (forwardIterateM U cap n).floor_twoHundred a K k
  have hmem := (forwardIterateM U cap n).mem_fullTerminalShiftImage X hX hi
  have h := abs_core_adaptive_pairingM_le_image_capacity U cap width n q hq S
    ((forwardIterateM U cap n).fullTerminalShift X hX hi) hmem F hu hF
  rw [forwardCoreTerminalBadDepthShiftUnitMassM_eq_kernel U cap width n K k X hX hk hi]
  refine (le_abs_self _).trans (h.trans ?_)
  have hcard : (S.card : ℝ) ≤ (e + 1 : ℝ) := by
    have := (forwardIterateM U cap n).fullTerminalShiftImage_card_le
      ((rootSpanM_iff_rootSpan (forwardIterateM U cap n) e).mp he) X hX hi
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcard (coreCapacityBudgetM_nonneg U cap width n)) hu

end

end ThreeXMinusOne
