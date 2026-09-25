import ThreeXMinusOne.CoreVariation
import ThreeXMinusOne.CoreTerminalMass
import ThreeXMinusOne.Window
import ThreeXMinusOne.SigmaBridge
import Erdos1135.ND.PositiveDensity.ExplicitTerminalVariation

/-!
# The terminal mass tracks the core mass

`explicit_terminalUnitMass_error`, mirrored.

The second half of the variation argument.  The terminal unit mass and the core marked mass are
two readings of the same weights — one through the shifted reference kernel at the chosen shift,
the other through the reference density at the coarse conductor — and their difference is again
an adaptive pairing of the core histogram, bounded by Layer 56.

**The two kernels coincide.**  `ndShiftedReferenceMarkedKernel` is `ndRootCoreFilteredKernel`
with the word filter identically `1`; both are the same sum of prefix transports.  So Layer 25
supplies the terminal mass's kernel form with no new work, and `explicitShiftedReferenceKernel_error`
— which quantifies over bare naturals — supplies the rate.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

/-- The two kernels are the same function. -/
theorem shiftedReferenceMarkedKernel_eq_filtered (b a K k : ℕ) :
    ndShiftedReferenceMarkedKernel b a K k =
      ndRootCoreFilteredKernel b a K k (fun _ => 1) (ndSyracuseUnitReferenceDensity k) := by
  funext y
  unfold ndShiftedReferenceMarkedKernel ndRootCoreFilteredKernel ndRootCoreTransportWord
  exact (Finset.sum_congr rfl fun w _ => (one_mul _).symm)

/-- The terminal unit mass as a kernel sum, at the negated residue. -/
theorem forwardCoreTerminalUnitMassM_eq_kernel
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ)
    (n K k : ℕ) (hk : 1 ≤ k) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) :
    letI := (forwardIterateM U cap n).state.labelFintype
    forwardCoreTerminalUnitMassM U cap width n K k X hX hi =
      ∑ i, forwardCoreOuterWeightM U cap width n i *
        ndShiftedReferenceMarkedKernel (forwardIterateM U cap n).floor
          ((forwardIterateM U cap n).fullTerminalShift X hX hi i) K k
          (-((((forwardIterateM U cap n).state.root i : ℕ)) :
            ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon (forwardIterateM U cap n).floor
              + k)))) := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  unfold forwardCoreTerminalUnitMassM
  rw [sum_sigma_packetM ((forwardIterateM U cap n).fullTerminalShift X hX hi)
    (forwardIterateM U cap n).floor K
    (fun i z => ucWeightM (forwardCoreOuterWeightM U cap width n) z *
      ndSyracuseUnitReferenceDensity k (-((ucSourceM z : ℕ) : ZMod (3 ^ k))))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := sum_unitIncidenceM_mark_eq_filteredKernel
    (Labels := ({i} : Finset (forwardIterateM U cap n).state.Label))
    (root := (forwardIterateM U cap n).state.root)
    (b := (forwardIterateM U cap n).floor)
    (a := (forwardIterateM U cap n).fullTerminalShift X hX hi i) (K := K)
    (forwardCoreOuterWeightM U cap width n) k
    (forwardIterateM U cap n).state.root_odd
    (by have hh := (forwardIterateM U cap n).floor_twoHundred; omega)
    (fun j => (Nat.pow_le_pow_right (by norm_num)
      ((forwardIterateM U cap n).floor_le_base j)).trans
      ((forwardIterateM U cap n).state.rootLower j))
    hk (fun _ => (1 : ℝ)) (ndSyracuseUnitReferenceDensity k)
    (unitReferenceDensity_natCast_eq_zero_of_not_unit hk)
  simp only [mul_one] at h
  rw [h, shiftedReferenceMarkedKernel_eq_filtered]
  rw [← Finset.sum_subtype ({i} : Finset (forwardIterateM U cap n).state.Label)
    (fun _ => Iff.rfl)
    (fun j => forwardCoreOuterWeightM U cap width n j *
      ndRootCoreFilteredKernel (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).fullTerminalShift X hX hi i) K k (fun _ => (1 : ℝ))
        (ndSyracuseUnitReferenceDensity k)
        (-((((forwardIterateM U cap n).state.root j : ℕ)) :
          ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon (forwardIterateM U cap n).floor + k)))))]
  simp

/-- **The terminal mass tracks the core mass**, with an error bounded by the capacity budget. -/
theorem explicit_terminalUnitMassM_error {A : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt A C)
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ)
    (n e K k : ℕ) (he : rootSpanM (forwardIterateM U cap n) e) (hk : 1 ≤ k)
    (hq : ndGeom2ShiftedWideSymmetricHorizon (forwardIterateM U cap n).floor + k ≤
      2 * (forwardIterateM U cap n).floor)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) :
    |forwardCoreTerminalUnitMassM U cap width n K k X hX hi -
        forwardCoreMassM U cap width n k (fun _ => 1)| ≤
      (e + 1 : ℝ) * coreCapacityBudgetM U cap width n * ((2 / 3 : ℝ) *
        (2 * C / (k : ℝ) ^ A + 4 * Real.exp (-((forwardIterateM U cap n).floor : ℝ) / 2560000) +
          (1 / 2 : ℝ) ^ (K + 1))) := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  set q := ndGeom2ShiftedWideSymmetricHorizon (forwardIterateM U cap n).floor + k with hqdef
  have hkq : k ≤ q := Nat.le_add_left _ _
  set F : ℕ → ZMod (3 ^ q) → ℝ := fun a y =>
    ndShiftedReferenceMarkedKernel (forwardIterateM U cap n).floor a K k y -
      ndSyracuseUnitReferenceDensity k (Tao.taoZModThreeProjection hkq y) with hF
  set u : ℝ := (2 / 3 : ℝ) * (2 * C / (k : ℝ) ^ A +
    4 * Real.exp (-((forwardIterateM U cap n).floor : ℝ) / 2560000) +
    (1 / 2 : ℝ) ^ (K + 1)) with hu_def
  have hu : 0 ≤ u := by rw [hu_def]; positivity
  have hFb : ∀ a ∈ (forwardIterateM U cap n).fullTerminalShiftImage X hX hi,
      ndTernaryUniformMean q (fun y => |F a y|) ≤ u := by
    intro a ha
    have h := explicitShiftedReferenceKernel_error hC hmix
      (forwardIterateM U cap n).floor a K k k
      (forwardIterateM U cap n).floor_twoHundred
      ((forwardIterateM U cap n).fullTerminalShiftImage_subset_legal X hX hi ha) hk hk hkq
    refine h.trans (le_of_eq ?_)
    rw [hu_def]; ring
  have hs := abs_core_adaptive_pairingM_le_image_capacity U cap width n q hq
    ((forwardIterateM U cap n).fullTerminalShiftImage X hX hi)
    ((forwardIterateM U cap n).fullTerminalShift X hX hi)
    ((forwardIterateM U cap n).mem_fullTerminalShiftImage X hX hi) F hu hFb
  have hmass : forwardCoreMassM U cap width n k (fun _ => 1) =
      ∑ i, forwardCoreOuterWeightM U cap width n i *
        ndSyracuseUnitReferenceDensity k (Tao.taoZModThreeProjection hkq
          (-((((forwardIterateM U cap n).state.root i : ℕ)) : ZMod (3 ^ q)))) := by
    rw [← forwardCoreHistogramM_referenceMark_pairing U cap width n k q hkq,
      forwardCoreHistogramM_pairing U cap width n q
        (fun y => ndSyracuseUnitReferenceDensity k (Tao.taoZModThreeProjection hkq (-y)))]
  have heq : forwardCoreTerminalUnitMassM U cap width n K k X hX hi -
      forwardCoreMassM U cap width n k (fun _ => 1) =
      ∑ i, forwardCoreOuterWeightM U cap width n i *
        F ((forwardIterateM U cap n).fullTerminalShift X hX hi i)
          (-((((forwardIterateM U cap n).state.root i : ℕ)) : ZMod (3 ^ q))) := by
    rw [forwardCoreTerminalUnitMassM_eq_kernel U cap width n K k hk X hX hi, hmass,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hF]; ring
  rw [heq]
  refine hs.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_
    (coreCapacityBudgetM_nonneg U cap width n)) hu)
  exact_mod_cast (forwardIterateM U cap n).fullTerminalShiftImage_card_le
    ((rootSpanM_iff_rootSpan (forwardIterateM U cap n) e).mp he) X hX hi

end

end ThreeXMinusOne
