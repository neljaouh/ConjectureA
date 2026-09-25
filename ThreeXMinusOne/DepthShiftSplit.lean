import ThreeXMinusOne.SigmaBridge
import ThreeXMinusOne.CoreTerminalMass
import ThreeXMinusOne.GoodCoreCensus
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalDepthShiftMarkedLoss

/-!
# Splitting the terminal mass by the depth-shift band

`forwardCoreTerminalBadDepthShiftUnitMass`, its kernel form, and
`forwardCoreTerminalGoodDepthShiftUnitMass`, mirrored.

The terminal mass is split into the part whose depth sits in the band the chosen shift selects
and the part that does not.  The *bad* part is the loss term: the next layer bounds it, and what
survives is the good mass the count consumes.

`ndTerminalDepthShiftGood` and `ndTerminalDepthShiftBadFilter` are word-and-depth only — they
never see a root or a residue — so both are the artifact's own, used verbatim.

The kernel form is Layer 25 applied one packet at a time: `sum_unitIncidenceM_mark_eq_filteredKernel`
takes the word filter as a parameter, so the bad filter is just another instantiation, and the
result is read at `−(root)` as everywhere else on the minus side.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

private theorem good_mask_subM (p : Prop) [Decidable p] (x y : ℝ) :
    x * y - x * (if p then 0 else 1) * y = if p then x * y else 0 := by
  split_ifs <;> ring

private theorem good_fiber_subM {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (p : ∀ i, κ i → Prop) [∀ i z, Decidable (p i z)] (x y : ∀ i, κ i → ℝ) :
    (∑ i, ∑ z, x i z * y i z) - (∑ i, ∑ z, x i z * (if p i z then 0 else 1) * y i z) =
      ∑ i, ∑ z, if p i z then x i z * y i z else 0 := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun z _ => good_mask_subM _ _ _

variable (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ)
  (n K k : ℕ) (X : ℝ) (hX : 0 < X)

/-- The part of the terminal mass whose depth falls outside the band: the loss term. -/
def forwardCoreTerminalBadDepthShiftUnitMassM
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) : ℝ := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  exact ∑ i : (forwardIterateM U cap n).state.Label,
    ∑ z : UnitChildIncidenceM ({i} : Finset (forwardIterateM U cap n).state.Label)
      (forwardIterateM U cap n).state.root (forwardIterateM U cap n).floor
      ((forwardIterateM U cap n).fullTerminalShift X hX hi i) K,
      ucWeightM (forwardCoreOuterWeightM U cap width n) z *
        ndTerminalDepthShiftBadFilter (forwardIterateM U cap n).floor
          ((forwardIterateM U cap n).fullTerminalShift X hX hi i) (ucWordM z) *
        ndSyracuseUnitReferenceDensity k (-((ucSourceM z : ℕ) : ZMod (3 ^ k)))

/-- **The loss term as a kernel sum.**  Layer 25, one packet at a time. -/
theorem forwardCoreTerminalBadDepthShiftUnitMassM_eq_kernel (hk : 1 ≤ k)
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) :
    letI := (forwardIterateM U cap n).state.labelFintype
    forwardCoreTerminalBadDepthShiftUnitMassM U cap width n K k X hX hi =
      ∑ i : (forwardIterateM U cap n).state.Label,
        forwardCoreOuterWeightM U cap width n i *
          ndRootCoreFilteredKernel (forwardIterateM U cap n).floor
            ((forwardIterateM U cap n).fullTerminalShift X hX hi i) K k
            (ndTerminalDepthShiftBadFilter (forwardIterateM U cap n).floor
              ((forwardIterateM U cap n).fullTerminalShift X hX hi i))
            (ndSyracuseUnitReferenceDensity k)
            (-(((forwardIterateM U cap n).state.root i : ℕ) :
              ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon (forwardIterateM U cap n).floor
                + k)))) := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  unfold forwardCoreTerminalBadDepthShiftUnitMassM
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_unitIncidenceM_mark_eq_filteredKernel
    (Labels := ({i} : Finset (forwardIterateM U cap n).state.Label))
    (root := (forwardIterateM U cap n).state.root)
    (b := (forwardIterateM U cap n).floor)
    (a := (forwardIterateM U cap n).fullTerminalShift X hX hi i) (K := K)
    (forwardCoreOuterWeightM U cap width n) k
    (forwardIterateM U cap n).state.root_odd
    (by have h := (forwardIterateM U cap n).floor_twoHundred; omega)
    (fun j => (Nat.pow_le_pow_right (by norm_num)
      ((forwardIterateM U cap n).floor_le_base j)).trans
      ((forwardIterateM U cap n).state.rootLower j))
    hk
    (ndTerminalDepthShiftBadFilter (forwardIterateM U cap n).floor
      ((forwardIterateM U cap n).fullTerminalShift X hX hi i))
    (ndSyracuseUnitReferenceDensity k)
    (unitReferenceDensity_natCast_eq_zero_of_not_unit hk)]
  rw [← Finset.sum_subtype ({i} : Finset (forwardIterateM U cap n).state.Label)
    (fun _ => Iff.rfl)
    (fun j => forwardCoreOuterWeightM U cap width n j *
      ndRootCoreFilteredKernel (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).fullTerminalShift X hX hi i) K k
        (ndTerminalDepthShiftBadFilter (forwardIterateM U cap n).floor
          ((forwardIterateM U cap n).fullTerminalShift X hX hi i))
        (ndSyracuseUnitReferenceDensity k)
        (-(((forwardIterateM U cap n).state.root j : ℕ) :
          ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon (forwardIterateM U cap n).floor + k)))))]
  simp

/-- What survives the band. -/
def forwardCoreTerminalGoodDepthShiftUnitMassM
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) : ℝ :=
  forwardCoreTerminalUnitMassM U cap width n K k X hX hi -
    forwardCoreTerminalBadDepthShiftUnitMassM U cap width n K k X hX hi

theorem forwardCoreTerminalGoodDepthShiftUnitMassM_le_original
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) :
    forwardCoreTerminalGoodDepthShiftUnitMassM U cap width n K k X hX hi ≤
      forwardCoreTerminalUnitMassM U cap width n K k X hX hi := by
  classical
  apply sub_le_self
  letI := (forwardIterateM U cap n).state.labelFintype
  unfold forwardCoreTerminalBadDepthShiftUnitMassM
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun z _ => ?_
  exact mul_nonneg (mul_nonneg
    (mul_nonneg (forwardCoreOuterWeightM_nonneg U cap width n _) (by
      unfold ucAtomM; positivity))
    (terminalDepthShiftBadFilter_nonneg _ _ _))
    (ndSyracuseUnitReferenceDensity_nonneg _ _)

end

end ThreeXMinusOne
