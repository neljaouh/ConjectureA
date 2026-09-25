import ThreeXMinusOne.UnitPhysicalMap
import ThreeXMinusOne.TerminalWindow
import ThreeXMinusOne.ForwardCoreMass

/-!
# The core terminal unit mass, and its cap-one fan bound

`forwardCoreTerminalUnitMass` and `forwardCoreTerminalUnitMass_le_full_cap_one_fan`, mirrored.

This is where the two halves meet.  The generational construction (Layers 16–30) delivers a
core-filtered mass over unit-child packets; the census (Layers 33–43) needs it as a sum over
physical cap-one incidences, so that Layer 39's window applies.  Layer 43 does the first step,
Layer 42 the second, and this file is their composition.

`forwardCoreOuterWeightM` is the `3x−1` counterpart of `forwardCoreOuterWeight`.  The `+1` version
is `if forwardCore … then outerWeight i else 0`; here it is `forwardCoreFactorM · outerWeight`,
the real-valued form Layer 29 adopted after the `Prop`-and-`if` encoding cost six builds.  The
two agree because the filter is `{0,1}`-valued, and the product form keeps every step algebraic.

The reference density is read at `−(source)`, matching Layer 30: the child's root *is* the
parent's incidence source, and the minus mark is read at the negated residue throughout.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

theorem forwardCoreFactorM_nonneg (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (z : (forwardIterateM U cap n).state.Label) :
    0 ≤ forwardCoreFactorM U cap width n z := by
  induction n generalizing U cap with
  | zero => norm_num [forwardCoreFactorM]
  | succ n ih =>
      exact mul_nonneg (rootCoreWordFilter_nonneg _ _ _) (ih _ _ _)

/-- The core-filtered outer weight: `+1` uses an `if`, we use the filter as a factor. -/
def forwardCoreOuterWeightM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (i : (forwardIterateM U cap n).state.Label) : ℝ :=
  forwardCoreFactorM U cap width n i * (forwardIterateM U cap n).state.outerWeight i

theorem forwardCoreOuterWeightM_nonneg (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (i : (forwardIterateM U cap n).state.Label) :
    0 ≤ forwardCoreOuterWeightM U cap width n i :=
  mul_nonneg (forwardCoreFactorM_nonneg U cap width n i)
    ((forwardIterateM U cap n).state.weight_nonneg i)

/-- The core-filtered terminal mass over a generation's unit-child packets. -/
def forwardCoreTerminalUnitMassM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K k : ℕ) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) : ℝ := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  exact ∑ z : Σ i : (forwardIterateM U cap n).state.Label,
      UnitChildIncidenceM ({i} : Finset (forwardIterateM U cap n).state.Label)
        (forwardIterateM U cap n).state.root (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).fullTerminalShift X hX hi i) K,
    ucWeightM (forwardCoreOuterWeightM U cap width n) z.2 *
      ndSyracuseUnitReferenceDensity k (-((ucSourceM z.2 : ℕ) : ZMod (3 ^ k)))

/-- The fanned cap-one bound, as its own definition so that both sides of the inequality
carry the label `Fintype` in the same spelling. -/
def coreTerminalFanBoundM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K k : ℕ) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) : ℝ := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  exact ∑ z : IncidenceM (forwardIterateM U cap n).state.Label
      (forwardIterateM U cap n).state.root
      (fun _ => (forwardIterateM U cap n).floor)
      ((forwardIterateM U cap n).fullTerminalShift X hX hi) 1,
    weightM (forwardCoreOuterWeightM U cap width n) z *
      ∑ j : Fin (K / 2 + 1), (1 / 4 : ℝ) ^ j.val *
        ndSyracuseUnitReferenceDensity k
          (-((sourceFanM j.val (sourceM z) : ℕ) : ZMod (3 ^ k)))

/-- **The core terminal mass is dominated by the fanned cap-one sum.** -/
theorem forwardCoreTerminalUnitMassM_le_cap_one_fan
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K k : ℕ) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) :
    forwardCoreTerminalUnitMassM U cap width n K k X hX hi ≤
      coreTerminalFanBoundM U cap width n K k X hX hi := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  set g : ℕ → ℝ := fun x => ndSyracuseUnitReferenceDensity k (-((x : ℕ) : ZMod (3 ^ k)))
    with hg_def
  have hg : ∀ x, 0 ≤ g x := fun x => ndSyracuseUnitReferenceDensity_nonneg _ _
  have hw := forwardCoreOuterWeightM_nonneg U cap width n
  have hr : ∀ i, 16 ^ (forwardIterateM U cap n).floor ≤ (forwardIterateM U cap n).state.root i :=
    fun i => (Nat.pow_le_pow_right (by norm_num)
      ((forwardIterateM U cap n).floor_le_base i)).trans
      ((forwardIterateM U cap n).state.rootLower i)
  have hb : 9 ≤ (forwardIterateM U cap n).floor := by
    have := (forwardIterateM U cap n).floor_twoHundred; omega
  have hfan := physical_terminal_depth_mark_le_cap_one_fanM
    (base := fun _ => (forwardIterateM U cap n).floor)
    (shift := (forwardIterateM U cap n).fullTerminalShift X hX hi) (K := K)
    (forwardIterateM U cap n).state.root_odd (fun _ => hb) hr
    (forwardCoreOuterWeightM U cap width n) hw (fun _ _ => (1 : ℝ))
    (fun _ _ => zero_le_one) g hg
  have hunit := singleton_unit_terminal_depth_mark_le_physicalM
    (forwardIterateM U cap n).state.root
    ((forwardIterateM U cap n).fullTerminalShift X hX hi) (forwardIterateM U cap n).floor K
    (forwardIterateM U cap n).state.root_odd hb hr
    (forwardCoreOuterWeightM U cap width n) hw (fun _ _ => (1 : ℝ))
    (fun _ _ => zero_le_one) g hg
  simp only [mul_one, hg_def] at hfan hunit
  unfold forwardCoreTerminalUnitMassM coreTerminalFanBoundM
  exact hunit.trans hfan

end

end ThreeXMinusOne
