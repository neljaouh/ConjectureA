import ThreeXMinusOne.LossBound
import ThreeXMinusOne.SigmaBridge

/-!
# The good mass as a filtered sum, and its cap-one fan bound

`forwardCoreTerminalGoodDepthShiftUnitMass_eq_sum` and
`forwardGoodDepthShiftUnitMass_le_full_cap_one_fan`, mirrored.

The good mass was defined as a difference (total minus loss).  To feed it to Layers 42–43 it has
to be a single filtered sum, and it is: the bad filter is `1 − indicator`, so
`W·g − W·(1−indicator)·g = W·indicator·g` pointwise.  That makes the good mass exactly the
weighted mark that `singleton_unit_terminal_depth_mark_le_physicalM` consumes, with the
depth-shift indicator as its `psi`.

Layer 48's bridge does the bookkeeping: the total is defined as a `Σ`-sum and the loss as a
double sum, and the two forms have to meet here.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

variable (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ)
  (n K k : ℕ) (X : ℝ) (hX : 0 < X)

/-- The good mass as a single weighted mark, with the indicator as `psi`. -/
theorem forwardCoreTerminalGoodDepthShiftUnitMassM_eq_sigma
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) :
    letI := (forwardIterateM U cap n).state.labelFintype
    forwardCoreTerminalGoodDepthShiftUnitMassM U cap width n K k X hX hi =
      ∑ z : Σ i : (forwardIterateM U cap n).state.Label,
          UnitChildIncidenceM ({i} : Finset (forwardIterateM U cap n).state.Label)
            (forwardIterateM U cap n).state.root (forwardIterateM U cap n).floor
            ((forwardIterateM U cap n).fullTerminalShift X hX hi i) K,
        ucWeightM (forwardCoreOuterWeightM U cap width n) z.2 *
          ndTerminalDepthShiftIndicator (forwardIterateM U cap n).floor
            ((forwardIterateM U cap n).fullTerminalShift X hX hi z.1) (ucDepthM z.2) *
          ndSyracuseUnitReferenceDensity k (-((ucSourceM z.2 : ℕ) : ZMod (3 ^ k))) := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  unfold forwardCoreTerminalGoodDepthShiftUnitMassM forwardCoreTerminalUnitMassM
    forwardCoreTerminalBadDepthShiftUnitMassM
  rw [← sum_sigma_packetM ((forwardIterateM U cap n).fullTerminalShift X hX hi)
    (forwardIterateM U cap n).floor K
    (fun i z => ucWeightM (forwardCoreOuterWeightM U cap width n) z *
      ndTerminalDepthShiftBadFilter (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).fullTerminalShift X hX hi i) (ucWordM z) *
      ndSyracuseUnitReferenceDensity k (-((ucSourceM z : ℕ) : ZMod (3 ^ k))))]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold ndTerminalDepthShiftBadFilter ndTerminalDepthShiftIndicator
  rw [ucWordM_length]
  split_ifs <;> ring

/-- **The good mass is dominated by the fanned cap-one sum.** -/
theorem forwardGoodDepthShiftUnitMassM_le_cap_one_fan
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) :
    letI := (forwardIterateM U cap n).state.labelFintype
    forwardCoreTerminalGoodDepthShiftUnitMassM U cap width n K k X hX hi ≤
      ∑ z : IncidenceM (forwardIterateM U cap n).state.Label
          (forwardIterateM U cap n).state.root
          (fun _ => (forwardIterateM U cap n).floor)
          ((forwardIterateM U cap n).fullTerminalShift X hX hi) 1,
        fullGoodCoreTerminalWeightM U cap width n
            ((forwardIterateM U cap n).fullTerminalShift X hX hi) 1 z *
          ∑ j : Fin (K / 2 + 1), (1 / 4 : ℝ) ^ j.val *
            ndSyracuseUnitReferenceDensity k
              (-((sourceFanM j.val (sourceM z) : ℕ) : ZMod (3 ^ k))) := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  set psi : (forwardIterateM U cap n).state.Label → ℕ → ℝ := fun i s =>
    ndTerminalDepthShiftIndicator (forwardIterateM U cap n).floor
      ((forwardIterateM U cap n).fullTerminalShift X hX hi i) s with hpsi
  set g : ℕ → ℝ := fun x => ndSyracuseUnitReferenceDensity k (-((x : ℕ) : ZMod (3 ^ k)))
    with hgdef
  have hg : ∀ x, 0 ≤ g x := fun x => ndSyracuseUnitReferenceDensity_nonneg _ _
  have hp : ∀ i s, 0 ≤ psi i s := fun _ _ => terminalDepthShiftIndicator_nonneg _ _ _
  have hw := forwardCoreOuterWeightM_nonneg U cap width n
  have hr : ∀ i, 16 ^ (forwardIterateM U cap n).floor ≤ (forwardIterateM U cap n).state.root i :=
    fun i => (Nat.pow_le_pow_right (by norm_num)
      ((forwardIterateM U cap n).floor_le_base i)).trans
      ((forwardIterateM U cap n).state.rootLower i)
  have hb : 9 ≤ (forwardIterateM U cap n).floor := by
    have := (forwardIterateM U cap n).floor_twoHundred; omega
  have hunit := singleton_unit_terminal_depth_mark_le_physicalM
    (forwardIterateM U cap n).state.root
    ((forwardIterateM U cap n).fullTerminalShift X hX hi) (forwardIterateM U cap n).floor K
    (forwardIterateM U cap n).state.root_odd hb hr
    (forwardCoreOuterWeightM U cap width n) hw psi hp g hg
  have hfan := physical_terminal_depth_mark_le_cap_one_fanM
    (base := fun _ => (forwardIterateM U cap n).floor)
    (shift := (forwardIterateM U cap n).fullTerminalShift X hX hi) (K := K)
    (forwardIterateM U cap n).state.root_odd (fun _ => hb) hr
    (forwardCoreOuterWeightM U cap width n) hw psi hp g hg
  rw [forwardCoreTerminalGoodDepthShiftUnitMassM_eq_sigma U cap width n K k X hX hi]
  refine (hunit.trans hfan).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold fullGoodCoreTerminalWeightM weightM
  simp only [hpsi, hgdef]

end

end ThreeXMinusOne
