import ThreeXMinusOne.LossBound
import ThreeXMinusOne.TerminalMajorant
import ThreeXMinusOne.Window
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalDepthShiftMarkedLoss

/-!
# The depth-shift loss, against a summable majorant

`forward_quarter_terminalBadDepthShiftUnitMass_le` and
`forward_terminalBadDepthShiftUnitMass_le_summable_majorant`, mirrored.

The third and last of the error terms.  Layer 57 bounded the loss by (image size) × (capacity
budget) × (an exponentially small kernel mean); here each factor is replaced by its geometric
majorant, exactly as Layer 68 did for the terminal error.

The same two shifts as Layer 68: the image factor reads `e + 1` rather than `e` because the minus
span budget grows by `cap + 4`, and the capacity budget carries `E`.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

/-- The quarter-conductor form of the loss bound. -/
theorem forward_quarter_terminalBadDepthShiftUnitMassM_le
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ)
    (e : ℕ) (he : rootSpanM U e) (n K : ℕ) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) :
    forwardCoreTerminalBadDepthShiftUnitMassM U cap width n K
        ((forwardIterateM U cap n).floor / 4) X hX hi ≤
      (rootSpanBudgetM e cap n + 1 : ℝ) * coreCapacityBudgetM U cap width n * ((2 / 3 : ℝ) *
        ((4 * ((forwardIterateM U cap n).floor : ℝ) + 4) *
          Real.exp (-((forwardIterateM U cap n).floor : ℝ) / 16384))) := by
  have hs : rootSpanM (forwardIterateM U cap n) (rootSpanBudgetM e cap n) := by
    simpa only [forwardIterateM_eq_iterateM] using iterateM_rootSpan U he cap n
  have hb := (forwardIterateM U cap n).floor_twoHundred
  have hq : ndGeom2ShiftedWideSymmetricHorizon (forwardIterateM U cap n).floor +
      (forwardIterateM U cap n).floor / 4 ≤ 2 * (forwardIterateM U cap n).floor := by
    unfold ndGeom2ShiftedWideSymmetricHorizon ndGeom2ShiftedWideSymmetricWidth
    omega
  exact forwardCoreTerminalBadDepthShiftUnitMassM_le U cap width n K _ _ hs (by omega) hq X hX hi

/-- **The loss, below `E ·` the `+1` majorant read at `e + 1`.** -/
theorem forward_terminalBadDepthShiftUnitMassM_le_summable_majorant
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (e L : ℕ)
    (he : rootSpanM U e) (hcap : ∀ n, cap n ≤ L * (n + 1)) (n K : ℕ) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) :
    forwardCoreTerminalBadDepthShiftUnitMassM U cap ndRootCoreWidth n K
        ((forwardIterateM U cap n).floor / 4) X hX hi ≤
      excessBound * (U.denominator *
        ndRootTerminalVariationMajorant U.floor (e + 1) L 0 0 n) := by
  have hfloor := forwardIterateM_floor_eq U cap n
  have hr := forward_quarter_terminalBadDepthShiftUnitMassM_le U cap ndRootCoreWidth e he n K
    X hX hi
  have hbudget := U.coreCapacityBudget_le_geometric cap L hcap n
  have herr := NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.terminalDepthShift_loss_le_existing_strip_constant
    (show 1 ≤ (forwardIterateM U cap n).floor by
      have := (forwardIterateM U cap n).floor_twoHundred; omega)
  have hi6 : 1 / ((forwardIterateM U cap n).floor : ℝ) ^ 6 ≤
      (1 / (U.floor : ℝ) ^ 6) * ((200 / 201 : ℝ) ^ 6) ^ n := by
    rw [hfloor]
    have hh := pow_le_pow_left₀
      (by positivity : (0 : ℝ) ≤ 1 / ((U.forwardIterate cap n).floor : ℝ))
      (U.core_inverse_floor_le_geometric cap n) 6
    simpa only [div_pow, one_pow, mul_pow, ← pow_mul, Nat.mul_comm] using hh
  have hh := mul_le_mul_of_nonneg_left hi6
    (by unfold ndRootCoreStripConstant; positivity : 0 ≤ ndRootCoreStripConstant)
  simp only [← mul_assoc, mul_one_div] at hh
  have her : (4 * ((forwardIterateM U cap n).floor : ℝ) + 4) *
      Real.exp (-((forwardIterateM U cap n).floor : ℝ) / 16384) ≤
      (ndRootCoreStripConstant / (U.floor : ℝ) ^ 6) * ((200 / 201 : ℝ) ^ 6) ^ n +
        ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n := by
    have hp : 0 ≤ ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n := by positivity
    linarith only [herr, hh, hp]
  have hspan : (rootSpanBudgetM e cap n + 1 : ℝ) ≤
      ((e + 1 + L + 4 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have hs := rootSpanBudgetM_le_quadratic e L cap hcap n
    have hn : rootSpanBudgetM e cap n + 1 ≤ (e + 1 + L + 4) * (n + 1) ^ 2 := by
      have hp : 1 ≤ (n + 1) ^ 2 := by
        simpa using Nat.pow_le_pow_left (show 1 ≤ n + 1 by omega) 2
      nlinarith only [hs, hp]
    exact_mod_cast hn
  have hD : 0 ≤ U.denominator := by
    classical
    letI := U.state.labelFintype
    exact Finset.sum_nonneg fun i _ => U.state.weight_nonneg i
  have hbM := (coreCapacityBudgetM_le U cap ndRootCoreWidth n).trans
    (mul_le_mul_of_nonneg_left hbudget excessBound_pos.le)
  have hrnn : (0 : ℝ) ≤ (2 / 3 : ℝ) *
      ((4 * ((forwardIterateM U cap n).floor : ℝ) + 4) *
        Real.exp (-((forwardIterateM U cap n).floor : ℝ) / 16384)) := by positivity
  have hBnn : (0 : ℝ) ≤ excessBound * (U.denominator *
      ((4 * (U.floor : ℝ) ^ (3 / 5 : ℝ) + 1) * (L + 5) *
        ((2 : ℝ) ^ (U.floor + 1) + (16 : ℝ) ^ U.floor)) *
      ((n + 1 : ℕ) : ℝ) ^ 3 * ndRootCoreGrowth ^ n) := by
    have hg : (0 : ℝ) ≤ ndRootCoreGrowth := by norm_num [ndRootCoreGrowth]
    have := excessBound_pos.le
    positivity
  have hRnn : (0 : ℝ) ≤ (2 / 3 : ℝ) *
      ((ndRootCoreStripConstant / (U.floor : ℝ) ^ 6) * ((200 / 201 : ℝ) ^ 6) ^ n +
        ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n) := by
    have : (0 : ℝ) ≤ ndRootCoreStripConstant := by unfold ndRootCoreStripConstant; positivity
    positivity
  refine hr.trans ?_
  refine le_trans (mul_le_mul (mul_le_mul hspan hbM
      (coreCapacityBudgetM_nonneg U cap ndRootCoreWidth n) (by positivity))
      (mul_le_mul_of_nonneg_left her (by norm_num)) hrnn
      (mul_nonneg (by positivity) hBnn)) (le_of_eq ?_)
  simp only [ndRootTerminalVariationMajorant, ndRootCoreVariationMajorant, mul_pow,
    pow_zero, one_mul]
  ring

end

end ThreeXMinusOne
