import ThreeXMinusOne.CoreCapacity
import ThreeXMinusOne.TerminalCharge
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricCoreSummedVariation

/-!
# The budget bridge

The `+1` development spends a long chain of purely numeric estimates on its capacity budget —
geometric bounds on the width sums, the cap sums, the floor growth and hence on the budget
itself, culminating in a summable variation majorant.  None of that mentions a map.

This file makes all of it available to `3x−1` at once, by showing the minus budget differs from
the `+1` budget by at most the *same* absolute factor that has appeared three times already:

    coreCapacityBudgetM ≤ exp(3·(9/16)^200·256/175) · coreCapacityBudget,

which is `(1 + 4.6 × 10^(-50)) ·` the `+1` budget.

The bridge rests on three identities that are true because the two constructions share their
floor recursion `floor ↦ floor + floor/100`: the accumulated width sums agree, the accumulated
base sums agree, and the two iterates have the same floor at every generation.  Each is a two-line
induction — the *states* differ completely, but every quantity these budgets are built from reads
only the floor.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

/-- The absolute generation-excess constant (Layer 37). -/
def excessBound : ℝ := Real.exp (3 * (9 / 16 : ℝ) ^ 200 * (256 / 175 : ℝ))

theorem excessBound_pos : 0 < excessBound := Real.exp_pos _

theorem one_le_excessBound : (1 : ℝ) ≤ excessBound := Real.one_le_exp (by positivity)

/-- The floor recursion, extracted: it is all these quantities read. -/
def floorIterM : ℕ → ℕ → ℕ
  | b, 0 => b
  | b, n + 1 => floorIterM (b + b / 100) n

theorem floorIterM_twoHundred {b : ℕ} (hb : 200 ≤ b) (n : ℕ) : 200 ≤ floorIterM b n := by
  induction n generalizing b with
  | zero => exact hb
  | succ n ih => exact ih (by omega)

theorem nextPlus_floor (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (K : ℕ) :
    (U.next K).floor = U.floor + U.floor / 100 := rfl

theorem forwardIterateM_floor_eq_iter (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) : (forwardIterateM U cap n).floor = floorIterM U.floor n := by
  induction n generalizing U cap with
  | zero => rfl
  | succ n ih =>
      change (forwardIterateM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n).floor = _
      rw [ih]
      rfl

theorem forwardIteratePlus_floor_eq_iter
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ) :
    (U.forwardIterate cap n).floor = floorIterM U.floor n := by
  induction n generalizing U cap with
  | zero => rfl
  | succ n ih =>
      change ((U.next (cap 0)).forwardIterate (ndGeom2RootSideCapTail cap) n).floor = _
      rw [ih, nextPlus_floor]
      rfl

/-- Both iterates have the same floor: the recursion is `floor ↦ floor + floor/100` either way. -/
theorem forwardIterateM_floor_eq (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    (forwardIterateM U cap n).floor = (U.forwardIterate cap n).floor := by
  rw [forwardIterateM_floor_eq_iter, forwardIteratePlus_floor_eq_iter]

/-- The accumulated width sum, as a pure floor recursion. -/
def widthSumIterM (width : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _b, 0 => 0
  | b, n + 1 => width b + widthSumIterM width (b + b / 100) n

theorem coreWidthSumM_eq_iter (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) :
    coreWidthSumM U cap width n = widthSumIterM width U.floor n := by
  induction n generalizing U cap with
  | zero => rfl
  | succ n ih =>
      change width U.floor + coreWidthSumM (nextFloorM U (cap 0))
        (ndGeom2RootSideCapTail cap) width n = _
      rw [ih]
      rfl

theorem coreWidthSumPlus_eq_iter (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) :
    U.coreWidthSum cap width n = widthSumIterM width U.floor n := by
  induction n generalizing U cap with
  | zero => rfl
  | succ n ih =>
      change width U.floor + (U.next (cap 0)).coreWidthSum (ndGeom2RootSideCapTail cap) width n = _
      rw [ih, nextPlus_floor]
      rfl

theorem coreWidthSumM_eq (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) :
    coreWidthSumM U cap width n = U.coreWidthSum cap width n := by
  rw [coreWidthSumM_eq_iter, coreWidthSumPlus_eq_iter]

/-- The accumulated base sum, as a pure floor recursion. -/
def baseSumIterM : ℕ → ℕ → ℕ
  | _b, 0 => 0
  | b, n + 1 => b + baseSumIterM (b + b / 100) n

theorem coreBaseSumM_eq_iter (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) : coreBaseSumM U cap n = baseSumIterM U.floor n := by
  induction n generalizing U cap with
  | zero => rfl
  | succ n ih =>
      change U.floor + coreBaseSumM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n = _
      rw [ih]
      rfl

theorem coreBaseSumPlus_eq_iter (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) : U.coreBaseSum cap n = baseSumIterM U.floor n := by
  induction n generalizing U cap with
  | zero => rfl
  | succ n ih =>
      change U.floor + (U.next (cap 0)).coreBaseSum (ndGeom2RootSideCapTail cap) n = _
      rw [ih, nextPlus_floor]
      rfl

theorem coreBaseSumM_eq (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) : coreBaseSumM U cap n = U.coreBaseSum cap n := by
  rw [coreBaseSumM_eq_iter, coreBaseSumPlus_eq_iter]

theorem denominatorM_eq (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) :
    denominatorM U = U.denominator := rfl

/-- **The bridge.**  The minus budget is the `+1` budget up to the absolute constant of
Layer 37. -/
theorem coreCapacityBudgetM_le (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) :
    coreCapacityBudgetM U cap width n ≤ excessBound * U.coreCapacityBudget cap width n := by
  unfold excessBound
  have hE : generationExcessProductM U cap n ≤
      Real.exp (3 * (9 / 16 : ℝ) ^ 200 * (256 / 175 : ℝ)) := generationExcessProductM_le U cap n
  have hE1 : (1 : ℝ) ≤ Real.exp (3 * (9 / 16 : ℝ) ^ 200 * (256 / 175 : ℝ)) :=
    Real.one_le_exp (by positivity)
  have hD : 0 ≤ U.denominator := by
    classical
    letI := U.state.labelFintype
    exact Finset.sum_nonneg fun i _ => U.state.weight_nonneg i
  unfold coreCapacityBudgetM NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.coreCapacityBudget
  rw [denominatorM_eq, coreWidthSumM_eq, forwardIterateM_floor_eq]
  set E := Real.exp (3 * (9 / 16 : ℝ) ^ 200 * (256 / 175 : ℝ)) with hEdef
  set c : ℝ := (((2 * U.coreWidthSum cap width n + 1) *
    (ndRootCoreCapSum cap n + 4 * n + 1) : ℕ) : ℝ) with hc
  have hcnn : 0 ≤ c := by rw [hc]; positivity
  have hgeo : (0 : ℝ) ≤ (16 : ℝ) ^ U.floor * (9 / 16 : ℝ) ^ (U.forwardIterate cap n).floor := by
    positivity
  have htwo : (0 : ℝ) ≤ (2 : ℝ) ^ (U.floor + 1) := by positivity
  have hlast : (2 : ℝ) ^ (U.floor + 1) +
      generationExcessProductM U cap n * (16 : ℝ) ^ U.floor *
        (9 / 16 : ℝ) ^ (U.forwardIterate cap n).floor ≤
      E * ((2 : ℝ) ^ (U.floor + 1) +
        (16 : ℝ) ^ U.floor * (9 / 16 : ℝ) ^ (U.forwardIterate cap n).floor) := by
    nlinarith only [hE, hE1, hgeo, htwo]
  have hlnn : 0 ≤ (2 : ℝ) ^ (U.floor + 1) +
      generationExcessProductM U cap n * (16 : ℝ) ^ U.floor *
        (9 / 16 : ℝ) ^ (U.forwardIterate cap n).floor := by
    have := generationExcessProductM_nonneg U cap n
    positivity
  nlinarith only [hlast, hD, hcnn, hlnn, mul_nonneg hD hcnn]

end

end ThreeXMinusOne
