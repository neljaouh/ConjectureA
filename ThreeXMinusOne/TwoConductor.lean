import ThreeXMinusOne.SubweightFan
import ThreeXMinusOne.GoodMassFan

/-!
# The two-conductor bound on the good mass

`forwardGoodDepthShiftUnitMass_le_two_conductor_of_height_of_nonreturningSeed`, mirrored.

Layer 58 dominates the good mass by the fanned cap-one sum; Layer 60 bounds that by
`(4/3)·H·(total good weight)` plus a mixing discrepancy.  With `H = (2/3)·p` the leading constant
is `(8/9)·p`, exactly as on the `+1` side — the height enters identically, because the reference
density is the same function for both maps.

The additive term is `88·(excess·potential)·epsilon` where `+1` has `44·potential·epsilon`: a
factor two from the wider window (Layer 39) and the generation excess from the charge (Layer 37).
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

theorem forwardGoodDepthShiftUnitMassM_le_two_conductor_of_height
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ)
    (n K m k : ℕ) (hmk : m ≤ k)
    (hseed : ∀ i k, 0 < k → (syrM^[k]) (U.state.root i) ≠ U.state.root i)
    (X : ℝ) (hX : 0 < X) (hQ : ((3 ^ k : ℕ) : ℝ) ≤ X)
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i))
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hL1 : ndTernaryUniformMean k (fun y => |ndSyracuseUnitReferenceDensity k y -
      ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|) ≤ epsilon)
    (p : ℕ) (hp : 0 < p)
    (hheight : ∀ y, ndSyracuseUnitReferenceDensity m y ≤ (2 / 3 : ℝ) * (p : ℝ)) :
    forwardCoreTerminalGoodDepthShiftUnitMassM U cap width n K k X hX hi ≤
      (8 / 9 : ℝ) * (p : ℝ) * fullGoodCoreTerminalMassM U cap width n
        ((forwardIterateM U cap n).fullTerminalShift X hX hi) 1 +
        88 * (generationExcessProductM U cap (n + 1) * U.parentSourcePotential) * epsilon := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  refine (forwardGoodDepthShiftUnitMassM_le_cap_one_fan U cap width n K k X hX hi).trans ?_
  have hwin : ∀ z : FullTerminalAtM U cap n
      ((forwardIterateM U cap n).fullTerminalShift X hX hi) 1,
      X ≤ (sourceM z : ℝ) ∧ (sourceM z : ℝ) < 64 * X :=
    fun z => fullTerminalM_source_window (forwardIterateM U cap n) X hX hi z
  have h := fullTerminalM_subweight_fan_two_conductor_bound U cap n
    ((forwardIterateM U cap n).fullTerminalShift X hX hi) 1 (K / 2 + 1) hseed
    (fullGoodCoreTerminalWeightM U cap width n
      ((forwardIterateM U cap n).fullTerminalShift X hX hi) 1)
    (fullGoodCoreTerminalWeightM_nonneg U cap width n
      ((forwardIterateM U cap n).fullTerminalShift X hX hi) 1)
    (fullGoodCoreTerminalWeightM_le_original U cap width n
      ((forwardIterateM U cap n).fullTerminalShift X hX hi) 1)
    m k hmk X hX hQ hwin (forwardIterateM U cap n).state.root_odd
    epsilon he hL1 ((2 / 3 : ℝ) * (p : ℝ)) (by positivity) hheight
  refine h.trans (le_of_eq ?_)
  unfold fullGoodCoreTerminalMassM
  ring

end

end ThreeXMinusOne
