import ThreeXMinusOne.NextState
import ThreeXMinusOne.Generations

/-!
# Iterating the `3x−1` child state

`NDGeom2ShiftedWideSymmetricRootSideUniformFloorState` carries only a floor, a proof that it is
at least `200`, and a proof that it is below every base — no map, no incidence — so the `3x−1`
generational construction is an inhabitant of the artifact's own wrapper.  Only the step changes,
from the artifact's `next` to `nextM`.

The floor recursion is `floor ↦ floor + floor/100`, identical to the `+1` one, so the artifact's
`explicitSeedFloor` and its bounds apply verbatim.  With `floor ≥ 200` that is a gain of at least
`2` per generation — exactly the hypothesis of `Generations.generation_product_le`, which is what
makes the accumulated `3x−1` excess a convergent geometric series rather than an unbounded
product.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

/-- One generation of the `3x−1` construction. -/
noncomputable def nextFloorM
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (K : ℕ) :
    NDGeom2ShiftedWideSymmetricRootSideUniformFloorState where
  state := nextM U.state U.floor K U.floor_twoHundred U.floor_le_base
  floor := U.floor + U.floor / 100
  floor_twoHundred := by have := U.floor_twoHundred; omega
  floor_le_base := fun z =>
    nextM_floor_add_oneHundredth_le_base U.state U.floor K
      U.floor_twoHundred U.floor_le_base z

@[simp] theorem nextFloorM_floor
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (K : ℕ) :
    (nextFloorM U K).floor = U.floor + U.floor / 100 := rfl

/-- `n` generations, with the cap schedule the artifact uses. -/
noncomputable def iterateM
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) :
    ℕ → NDGeom2ShiftedWideSymmetricRootSideUniformFloorState
  | 0 => U
  | n + 1 => nextFloorM (iterateM U cap n) (cap n)

@[simp] theorem iterateM_zero
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) :
    iterateM U cap 0 = U := rfl

@[simp] theorem iterateM_succ
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ) :
    iterateM U cap (n + 1) = nextFloorM (iterateM U cap n) (cap n) := rfl

theorem iterateM_floor_twoHundred
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ) :
    200 ≤ (iterateM U cap n).floor := (iterateM U cap n).floor_twoHundred

/-- **The floor gains at least `2` per generation.** -/
theorem iterateM_floor_step
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ) :
    (iterateM U cap n).floor + 2 ≤ (iterateM U cap (n + 1)).floor := by
  have h := iterateM_floor_twoHundred U cap n
  change (iterateM U cap n).floor + 2 ≤
    (iterateM U cap n).floor + (iterateM U cap n).floor / 100
  omega

/-- The hypothesis of `Generations.generation_product_le`, discharged. -/
theorem iterateM_floor_lower
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ) :
    200 + 2 * n ≤ (iterateM U cap n).floor :=
  floor_lower (fun k => (iterateM U cap k).floor)
    (iterateM_floor_twoHundred U cap 0) (iterateM_floor_step U cap) n

end ThreeXMinusOne
