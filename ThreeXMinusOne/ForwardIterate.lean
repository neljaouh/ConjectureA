import ThreeXMinusOne.IterateState
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideHistoryInjectivity

/-!
# Front-peeling the `3x−1` iterate

A correction to `IterateState`.

`iterateM` peels from the **back**: `iterateM U cap (n+1) = nextFloorM (iterateM U cap n) (cap n)`.
That is the natural reading, and it is what made `MarkedMass.massM_succ` relate generation `n+1`
to generation `n` directly.  But it is the wrong direction to meet the artifact:
`ndRootCoreBackwardMark` and `forwardCore` both peel from the **front** — kernel at the outer
floor `b` with `cap 0`, wrapping the level-`n` object for child floor `b + b/100` with
`ndGeom2RootSideCapTail cap`.

The two orders apply the same caps in the same sequence, so they agree propositionally, but not
definitionally — which is why `massM_succ` came out with the kernel at the *innermost* floor and
does not slot into the mark recursion as written.

The artifact hits this too and carries both forms plus a reconciling lemma
(`iterate_succ_eq_tail`, `forwardIterate_eq_iterate`).  This is that pair for `3x−1`.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

theorem iterateM_succ_eq_tail (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    iterateM U cap (n + 1) =
      iterateM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change nextFloorM (iterateM U cap (n + 1)) (cap (n + 1)) =
        nextFloorM (iterateM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n) (cap (n + 1))
      exact congrArg (fun V => nextFloorM V (cap (n + 1))) ih

/-- The front-peeling iterate, matching the recursion of `ndRootCoreBackwardMark`. -/
noncomputable def forwardIterateM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) : ℕ → NDGeom2ShiftedWideSymmetricRootSideUniformFloorState
  | 0 => U
  | n + 1 => forwardIterateM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n

/-- **The two orders agree.** -/
theorem forwardIterateM_eq_iterateM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) : forwardIterateM U cap n = iterateM U cap n := by
  induction n generalizing U cap with
  | zero => rfl
  | succ n ih =>
      simp only [forwardIterateM, ih]
      exact (iterateM_succ_eq_tail U cap n).symm

@[simp] theorem forwardIterateM_zero (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) : forwardIterateM U cap 0 = U := rfl

@[simp] theorem forwardIterateM_succ (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    forwardIterateM U cap (n + 1) =
      forwardIterateM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n := rfl

/-- Floor growth transports to the front-peeling form. -/
theorem forwardIterateM_floor_lower (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) : 200 + 2 * n ≤ (forwardIterateM U cap n).floor := by
  rw [forwardIterateM_eq_iterateM]
  exact iterateM_floor_lower U cap n

end

end ThreeXMinusOne
