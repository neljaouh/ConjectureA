import ThreeXMinusOne.CoreMass

/-!
# The mass identity: `3x−1` core mass equals the artifact's backward mark

This is the step `CoreMass` was missing, and it needed one correction to that file's shape.

`coreMassM` accumulates its word filters back-to-front, because `iterateM` peels from the back.
`ndRootCoreBackwardMark` recurses front-to-first: the kernel sits at the *outer* floor `b` with
`cap 0`, wrapping the level-`n` object at floor `b + b/100` with `ndGeom2RootSideCapTail cap`.
`ForwardIterate` fixed the state, but not the accumulated factor — so `coreMassM_succ`, which is
a back step, cannot be fed to an induction that has to peel forwards.

The artifact's own remedy, which I had not read until I needed it, is that
`forwardCoreMarkedMass` carries a `theta : U.state.Label → ℝ`.  The successor step does not need
a back-peeling factor at all: it absorbs the first generation's filter into `theta`, replacing
`theta` by `theta' z = theta (ucLabelM z) * filter (ucWordM z)` and recursing on the child.  So
the accumulation lives in the argument, and the induction is `generalizing U cap theta`.

That is what this file does for `3x−1`.  Everything else is the seven-rung tower already built:
`MassKernel.sum_unitIncidenceM_mark_eq_filteredKernel` turns the child's sum back into a sum over
the parent's labels against `ndRootCoreFilteredKernel`, at the negated residue throughout.
-/

set_option maxHeartbeats 2000000

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

/-- The conductor only grows. -/
theorem le_backwardConductorM (b k : ℕ) : ∀ n, k ≤ ndRootCoreBackwardConductor b k n
  | 0 => le_refl k
  | n + 1 => le_trans (le_backwardConductorM (b + b / 100) k n) (Nat.le_add_left _ _)

/-- The parent label a level-`n` front-peeled label descends from. -/
def forwardAncestorM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) :
    (n : ℕ) → (forwardIterateM U cap n).state.Label → U.state.Label
  | 0, i => i
  | n + 1, z =>
      ucLabelM (forwardAncestorM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n z)

/-- The first-generation incidence a level-`(n+1)` label passes through. -/
def forwardFirstIncidenceM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (z : (forwardIterateM U cap (n + 1)).state.Label) :
    (nextFloorM U (cap 0)).state.Label :=
  forwardAncestorM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n z

/-- The accumulated word filter, peeled front-to-back to match the mark. -/
def forwardCoreFactorM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) : (n : ℕ) → (forwardIterateM U cap n).state.Label → ℝ
  | 0, _ => 1
  | n + 1, z =>
      ndRootCoreWordFilter U.floor (width U.floor) (ucWordM (forwardFirstIncidenceM U cap n z)) *
        forwardCoreFactorM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) width n z

/-- **The `3x−1` core-filtered marked mass**, read at the negated ternary residue. -/
def forwardCoreMassM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n k : ℕ) (theta : U.state.Label → ℝ) : ℝ := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  exact ∑ z, forwardCoreFactorM U cap width n z *
    (forwardIterateM U cap n).state.outerWeight z * theta (forwardAncestorM U cap n z) *
    ndSyracuseUnitReferenceDensity k
      (-(((forwardIterateM U cap n).state.root z : ℕ) : ZMod (3 ^ k)))

/-- **The mass identity.**  `n` generations of the `3x−1` construction, filtered by the
artifact's own word filter, weigh exactly what the artifact's backward mark predicts — read at
`-(root)` rather than `root`, which is the whole of the residue flip. -/
theorem forwardCoreMassM_eq_backwardMarkM
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ) (n k : ℕ)
    (hk : 1 ≤ k) (theta : U.state.Label → ℝ) :
    forwardCoreMassM U cap width n k theta =
      letI := U.state.labelFintype;
      ∑ i, U.state.outerWeight i * theta i *
        ndRootCoreBackwardMark U.floor cap width k n
          (-(((U.state.root i : ℕ)) : ZMod (3 ^ ndRootCoreBackwardConductor U.floor k n))) := by
  classical
  induction n generalizing U cap theta with
  | zero =>
      letI := U.state.labelFintype
      show (∑ z : U.state.Label, forwardCoreFactorM U cap width 0 z * U.state.outerWeight z *
        theta (forwardAncestorM U cap 0 z) *
        ndSyracuseUnitReferenceDensity k (-((U.state.root z : ℕ) : ZMod (3 ^ k)))) = _
      refine Fintype.sum_equiv (Equiv.refl _) _ _ ?_
      intro i
      simp only [Equiv.refl_apply, forwardCoreFactorM, forwardAncestorM,
        ndRootCoreBackwardMark, ndRootCoreBackwardConductor, one_mul]
      rfl
  | succ n ih =>
      letI := U.state.labelFintype
      set V := nextFloorM U (cap 0) with hV
      letI := V.state.labelFintype
      set ct := ndGeom2RootSideCapTail cap with hct
      set theta' : V.state.Label → ℝ := fun j =>
        theta (ucLabelM j) * ndRootCoreWordFilter U.floor (width U.floor) (ucWordM j) with htheta'
      -- Peel the first generation into `theta`.
      have hstep : forwardCoreMassM U cap width (n + 1) k theta =
          forwardCoreMassM V ct width n k theta' := by
        letI := (forwardIterateM V ct n).state.labelFintype
        show (∑ z : (forwardIterateM V ct n).state.Label, forwardCoreFactorM U cap width (n + 1) z *
          (forwardIterateM V ct n).state.outerWeight z *
          theta (forwardAncestorM U cap (n + 1) z) *
          ndSyracuseUnitReferenceDensity k
            (-(((forwardIterateM V ct n).state.root z : ℕ) : ZMod (3 ^ k)))) = _
        refine Fintype.sum_equiv (Equiv.refl _) _ _ ?_
        intro z
        simp only [Equiv.refl_apply, forwardCoreFactorM, forwardAncestorM,
          forwardFirstIncidenceM, forwardCoreMassM, theta', V, ct]
        ring
      rw [hstep, ih V ct theta']
      -- Fold the child's sum back onto the parent's labels.
      set q := ndRootCoreBackwardConductor V.floor k n with hq
      set g := ndRootCoreBackwardMark V.floor ct width k n with hg
      have hunit : ∀ N : ℕ, ¬ IsUnit ((N : ℕ) : ZMod (3 ^ 1)) →
          g ((N : ℕ) : ZMod (3 ^ q)) = 0 :=
        rootCoreBackwardMark_natCast_eq_zero_of_not_unit V.floor ct width hk n
      have hkey := sum_unitIncidenceM_mark_eq_filteredKernel
        (Labels := (Finset.univ : Finset U.state.Label)) (root := U.state.root)
        (b := U.floor) (a := ndGeom2ShiftedWideSymmetricShiftRadius U.floor) (K := cap 0)
        (fun i => U.state.outerWeight i * theta i) q U.state.root_odd
        (by have h := U.floor_twoHundred; omega)
        (fun i => (Nat.pow_le_pow_right (by norm_num)
          (U.floor_le_base i)).trans (U.state.rootLower i))
        (le_trans hk (by rw [hq]; exact le_backwardConductorM V.floor k n))
        (ndRootCoreWordFilter U.floor (width U.floor)) g hunit
      have hL : (∑ j : V.state.Label, V.state.outerWeight j * theta' j *
            g ((-((V.state.root j : ℕ) : ZMod (3 ^ q))))) =
          ∑ z : UnitChildIncidenceM (Finset.univ : Finset U.state.Label) U.state.root U.floor
                  (ndGeom2ShiftedWideSymmetricShiftRadius U.floor) (cap 0),
            ucWeightM (fun i => U.state.outerWeight i * theta i) z *
              ndRootCoreWordFilter U.floor (width U.floor) (ucWordM z) *
              g (-(((ucSourceM z : ℕ)) : ZMod (3 ^ q))) := by
        refine Fintype.sum_equiv (Equiv.refl (UnitChildIncidenceM
          (Finset.univ : Finset U.state.Label) U.state.root U.floor
          (ndGeom2ShiftedWideSymmetricShiftRadius U.floor) (cap 0))) _ _ ?_
        intro z
        simp only [Equiv.refl_apply, ucWeightM, ucAtomM, theta', V, nextFloorM, nextM,
          atomM, toPhysicalM_depth, toPhysicalM_word]
        ring
      rw [hL, hkey]
      refine (Finset.sum_subtype Finset.univ (fun _ => Iff.rfl) (fun i =>
        U.state.outerWeight i * theta i *
          ndRootCoreBackwardMark U.floor cap width k (n + 1)
            (-((U.state.root i : ℕ) :
              ZMod (3 ^ ndRootCoreBackwardConductor U.floor k (n + 1)))))).symm.trans ?_
      exact Finset.sum_congr rfl fun i _ => by
        simp only [ndRootCoreBackwardMark, ndRootCoreBackwardConductor]

end

end ThreeXMinusOne
