import ThreeXMinusOne.IterateState
import ThreeXMinusOne.MassKernel
import ThreeXMinusOne.Seed

/-!
# The marked mass of the `3x−1` iterate

The composition step.  `MassKernel` identified the sum over minus unit-child incidences with the
artifact's filtered kernel at `-(root)`.  `IterateState` built the generational iterate.  This
puts them together: the marked mass at generation `n+1` is the kernel applied to the marked data
of generation `n`, which is exactly the recursion `ndRootCoreBackwardMark` obeys.

The reference density is read at `-(root z)` throughout, because that is where `MassKernel`
leaves it and where `Seed` supplies the artifact's lower bound.

The two facts that make the step go through are definitional consequences of how `nextM` was
built in `NextState`: the labels of generation `n+1` *are* the unit-child incidences of
generation `n`, its roots *are* their sources, and its outer weight *is* the parent's weight
times the incidence atom.  So no transport of data across the generation boundary is needed —
the plus development's `forwardLastIncidenceEquiv` is `rfl` here.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

/-- The marked mass of the `3x−1` iterate at generation `n`, read at the negated residue. -/
def massM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n k : ℕ) : ℝ := by
  classical
  letI := (iterateM U cap n).state.labelFintype
  exact ∑ z, (iterateM U cap n).state.outerWeight z *
    ndSyracuseUnitReferenceDensity k
      (-((((iterateM U cap n).state.root z : ℕ)) : ZMod (3 ^ k)))

/-! ### Projections of the successor generation

These are `rfl`, but stating them keeps the elaborator from unfolding `iterateM` through
`nextFloorM` to `nextM` at every use — which is what made the first attempt at `massM_succ` time
out in `whnf`. -/

theorem iterateM_succ_root (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (x : (iterateM U cap (n + 1)).state.Label) :
    (iterateM U cap (n + 1)).state.root x = ucSourceM x := rfl

theorem iterateM_succ_weight (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (x : (iterateM U cap (n + 1)).state.Label) :
    (iterateM U cap (n + 1)).state.outerWeight x =
      (iterateM U cap n).state.outerWeight (ucLabelM x) * atomM (toPhysicalM x) := rfl

set_option maxHeartbeats 1000000 in
/-- **The composition step.**  One generation of the `3x−1` marked mass is the artifact's
filtered kernel applied at the negated residues of the previous generation. -/
theorem massM_succ (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n k : ℕ) (hk : 1 ≤ k) :
    massM U cap (n + 1) k =
      letI := (iterateM U cap n).state.labelFintype;
      ∑ i, (iterateM U cap n).state.outerWeight i *
        ndRootCoreFilteredKernel (iterateM U cap n).floor
          (ndGeom2ShiftedWideSymmetricShiftRadius (iterateM U cap n).floor) (cap n) k
          (fun _ => (1 : ℝ)) (ndSyracuseUnitReferenceDensity k)
          (-((((iterateM U cap n).state.root i : ℕ)) :
            ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon (iterateM U cap n).floor + k)))) := by
  classical
  letI := (iterateM U cap n).state.labelFintype
  have hunit : ∀ n' : ℕ, ¬ IsUnit ((n' : ℕ) : ZMod (3 ^ 1)) →
      ndSyracuseUnitReferenceDensity k ((n' : ℕ) : ZMod (3 ^ k)) = 0 :=
    fun n' hn' => unitReferenceDensity_natCast_eq_zero_of_not_unit hk n' hn'
  have hkey := sum_unitIncidenceM_mark_eq_filteredKernel
    (Labels := (Finset.univ : Finset (iterateM U cap n).state.Label))
    (root := (iterateM U cap n).state.root)
    (b := (iterateM U cap n).floor)
    (a := ndGeom2ShiftedWideSymmetricShiftRadius (iterateM U cap n).floor)
    (K := cap n)
    (iterateM U cap n).state.outerWeight k
    (iterateM U cap n).state.root_odd
    (by have h := (iterateM U cap n).floor_twoHundred; omega)
    (fun i => (Nat.pow_le_pow_right (by norm_num)
      ((iterateM U cap n).floor_le_base i)).trans ((iterateM U cap n).state.rootLower i))
    hk (fun _ => (1 : ℝ)) (ndSyracuseUnitReferenceDensity k) hunit
  letI := (iterateM U cap (n + 1)).state.labelFintype
  have hL : massM U cap (n + 1) k =
      ∑ x : UnitChildIncidenceM (Finset.univ : Finset (iterateM U cap n).state.Label)
              (iterateM U cap n).state.root (iterateM U cap n).floor
              (ndGeom2ShiftedWideSymmetricShiftRadius (iterateM U cap n).floor) (cap n),
        ucWeightM (iterateM U cap n).state.outerWeight x * (1 : ℝ) *
          ndSyracuseUnitReferenceDensity k (-(((ucSourceM x : ℕ)) : ZMod (3 ^ k))) := by
    refine Fintype.sum_equiv (Equiv.refl _) _ _ ?_
    intro x
    simp only [Equiv.refl_apply, ucWeightM, ucAtomM, mul_one,
      iterateM_succ_root, iterateM_succ_weight, atomM,
      toPhysicalM_depth, toPhysicalM_word]
  have hR : (∑ i : {i : (iterateM U cap n).state.Label // i ∈ (Finset.univ : Finset _)},
        (iterateM U cap n).state.outerWeight i.val *
          ndRootCoreFilteredKernel (iterateM U cap n).floor
            (ndGeom2ShiftedWideSymmetricShiftRadius (iterateM U cap n).floor) (cap n) k
            (fun _ => (1 : ℝ)) (ndSyracuseUnitReferenceDensity k)
            (-(((iterateM U cap n).state.root i.val : ℕ) :
              ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon (iterateM U cap n).floor + k))))) =
      ∑ i, (iterateM U cap n).state.outerWeight i *
        ndRootCoreFilteredKernel (iterateM U cap n).floor
          (ndGeom2ShiftedWideSymmetricShiftRadius (iterateM U cap n).floor) (cap n) k
          (fun _ => (1 : ℝ)) (ndSyracuseUnitReferenceDensity k)
          (-(((iterateM U cap n).state.root i : ℕ) :
            ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon (iterateM U cap n).floor + k)))) :=
    Fintype.sum_equiv (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x)) _ _ (fun _ => rfl)
  rw [hL, hkey, hR]

end

end ThreeXMinusOne
