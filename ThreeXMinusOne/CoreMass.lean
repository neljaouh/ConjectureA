import ThreeXMinusOne.MarkedMass
import ThreeXMinusOne.ForwardIterate

/-!
# The word filter, and the core-filtered mass

The bridge `MarkedMass` was missing.  `massM` carries `psi ≡ 1`, whereas
`ndRootCoreBackwardMark` carries `ndRootCoreWordFilter`, and that filter is how the mixing input
enters the argument.

`ndRootCoreWordFilter b m w = if b ≤ w.length + m ∧ w.length ≤ b + m then 1 else 0` is a depth
band on the word — word-only and residue-blind, so like the crossing and overshoot predicates it
needs no porting.  What is needed is the accumulated filter on the minus iterate, and the
observation that `MassKernel` already takes `psi` as a parameter, so the filtered mass is an
instantiation rather than a new development.

The filter is carried as a **real-valued factor** rather than a `Prop` with an `if`.  It is
already `{0,1}`-valued, so nothing is lost, and the generation step becomes pure algebra: no case
analysis, and in particular none of the `split_ifs` branch-naming that a `Prop` formulation
forces.
-/

set_option maxHeartbeats 2000000

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

/-- The accumulated word filter along the minus iterate, real-valued. -/
def coreFactorM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ) :
    (n : ℕ) → (iterateM U cap n).state.Label → ℝ
  | 0, _ => 1
  | n + 1, z =>
      ndRootCoreWordFilter (iterateM U cap n).floor (width (iterateM U cap n).floor)
          (ucWordM z) *
        coreFactorM U cap width n (ucLabelM z)

/-- The core-filtered marked mass, read at the negated residue. -/
def coreMassM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n k : ℕ) : ℝ := by
  classical
  letI := (iterateM U cap n).state.labelFintype
  exact ∑ z, coreFactorM U cap width n z * (iterateM U cap n).state.outerWeight z *
    ndSyracuseUnitReferenceDensity k
      (-(((iterateM U cap n).state.root z : ℕ) : ZMod (3 ^ k)))

/-- **The filtered generation step.**  The word filter is the artifact's own
`ndRootCoreWordFilter`, which is what `ndRootCoreBackwardMark` carries. -/
theorem coreMassM_succ (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n k : ℕ) (hk : 1 ≤ k) :
    coreMassM U cap width (n + 1) k =
      letI := (iterateM U cap n).state.labelFintype;
      ∑ i, (coreFactorM U cap width n i * (iterateM U cap n).state.outerWeight i) *
        ndRootCoreFilteredKernel (iterateM U cap n).floor
          (ndGeom2ShiftedWideSymmetricShiftRadius (iterateM U cap n).floor) (cap n) k
          (ndRootCoreWordFilter (iterateM U cap n).floor (width (iterateM U cap n).floor))
          (ndSyracuseUnitReferenceDensity k)
          (-((((iterateM U cap n).state.root i : ℕ)) :
            ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon (iterateM U cap n).floor + k)))) := by
  classical
  letI := (iterateM U cap n).state.labelFintype
  letI := (iterateM U cap (n + 1)).state.labelFintype
  have hunit : ∀ n' : ℕ, ¬ IsUnit ((n' : ℕ) : ZMod (3 ^ 1)) →
      ndSyracuseUnitReferenceDensity k ((n' : ℕ) : ZMod (3 ^ k)) = 0 :=
    fun n' hn' => unitReferenceDensity_natCast_eq_zero_of_not_unit hk n' hn'
  have hkey := sum_unitIncidenceM_mark_eq_filteredKernel
    (Labels := (Finset.univ : Finset (iterateM U cap n).state.Label))
    (root := (iterateM U cap n).state.root)
    (b := (iterateM U cap n).floor)
    (a := ndGeom2ShiftedWideSymmetricShiftRadius (iterateM U cap n).floor)
    (K := cap n)
    (fun i => coreFactorM U cap width n i * (iterateM U cap n).state.outerWeight i) k
    (iterateM U cap n).state.root_odd
    (by have h := (iterateM U cap n).floor_twoHundred; omega)
    (fun i => (Nat.pow_le_pow_right (by norm_num)
      ((iterateM U cap n).floor_le_base i)).trans ((iterateM U cap n).state.rootLower i))
    hk (ndRootCoreWordFilter (iterateM U cap n).floor (width (iterateM U cap n).floor))
    (ndSyracuseUnitReferenceDensity k) hunit
  have hL : coreMassM U cap width (n + 1) k =
      ∑ x : UnitChildIncidenceM (Finset.univ : Finset (iterateM U cap n).state.Label)
              (iterateM U cap n).state.root (iterateM U cap n).floor
              (ndGeom2ShiftedWideSymmetricShiftRadius (iterateM U cap n).floor) (cap n),
        ucWeightM
            (fun i => coreFactorM U cap width n i * (iterateM U cap n).state.outerWeight i) x *
          ndRootCoreWordFilter (iterateM U cap n).floor
            (width (iterateM U cap n).floor) (ucWordM x) *
          ndSyracuseUnitReferenceDensity k (-(((ucSourceM x : ℕ)) : ZMod (3 ^ k))) := by
    refine Fintype.sum_equiv (Equiv.refl _) _ _ ?_
    intro x
    simp only [Equiv.refl_apply, coreMassM, ucWeightM, ucAtomM, coreFactorM,
      iterateM_succ_root, iterateM_succ_weight, atomM,
      toPhysicalM_depth, toPhysicalM_word]
    ring
  have hR : (∑ i : {i : (iterateM U cap n).state.Label // i ∈ (Finset.univ : Finset _)},
        (coreFactorM U cap width n i.val * (iterateM U cap n).state.outerWeight i.val) *
          ndRootCoreFilteredKernel (iterateM U cap n).floor
            (ndGeom2ShiftedWideSymmetricShiftRadius (iterateM U cap n).floor) (cap n) k
            (ndRootCoreWordFilter (iterateM U cap n).floor (width (iterateM U cap n).floor))
            (ndSyracuseUnitReferenceDensity k)
            (-(((iterateM U cap n).state.root i.val : ℕ) :
              ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon (iterateM U cap n).floor + k))))) =
      ∑ i, (coreFactorM U cap width n i * (iterateM U cap n).state.outerWeight i) *
        ndRootCoreFilteredKernel (iterateM U cap n).floor
          (ndGeom2ShiftedWideSymmetricShiftRadius (iterateM U cap n).floor) (cap n) k
          (ndRootCoreWordFilter (iterateM U cap n).floor (width (iterateM U cap n).floor))
          (ndSyracuseUnitReferenceDensity k)
          (-(((iterateM U cap n).state.root i : ℕ) :
            ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon (iterateM U cap n).floor + k)))) :=
    Fintype.sum_equiv (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x)) _ _ (fun _ => rfl)
  rw [hL, hkey, hR]

end

end ThreeXMinusOne
