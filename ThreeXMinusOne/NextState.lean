import ThreeXMinusOne.UnitChild
import ThreeXMinusOne.FloorGrowth

/-!
# The `3x−1` child state

`NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorUnitNext`, mirrored.

This is the construction the whole generational argument runs on: the child's labels *are*
unit-child incidences of the parent, its roots are the incidence sources, and its base is the
dyadic base of those sources.  The artifact's structure is map-agnostic, so the `3x−1` child is
an inhabitant of the very same structure; what changes is only that the labels are
`UnitChildIncidenceM` — the artifact's word finsets read at the negated residue.

Three of the four non-trivial fields are already in hand: `root_odd` from `UnitChild`,
`base_eq` by definition, and `base_twoHundred` from `FloorGrowth`.  The floor consequently gains
at least `b/100` per generation, which is precisely what `Generations.generation_product_le`
needs to bound the accumulated `3x−1` excess uniformly in the number of generations.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable instance instFintypeUnitChildWordM (root b a K : ℕ)
    (s : NDGeom2ShiftedWideSymmetricBoundedOvershootDepth b) (u : NDGeom2RootSideUnitDigit) :
    Fintype (UnitChildWordM root b a K s u) :=
  Fintype.ofFinset
    (ndGeom2ShiftedWideSymmetricRootSideUnitChildWordFinset
      b a s.1 K u.1 (-(root : ZMod (3 ^ (1 + s.1)))))
    (by intro rootSide; rfl)

/-- **The `3x−1` child state.** -/
noncomputable def nextM (S : NDGeom2ShiftedWideSymmetricRegenerativeState) (b K : ℕ)
    (hb : 200 ≤ b) (hfloor : ∀ i, b ≤ S.base i) :
    NDGeom2ShiftedWideSymmetricRegenerativeState := by
  letI := S.labelFintype
  exact {
    Label := UnitChildIncidenceM (Finset.univ : Finset S.Label) S.root b
      (ndGeom2ShiftedWideSymmetricShiftRadius b) K
    labelFintype := inferInstance
    root := fun z => ucSourceM z
    base := fun z => ndA5QOneRootDyadicBase (ucSourceM z)
    outerWeight := fun z => S.outerWeight (ucLabelM z) * atomM (toPhysicalM z)
    weight_nonneg := fun z =>
      mul_nonneg (S.weight_nonneg _) (atomM_nonneg (toPhysicalM z))
    root_odd := fun z => ucSourceM_odd S.root_odd z
    base_eq := fun _z => rfl
    base_twoHundred := fun z => by
      have h := floor_add_oneHundredth_le_sourceMBase (rootBase := S.base)
        S.root_odd hb hfloor S.rootLower (toPhysicalM z)
      change 200 ≤ ndA5QOneRootDyadicBase (sourceM (toPhysicalM z))
      omega }

@[simp] theorem nextM_root (S : NDGeom2ShiftedWideSymmetricRegenerativeState) (b K : ℕ)
    (hb : 200 ≤ b) (hfloor : ∀ i, b ≤ S.base i)
    (z : (nextM S b K hb hfloor).Label) :
    (nextM S b K hb hfloor).root z = ucSourceM z := rfl

/-- **The floor strictly grows.**  `Generations.generation_product_le` consumes exactly this. -/
theorem nextM_floor_add_oneHundredth_le_base
    (S : NDGeom2ShiftedWideSymmetricRegenerativeState) (b K : ℕ)
    (hb : 200 ≤ b) (hfloor : ∀ i, b ≤ S.base i)
    (z : (nextM S b K hb hfloor).Label) :
    b + b / 100 ≤ (nextM S b K hb hfloor).base z := by
  change b + b / 100 ≤ ndA5QOneRootDyadicBase (ucSourceM z)
  exact floor_add_oneHundredth_le_sourceMBase (rootBase := S.base)
    S.root_odd hb hfloor S.rootLower (toPhysicalM z)

end ThreeXMinusOne
