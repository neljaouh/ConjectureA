import ThreeXMinusOne.TerminalCharge

/-!
# The terminal census: mass against source count

`fullTerminal_mass_mul_lower_le_frozenPotential_mul_card`, mirrored.

This is the census proper.  The terminal mass is a sum over *incidences*; the predecessor count
counts *naturals*.  Layer 34 says a terminal incidence is pinned by its ancestor together with
its source, so the map `z ↦ (ancestor z, source z)` is injective and the incidence sum embeds in
`labels × sources`.  Bounding each term by its ancestor's root-times-weight (Layer 37) and
summing over that product gives `potential · #sources`.

So a window lower bound `X` on every terminal source converts mass into count:

    X · mass ≤ (generation excess) · potential · #sources,

and the generation excess is `1 + 4.6 × 10^(-50)` by Layer 37, uniformly in `n`.

`parentSourcePotential` needs no porting: it is a field of the artifact's own state wrapper,
which the `3x−1` construction inhabits.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

noncomputable instance instFintypeWordM (root b a K : ℕ)
    (s : NDGeom2ShiftedWideSymmetricBoundedOvershootDepth b) :
    Fintype (WordM root b a K s) :=
  Fintype.ofFinset
    (ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset b a s.1 K
      (-(root : ZMod (3 ^ s.1))))
    (by intro rootSide; rfl)

variable {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}

theorem weightM_nonneg (outerWeight : Label → ℝ) (hw : ∀ i, 0 ≤ outerWeight i)
    (z : IncidenceM Label root base shift K) : 0 ≤ weightM outerWeight z :=
  mul_nonneg (hw _) (atomM_nonneg z)

/-- The distinct sources realised at generation `n`. -/
def fullTerminalSourcesM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (shift : (forwardIterateM U cap n).state.Label → ℕ) (K : ℕ) :
    Finset ℕ := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  exact Finset.univ.image
    (sourceM (Label := (forwardIterateM U cap n).state.Label)
      (root := (forwardIterateM U cap n).state.root)
      (base := fun _ => (forwardIterateM U cap n).floor) (shift := shift) (K := K))

/-- The terminal mass at generation `n`. -/
def fullTerminalMassM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (shift : (forwardIterateM U cap n).state.Label → ℕ) (K : ℕ) : ℝ := by
  letI := (forwardIterateM U cap n).state.labelFintype
  exact ∑ z : FullTerminalAtM U cap n shift K,
    weightM (forwardIterateM U cap n).state.outerWeight z

/-- **The census.**  `+1` has this with the generation excess replaced by `1`. -/
theorem fullTerminalM_mass_mul_lower_le_potential_mul_card
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    (shift : (forwardIterateM U cap n).state.Label → ℕ) (K : ℕ)
    (hseed : ∀ i k, 0 < k → (syrM^[k]) (U.state.root i) ≠ U.state.root i)
    (X : ℝ) (hX : ∀ z : FullTerminalAtM U cap n shift K, X ≤ (sourceM z : ℝ)) :
    X * fullTerminalMassM U cap n shift K ≤
      generationExcessProductM U cap (n + 1) *
        (U.parentSourcePotential * (fullTerminalSourcesM U cap n shift K).card) := by
  classical
  letI := U.state.labelFintype
  letI := (forwardIterateM U cap n).state.labelFintype
  set W := fun z : FullTerminalAtM U cap n shift K =>
    weightM (forwardIterateM U cap n).state.outerWeight z with hW
  set P := fun i : U.state.Label => (U.state.root i : ℝ) * U.state.outerWeight i with hP
  set cell := fun z : FullTerminalAtM U cap n shift K =>
    (fullTerminalAncestorM z, sourceM z) with hcell
  set sources := fullTerminalSourcesM U cap n shift K with hsources
  have hinj : Function.Injective cell := by
    intro z w h
    exact fullTerminalM_eq_of_nonreturningSeed_ancestor_source_eq hseed
      (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hsub : Finset.univ.image cell ⊆ Finset.univ.product sources := by
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
      Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  have hprod := generationExcessProductM_nonneg U cap (n + 1)
  calc X * fullTerminalMassM U cap n shift K
      = ∑ z, X * W z := by
        change X * (∑ z, W z) = _
        rw [Finset.mul_sum]
    _ ≤ ∑ z : FullTerminalAtM U cap n shift K,
        generationExcessProductM U cap (n + 1) * P (fullTerminalAncestorM z) := by
        refine Finset.sum_le_sum fun z _ => ?_
        have hw := weightM_nonneg (forwardIterateM U cap n).state.outerWeight
          (forwardIterateM U cap n).state.weight_nonneg z
        exact (mul_le_mul_of_nonneg_right (hX z) hw).trans
          (fullTerminalM_source_mul_weight_le_owner U cap n shift K z)
    _ = generationExcessProductM U cap (n + 1) *
        ∑ z : FullTerminalAtM U cap n shift K, P (fullTerminalAncestorM z) := by
        rw [Finset.mul_sum]
    _ ≤ generationExcessProductM U cap (n + 1) *
        (U.parentSourcePotential * (sources.card : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hprod
        calc (∑ z : FullTerminalAtM U cap n shift K, P (fullTerminalAncestorM z))
            = ∑ c ∈ Finset.univ.image cell, P c.1 := by
              rw [Finset.sum_image]
              exact fun a _ b _ h => hinj h
          _ ≤ ∑ c ∈ Finset.univ.product sources, P c.1 := by
              refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun c _ _ => ?_
              exact mul_nonneg (Nat.cast_nonneg _) (U.state.weight_nonneg c.1)
          _ = U.parentSourcePotential * (sources.card : ℝ) := by
              calc (∑ c ∈ Finset.univ.product sources, P c.1)
                  = ∑ i : U.state.Label, ∑ _s ∈ sources, P i := Finset.sum_product _ _ _
                _ = U.parentSourcePotential * (sources.card : ℝ) := by
                    simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
                    unfold NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.parentSourcePotential
                      ndGeom2PredictableRootSideParentSourcePotential
                      NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorAllLabels
                    dsimp only [P]
                    ring
    _ = _ := rfl

end

end ThreeXMinusOne
