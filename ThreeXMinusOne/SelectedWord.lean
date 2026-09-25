import ThreeXMinusOne.UnitChildExt
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricReferenceMarkedPhysicalIncidence

/-!
# The selected-word map for `3x−1`

Rung four: `unitIncidenceSelectedWord` and its injectivity.

The map sends a unit-child incidence to its label together with its root-side word, viewed as a
*selected* reference word.  Membership in `ndShiftedReferenceSelectedWords` is the crossing and
bounded-overshoot data, which is word-only — so the map itself is residue-independent and the
minus version is the `+1` one verbatim.  Injectivity is where the residue matters, and it reduces
to `UnitChildExt.unitChildM_eq_of_label_eq_of_commonPrefix`.

Injectivity is the point of the whole rung: it is what lets the sum over incidences be rewritten
as a sum over words, which is the shape the artifact's kernel is stated in.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

variable {Label : Type*} {Labels : Finset Label} {root : Label → ℕ} {b a K : ℕ}

theorem ucWordM_length (z : UnitChildIncidenceM Labels root b a K) :
    (ucWordM z).length = ucDepthM z := by
  simpa only [toPhysicalM_word, toPhysicalM_depth] using wordM_length (toPhysicalM z)

/-- The word of a minus unit-child incidence, as a selected reference word. -/
def selectedWordM (z : UnitChildIncidenceM Labels root b a K) :
    {i : Label // i ∈ Labels} × ndShiftedReferenceSelectedWords b a K := by
  refine ⟨z.1, ⟨ucWordM z, ?_⟩⟩
  rw [mem_shiftedReferenceSelectedWords_iff, ucWordM_length]
  exact (mem_ndGeom2ShiftedWideSymmetricRootSideUnitChildWordFinset_iff.mp z.2.2.2.2).2.1

@[simp] theorem selectedWordM_fst (z : UnitChildIncidenceM Labels root b a K) :
    (selectedWordM z).1.val = ucLabelM z := rfl

@[simp] theorem selectedWordM_snd (z : UnitChildIncidenceM Labels root b a K) :
    (selectedWordM z).2.val = ucWordM z := rfl

/-- **The selected-word map is injective.** -/
theorem selectedWordM_injective (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i) :
    Function.Injective
      (selectedWordM (Labels := Labels) (root := root) (b := b) (a := a) (K := K)) := by
  intro z w heq
  have hl : ucLabelM z = ucLabelM w := congrArg (fun p => p.1.val) heq
  have hw : ucWordM z = ucWordM w := congrArg (fun p => p.2.val) heq
  have hz := ucWordM_length z
  have hwlen := ucWordM_length w
  apply unitChildM_eq_of_label_eq_of_commonPrefix hrootOdd hb hrootLower hl
    (fullRootSide := ucWordM z)
  · rw [← hz, List.take_length]
  · rw [hw, ← hwlen, List.take_length]

end ThreeXMinusOne
