import ThreeXMinusOne.AmbientChild
import ThreeXMinusOne.UnitChild

/-!
# The unit digit of a `3x−1` incidence

Rung two: the minus twins of `…BoundedOvershootIncidence_root_eq_ambientChild_sourceDigit` and
`…UnitChildIncidence_sourceDigit_eq`.

Both carry the negation that `AmbientChild` established.  On the `+1` side the digit of a
unit-child incidence is `source mod 3`; here it is `-(source) mod 3`, and the root appears
negated on the other side as well.  Recovering the digit from the source is what makes
`toPhysicalM` injective, and hence the selected-word map injective — the step the mass identity
needs.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

variable {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}

/-- The minus physical incidence, read at modulus `3^(1+depth)`. -/
theorem rootM_eq_ambientChild_negSourceDigit
    (hrootOdd : ∀ i, Odd (root i)) (hbaseNine : ∀ i, 9 ≤ base i)
    (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (z : IncidenceM Label root base shift K) :
    -((root (labelM z) : ℕ) : ZMod (3 ^ (1 + depthM z))) =
      ndReversedPrefixAmbientChild (depthM z) (rootSideWordM z)
        (-((sourceM z : ℕ) : ZMod (3 ^ 1))) := by
  apply natCastM_eq_ambientChild_negDigit_of_affineM (wordM_length z)
  simpa only [chronologicalWordM] using (sourceM_odd_and_affine hrootOdd z).2

variable {Labels : Finset Label} {b a : ℕ}

def ucDigitM (z : UnitChildIncidenceM Labels root b a K) : ZMod (3 ^ 1) := z.2.2.1.1

/-- **The digit of a `3x−1` unit-child incidence is `-(source) mod 3`.** -/
theorem ucSourceDigitM_eq
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (z : UnitChildIncidenceM Labels root b a K) :
    -((sourceM (toPhysicalM z) : ℕ) : ZMod (3 ^ 1)) = ucDigitM z := by
  set s := ucDepthM z with hs
  set rootSide := ucWordM z with hrs
  set u := z.2.2.1 with hu
  have hword := (mem_ndGeom2ShiftedWideSymmetricRootSideUnitChildWordFinset_iff).1 z.2.2.2.2
  have hrootActual :
      -((root (ucLabelM z) : ℕ) : ZMod (3 ^ (1 + s))) =
        ndReversedPrefixAmbientChild s rootSide u.1 := by
    simpa only [s, rootSide, u] using hword.2.2.symm
  have hsource :
      -((root (ucLabelM z) : ℕ) : ZMod (3 ^ (1 + s))) =
        ndReversedPrefixAmbientChild s rootSide
          (-((sourceM (toPhysicalM z) : ℕ) : ZMod (3 ^ 1))) := by
    simpa only [s, rootSide] using
      rootM_eq_ambientChild_negSourceDigit hrootOdd (fun _ => hb) (fun _ => hrootLower _)
        (toPhysicalM z)
  exact ndReversedPrefixAmbientChild_injective s rootSide (hsource.symm.trans hrootActual)

end ThreeXMinusOne
