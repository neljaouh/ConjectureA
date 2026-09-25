import ThreeXMinusOne.DigitM
import ThreeXMinusOne.IncidenceExt

/-!
# Unit-child extensionality and injectivity for `3x−1`

Rung three: `…UnitChildIncidence_ext`, `…_toPhysical_injective` and
`…UnitChildIncidence_eq_of_label_eq_of_commonPrefix`.

`toPhysicalM` forgets the unit digit, so injectivity needs the digit to be recoverable from the
physical data — which is exactly what `DigitM.ucSourceDigitM_eq` supplies, with the negation the
sign trap forces.  With that, the common-prefix statement reduces to the physical one proved in
`IncidenceExt`.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

variable {Label : Type*} {Labels : Finset Label} {root : Label → ℕ} {b a K : ℕ}

@[simp] theorem toPhysicalM_label (z : UnitChildIncidenceM Labels root b a K) :
    labelM (toPhysicalM z) = ucLabelM z := rfl

@[simp] theorem toPhysicalM_depth (z : UnitChildIncidenceM Labels root b a K) :
    depthM (toPhysicalM z) = ucDepthM z := rfl

@[simp] theorem toPhysicalM_word (z : UnitChildIncidenceM Labels root b a K) :
    rootSideWordM (toPhysicalM z) = ucWordM z := rfl

theorem unitChildM_ext {z w : UnitChildIncidenceM Labels root b a K}
    (hlabel : ucLabelM z = ucLabelM w) (hdepth : ucDepthM z = ucDepthM w)
    (hdigit : ucDigitM z = ucDigitM w) (hword : ucWordM z = ucWordM w) :
    z = w := by
  rcases z with ⟨i, s, u, zword⟩
  rcases w with ⟨j, t, v, wword⟩
  change i.1 = j.1 at hlabel
  have hij : i = j := Subtype.ext hlabel
  subst hij
  change s.1 = t.1 at hdepth
  have hst : s = t := Subtype.ext hdepth
  subst hst
  change u.1 = v.1 at hdigit
  have huv : u = v := Subtype.ext hdigit
  subst huv
  change zword.1 = wword.1 at hword
  have hzw : zword = wword := Subtype.ext hword
  subst hzw
  rfl

theorem toPhysicalM_injective (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i) :
    Function.Injective
      (toPhysicalM (Labels := Labels) (root := root) (b := b) (a := a) (K := K)) := by
  intro z w hphysical
  have hlabel : ucLabelM z = ucLabelM w := by
    simpa only [toPhysicalM_label] using congrArg labelM hphysical
  have hdepth : ucDepthM z = ucDepthM w := by
    simpa only [toPhysicalM_depth] using congrArg depthM hphysical
  have hword : ucWordM z = ucWordM w := by
    simpa only [toPhysicalM_word] using congrArg rootSideWordM hphysical
  have hsource : sourceM (toPhysicalM z) = sourceM (toPhysicalM w) :=
    congrArg sourceM hphysical
  have hdigit : ucDigitM z = ucDigitM w := by
    calc ucDigitM z = -((sourceM (toPhysicalM z) : ℕ) : ZMod (3 ^ 1)) :=
          (ucSourceDigitM_eq hrootOdd hb hrootLower z).symm
      _ = -((sourceM (toPhysicalM w) : ℕ) : ZMod (3 ^ 1)) := by rw [hsource]
      _ = ucDigitM w := ucSourceDigitM_eq hrootOdd hb hrootLower w
  exact unitChildM_ext hlabel hdepth hdigit hword

/-- **The common-prefix statement for the `3x−1` unit child.** -/
theorem unitChildM_eq_of_label_eq_of_commonPrefix
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    {z w : UnitChildIncidenceM Labels root b a K}
    (hlabel : ucLabelM z = ucLabelM w) {fullRootSide : List ℕ+}
    (hzPrefix : ucWordM z = fullRootSide.take (ucDepthM z))
    (hwPrefix : ucWordM w = fullRootSide.take (ucDepthM w)) :
    z = w := by
  apply toPhysicalM_injective hrootOdd hb hrootLower
  apply incidenceM_eq_of_label_eq_of_commonPrefix (fullRootSide := fullRootSide)
  · simpa only [toPhysicalM_label] using hlabel
  · simpa only [toPhysicalM_word, toPhysicalM_depth] using hzPrefix
  · simpa only [toPhysicalM_word, toPhysicalM_depth] using hwPrefix

end ThreeXMinusOne
