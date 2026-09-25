import ThreeXMinusOne.ShellIncidence

/-!
# Extensionality for the `3x−1` incidence

`…BoundedOvershootIncidence_ext` and `…_eq_of_label_eq_of_commonPrefix`, mirrored.

These are what make the selected-word map injective, and injectivity is what turns the sum over
incidences into a sum over words — the first step of the mass identity that is all that now
stands between these layers and `MazurM2Neg`.

The mirror is trivial in content: the argument is that the depth of a first crossing is
determined by the full word, which is residue-independent reasoning.  The residue enters only
through membership in the word finset, which both incidences satisfy by construction.  The
artifact's own uniqueness lemma is `private`, so it is reproved here.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

variable {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}

theorem incidenceM_ext {z w : IncidenceM Label root base shift K}
    (hlabel : labelM z = labelM w) (hdepth : depthM z = depthM w)
    (hword : rootSideWordM z = rootSideWordM w) : z = w := by
  rcases z with ⟨i, s, zword⟩
  rcases w with ⟨j, t, wword⟩
  change i = j at hlabel
  subst hlabel
  change (s : ℕ) = (t : ℕ) at hdepth
  have hst : s = t := Subtype.ext hdepth
  subst hst
  change zword.1 = wword.1 at hword
  have hzw : zword = wword := Subtype.ext hword
  subst hzw
  rfl

/-- The artifact's `ndFiniteFirstHitAt_unique_depth` is `private`; reproved. -/
private theorem firstHitAt_unique_depth {I : Finset ℕ} {Hit : ℕ → List ℕ+ → Prop}
    {s t : ℕ} {full : List ℕ+}
    (hs : ndFiniteFirstHitAt I Hit s full) (ht : ndFiniteFirstHitAt I Hit t full) :
    s = t := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · exact (ht.2.2 s hs.1 hst) hs.2.1
  · exact (hs.2.2 t ht.1 hts) ht.2.1

/-- **Two minus incidences with the same label and a common full word are equal.** -/
theorem incidenceM_eq_of_label_eq_of_commonPrefix
    {z w : IncidenceM Label root base shift K}
    (hlabel : labelM z = labelM w) {fullRootSide : List ℕ+}
    (hzPrefix : rootSideWordM z = fullRootSide.take (depthM z))
    (hwPrefix : rootSideWordM w = fullRootSide.take (depthM w)) :
    z = w := by
  let iz := labelM z
  let iw := labelM w
  let sz := depthM z
  let sw := depthM w
  have hzFirstTake :
      ndFiniteFirstHitAt
        (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths (base iz))
        (ndGeom2ShiftedWideSymmetricCrossingEligibleHit (base iz) (shift iz)) sz
        (fullRootSide.take sz) := by
    simpa only [iz, sz, ← hzPrefix] using firstCrossingM z
  have hzFirst :
      ndFiniteFirstHitAt
        (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths (base iz))
        (ndGeom2ShiftedWideSymmetricCrossingEligibleHit (base iz) (shift iz)) sz
        fullRootSide :=
    (ndFiniteFirstShiftedWideSymmetricCrossing_take_iff
      (base iz) (shift iz) sz fullRootSide).mp hzFirstTake
  have hwFirstTake :
      ndFiniteFirstHitAt
        (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths (base iw))
        (ndGeom2ShiftedWideSymmetricCrossingEligibleHit (base iw) (shift iw)) sw
        (fullRootSide.take sw) := by
    simpa only [iw, sw, ← hwPrefix] using firstCrossingM w
  have hwFirst :
      ndFiniteFirstHitAt
        (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths (base iw))
        (ndGeom2ShiftedWideSymmetricCrossingEligibleHit (base iw) (shift iw)) sw
        fullRootSide :=
    (ndFiniteFirstShiftedWideSymmetricCrossing_take_iff
      (base iw) (shift iw) sw fullRootSide).mp hwFirstTake
  have hi : iz = iw := hlabel
  have hwFirst' :
      ndFiniteFirstHitAt
        (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths (base iz))
        (ndGeom2ShiftedWideSymmetricCrossingEligibleHit (base iz) (shift iz)) sw
        fullRootSide := by
    simpa only [hi] using hwFirst
  have hdepth : sz = sw := firstHitAt_unique_depth hzFirst hwFirst'
  have hdepth' : depthM z = depthM w := by simpa only [sz, sw] using hdepth
  have hword : rootSideWordM z = rootSideWordM w := by
    rw [hzPrefix, hwPrefix, hdepth']
  exact incidenceM_ext hlabel hdepth' hword

end ThreeXMinusOne
