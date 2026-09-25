import ThreeXMinusOne.Shell
import ThreeXMinusOne.Incidence

/-!
# The shell bounds at a `3x−1` incidence

`…IncidenceSource_shell` for the minus incidence.  Every input is already available: the
first-crossing and bounded-overshoot predicates come from the artifact's own membership
characterisation of the word finset (word-only, and the finset is the artifact's own at the
negated residue), the reversal lemmas are word-only, the room bound is `Incidence.roomM`, and
the affine identity is `Incidence.sourceM_odd_and_affine`.

Relative to `+1` the upper constant is `4·2^K` rather than `2·2^K` — the source window widens by
a factor two and nothing else changes.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

variable {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}

theorem firstCrossingM (z : IncidenceM Label root base shift K) :
    ndGeom2ShiftedWideSymmetricFirstCrossingAt
      (base (labelM z)) (shift (labelM z)) (depthM z) (rootSideWordM z) :=
  (mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff.mp
    (wordM_mem z)).2.1.1

theorem boundedOvershootM (z : IncidenceM Label root base shift K) :
    ndGeom2ShiftedWideSymmetricBoundedOvershoot
      (base (labelM z)) (shift (labelM z)) (depthM z) K (rootSideWordM z) :=
  (mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff.mp
    (wordM_mem z)).2.1.2

/-- **The `3x−1` incidence shell.** -/
theorem sourceM_shell (hrootOdd : ∀ i, Odd (root i)) (hbaseNine : ∀ i, 9 ≤ base i)
    (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (z : IncidenceM Label root base shift K) :
    2 ^ shift (labelM z) * 4 ^ base (labelM z) * root (labelM z) ≤
        4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius (base (labelM z)) *
          3 ^ base (labelM z) * sourceM z ∧
      2 ^ ndGeom2ShiftedWideSymmetricShiftRadius (base (labelM z)) *
          3 ^ base (labelM z) * sourceM z ≤
        4 * 2 ^ K * 2 ^ shift (labelM z) * 4 ^ base (labelM z) * root (labelM z) := by
  have hhitRootSide :
      ndGeom2ShiftedWideSymmetricHit
        (base (labelM z)) (shift (labelM z)) (depthM z) (rootSideWordM z) :=
    (firstCrossingM z).2.1.2
  have hhitWord :
      ndGeom2ShiftedWideSymmetricHit
        (base (labelM z)) (shift (labelM z)) (depthM z) (chronologicalWordM z) :=
    ndGeom2ShiftedWideSymmetricHit_reverse_of_length (wordM_length z) hhitRootSide
  have hoverWord :
      ndGeom2ShiftedWideSymmetricBoundedOvershoot
        (base (labelM z)) (shift (labelM z)) (depthM z) K (chronologicalWordM z) :=
    (ndGeom2ShiftedWideSymmetricBoundedOvershoot_reverse
      (base (labelM z)) (shift (labelM z)) (depthM z) K (rootSideWordM z)).2
      (boundedOvershootM z)
  exact crossBoundsM_of_boundedOvershoot
    (chronologicalWordM_length z) hhitWord hoverWord
    (roomM hbaseNine hrootLower z)
    ((sourceM_odd_and_affine hrootOdd z).2)

end ThreeXMinusOne
