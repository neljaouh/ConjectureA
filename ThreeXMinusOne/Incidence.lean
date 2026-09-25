import ThreeXMinusOne.AffineResidueM
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideBoundedOvershootPhysicalIncidence

/-!
# The physical incidence layer for `3x−1`

Layer 7 of the port, and the payoff of Layer 6.

The artifact's word finset

    ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset b a s K x

takes the admissible ternary residue `x` as an argument, and every counting, capacity and mass
theorem about it is stated for general `x`.  The `3x+1` development instantiates
`x := (root : ZMod (3^s))`.  By `AffineResidueM`, the `3x−1` condition is that same finset at
`x := -(root : ZMod (3^s))`.

So the incidence layer for `3x−1` is an **instantiation, not a duplication**: the definitions
below reuse the artifact's finset, its membership characterisation, its first-crossing and
bounded-overshoot predicates, and its `Fintype` instance, changing only the residue.  What has to
be reproved is the source trio — and those proofs are the `+1` ones with `taoAffList` replaced by
`taoAffListM`.

One hypothesis disappears.  The `+1` source needs `hbaseNine` and `hrootLower` solely to supply
`2·3^depth < root`, which keeps the truncated subtraction in `taoAffineSourceCandidate` honest.
The `3x−1` candidate is a sum, so `sourceM_odd_and_affine` below needs only `Odd (root i)`.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.Tao Erdos1135.ND.PositiveDensity

noncomputable section

/-- The `3x−1` root-side word: the artifact's own finset, at the negated residue. -/
abbrev WordM (root b a K : ℕ)
    (s : NDGeom2ShiftedWideSymmetricBoundedOvershootDepth b) :=
  {rootSide : List ℕ+ // rootSide ∈
    ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset
      b a s.1 K (-(root : ZMod (3 ^ s.1)))}

abbrev IncidenceM (Label : Type*) (root base shift : Label → ℕ) (K : ℕ) :=
  Σ i : Label,
    Σ s : NDGeom2ShiftedWideSymmetricBoundedOvershootDepth (base i),
      WordM (root i) (base i) (shift i) K s

variable {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}

def labelM (z : IncidenceM Label root base shift K) : Label := z.1

def depthM (z : IncidenceM Label root base shift K) : ℕ := z.2.1.1

def rootSideWordM (z : IncidenceM Label root base shift K) : List ℕ+ := z.2.2.1

def chronologicalWordM (z : IncidenceM Label root base shift K) : List ℕ+ :=
  (rootSideWordM z).reverse

theorem wordM_mem (z : IncidenceM Label root base shift K) :
    rootSideWordM z ∈
      ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset
        (base (labelM z)) (shift (labelM z)) (depthM z) K
        (-(root (labelM z) : ZMod (3 ^ depthM z))) :=
  z.2.2.2

theorem wordM_length (z : IncidenceM Label root base shift K) :
    (rootSideWordM z).length = depthM z :=
  (mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff.mp
    (wordM_mem z)).1

theorem chronologicalWordM_length (z : IncidenceM Label root base shift K) :
    (chronologicalWordM z).length = depthM z := by
  unfold chronologicalWordM
  rw [List.length_reverse, wordM_length]

theorem section7CompatibleM (z : IncidenceM Label root base shift K) :
    -(root (labelM z) : ZMod (3 ^ depthM z)) =
      Tao.taoSection7OffsetZMod (depthM z) (rootSideWordM z) :=
  (mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff.mp
    (wordM_mem z)).2.2.symm

/-- The residue condition of Layer 6, read off the artifact's own membership characterisation. -/
theorem affineCompatibleM (z : IncidenceM Label root base shift K) :
    (root (labelM z) : ZMod (3 ^ depthM z)) =
      taoAffineOffsetZModM (depthM z) (chronologicalWordM z) := by
  have h := section7CompatibleM z
  unfold taoAffineOffsetZModM chronologicalWordM
  rw [Tao.taoAffineOffsetZMod_reverse_eq_taoSection7OffsetZMod (wordM_length z)]
  linear_combination -h

theorem depthM_mem (z : IncidenceM Label root base shift K) :
    depthM z ∈ ndGeom2ShiftedWideSymmetricCrossingSelectedDepths (base (labelM z)) :=
  z.2.1.2

/-- The artifact's own room bound, reproved for the minus incidence.  Its proof uses only the
depth and the base, never the word or the map, so it is the `+1` proof verbatim. -/
theorem roomM (hbaseNine : ∀ i, 9 ≤ base i) (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (z : IncidenceM Label root base shift K) :
    2 * 3 ^ depthM z < root (labelM z) :=
  ndGeom2ShiftedWideSymmetric_two_mul_three_pow_lt_root
    (hbaseNine _) (depthM_mem z) (hrootLower _)

def sourceM (z : IncidenceM Label root base shift K) : ℕ :=
  taoAffineSourceCandidateM (depthM z) (chronologicalWordM z) (root (labelM z))

/-- **The source trio, part 1.**  Note the absent `hbaseNine` / `hrootLower`. -/
theorem sourceM_odd_and_affine (hrootOdd : ∀ i, Odd (root i))
    (z : IncidenceM Label root base shift K) :
    Odd (sourceM z) ∧
      taoAffListM (chronologicalWordM z) (sourceM z : ℚ) = (root (labelM z) : ℚ) := by
  obtain ⟨source, hAff, _hunique⟩ :=
    existsUnique_taoAffListM_eq_of_affineOffsetZModM
      (chronologicalWordM_length z) (hrootOdd (labelM z)) (affineCompatibleM z)
  have hsource : sourceM z = source.1 := by
    unfold sourceM
    exact taoAffineSourceCandidateM_eq_of_taoAffListM_eq (chronologicalWordM_length z) hAff
  rw [hsource]
  exact ⟨source.2, hAff⟩

theorem sourceM_odd (hrootOdd : ∀ i, Odd (root i))
    (z : IncidenceM Label root base shift K) : Odd (sourceM z) :=
  (sourceM_odd_and_affine hrootOdd z).1

/-- **The source trio, part 2.**  The reverse word is the source's `3x−1` valuation word. -/
theorem sourceM_valuation (hrootOdd : ∀ i, Odd (root i))
    (z : IncidenceM Label root base shift K) :
    syrMValuationPNatList (depthM z) (sourceM z) (sourceM_odd hrootOdd z) =
      chronologicalWordM z := by
  obtain ⟨_hodd, hvalues, _hiterate⟩ :=
    taoAffListM_oddNat_decode (chronologicalWordM z) (sourceM z) (root (labelM z))
      (hrootOdd (labelM z)) ((sourceM_odd_and_affine hrootOdd z).2)
  simpa only [chronologicalWordM_length z] using hvalues

/-- **The source trio, part 3.**  The source reaches the root in `depth` accelerated steps. -/
theorem sourceM_iterate (hrootOdd : ∀ i, Odd (root i))
    (z : IncidenceM Label root base shift K) :
    (syrM^[depthM z]) (sourceM z) = root (labelM z) := by
  obtain ⟨_hodd, _hvalues, hiterate⟩ :=
    taoAffListM_oddNat_decode (chronologicalWordM z) (sourceM z) (root (labelM z))
      (hrootOdd (labelM z)) ((sourceM_odd_and_affine hrootOdd z).2)
  simpa only [chronologicalWordM_length z] using hiterate

end

end ThreeXMinusOne
