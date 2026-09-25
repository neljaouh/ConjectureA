import ThreeXMinusOne.ShellIncidence
import ThreeXMinusOne.IncidenceCharge
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideUniformFloorUnitChildState

/-!
# The `3x−1` unit-child incidence

The entry point to the child-state construction, which is what stands between these layers and
the **mass** input of `Assembly.count_ge_of_incidence_family`.

The artifact's state iterates by taking the labels of the child state to *be* unit-child
incidences of the parent, with the child's roots the incidence sources.  As with the physical
incidence (Layer 7), the unit-child word finset takes the admissible residue as an argument and
the `3x+1` development instantiates it at `root`; the `3x−1` condition is that same finset at
`-(root)`.

The key compatibility is that the residue flip commutes with the projection
`ZMod (3^(1+s)) → ZMod (3^s)`, since `taoZModThreeProjection` is additive: negating upstairs and
projecting agrees with projecting and negating.  So `toPhysicalM` lands in the `IncidenceM` of
Layer 7, and with it every fact proved there and in Layers 8, 12 and 13 — oddness, the valuation
word, the iterate, the unconditional charge bound and the shell — transfers to the unit-child
incidence for free.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

/-!
## A sign trap in the unit digit

The word finset is read at `-(root)`, but the *digit* is **not** `source mod 3`.

`ndReversedPrefixAmbientChild s w z = taoSection6AmbientTailEmbed … z + headPrefix(offset)`, and
`taoSection6AmbientTailEmbed` is linear in `z`.  For `3x+1` the cleared identity
`3^L·N + C = 2^W·M` gives

    M = tailEmbed (N mod 3) + headPrefix(offset)

so `…_sourceDigit_eq` recovers the digit as `source mod 3`.  For `3x−1` the identity is
`3^L·N = 2^W·M + C`, hence

    -M = tailEmbed (-N) + headPrefix(offset),

and the digit recovered from an incidence is `-(source) mod 3`.

So the minus twin of `…_sourceDigit_eq` must read `digit z = -(sourceM … : ZMod (3^1))`.  Getting
this wrong would not fail to compile at the definition — it would fail much later, in the
injectivity of the selected-word map, and would be hard to trace back.  Everything above this
point is unaffected: `toPhysicalM` uses only the projection to `ZMod (3^s)`, where the digit does
not appear.
-/

/-- The `3x−1` unit-child word: the artifact's own finset, at the negated residue. -/
abbrev UnitChildWordM (root b a K : ℕ)
    (s : NDGeom2ShiftedWideSymmetricBoundedOvershootDepth b) (u : NDGeom2RootSideUnitDigit) :=
  {rootSide : List ℕ+ // rootSide ∈
    ndGeom2ShiftedWideSymmetricRootSideUnitChildWordFinset
      b a s.1 K u.1 (-(root : ZMod (3 ^ (1 + s.1))))}

abbrev UnitChildIncidenceM {Label : Type*} (Labels : Finset Label) (root : Label → ℕ)
    (b a K : ℕ) :=
  Σ i : {i : Label // i ∈ Labels},
    Σ s : NDGeom2ShiftedWideSymmetricBoundedOvershootDepth b,
      Σ u : NDGeom2RootSideUnitDigit,
        UnitChildWordM (root i.1) b a K s u

variable {Label : Type*} {Labels : Finset Label} {root : Label → ℕ} {b a K : ℕ}

def ucLabelM (z : UnitChildIncidenceM Labels root b a K) : Label := z.1.1

def ucDepthM (z : UnitChildIncidenceM Labels root b a K) : ℕ := z.2.1.1

def ucWordM (z : UnitChildIncidenceM Labels root b a K) : List ℕ+ := z.2.2.2.1

/-- **The projection to the physical minus incidence.** -/
def toPhysicalM (z : UnitChildIncidenceM Labels root b a K) :
    IncidenceM Label root (fun _ => b) (fun _ => a) K := by
  let i := ucLabelM z
  let s := z.2.1
  let u := z.2.2.1
  let rootSide := ucWordM z
  have hunit := (mem_ndGeom2ShiftedWideSymmetricRootSideUnitChildWordFinset_iff).1 z.2.2.2.2
  have hprojection := ndReversedPrefixAmbientChild_projection s.1 rootSide u.1
  have hchild :
      ndReversedPrefixAmbientChild s.1 rootSide u.1 = -(root i : ZMod (3 ^ (1 + s.1))) := by
    simpa only [i, s, u, rootSide] using hunit.2.2
  have hoffset :
      Tao.taoSection7OffsetZMod s.1 rootSide = -(root i : ZMod (3 ^ s.1)) := by
    calc Tao.taoSection7OffsetZMod s.1 rootSide
        = Tao.taoZModThreeProjection (show s.1 ≤ 1 + s.1 by omega)
            (ndReversedPrefixAmbientChild s.1 rootSide u.1) := hprojection.symm
      _ = Tao.taoZModThreeProjection (show s.1 ≤ 1 + s.1 by omega)
            (-(root i : ZMod (3 ^ (1 + s.1)))) := by rw [hchild]
      _ = -(Tao.taoZModThreeProjection (show s.1 ≤ 1 + s.1 by omega)
            ((root i : ℕ) : ZMod (3 ^ (1 + s.1)))) := by rw [map_neg]
      _ = -(root i : ZMod (3 ^ s.1)) := by
          rw [Tao.taoZModThreeProjection_natCast (show s.1 ≤ 1 + s.1 by omega) (root i)]
  refine ⟨i, s, ⟨rootSide, ?_⟩⟩
  exact (mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff).2
    ⟨hunit.1, hunit.2.1, hoffset⟩

/-- The unit-child source, defined exactly as the artifact defines the `+1` one: through the
physical incidence. -/
def ucSourceM (z : UnitChildIncidenceM Labels root b a K) : ℕ := sourceM (toPhysicalM z)

theorem ucSourceM_odd (hrootOdd : ∀ i, Odd (root i))
    (z : UnitChildIncidenceM Labels root b a K) : Odd (ucSourceM z) :=
  sourceM_odd hrootOdd (toPhysicalM z)

theorem ucSourceM_iterate (hrootOdd : ∀ i, Odd (root i))
    (z : UnitChildIncidenceM Labels root b a K) :
    (syrM^[depthM (toPhysicalM z)]) (ucSourceM z) = root (ucLabelM z) :=
  sourceM_iterate hrootOdd (toPhysicalM z)

/-- The unconditional charge bound, inherited. -/
theorem ucSourceM_mul_atomM_le_root (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (z : UnitChildIncidenceM Labels root b a K) :
    (ucSourceM z : ℝ) * atomM (toPhysicalM z) ≤ (3 / 2 : ℝ) * (root (ucLabelM z) : ℝ) :=
  sourceM_mul_atomM_le_root_unconditional hrootOdd (fun _ => hb) (fun _ => hrootLower _)
    (toPhysicalM z)

end ThreeXMinusOne
