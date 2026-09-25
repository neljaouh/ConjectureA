import ThreeXMinusOne.Existence
import ThreeXMinusOne.NextState
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricCoreBackwardMean

/-!
# The `3x−1` mass identity

Rung seven, the top of the tower: the sum over minus unit-child incidences equals the artifact's
filtered kernel **at the negated residue**.

Everything the proof needs is now in place.  `SelectedWord` gives the injection from incidences
to (label, word) pairs; `Transport` evaluates a single incidence's contribution; `Existence`
supplies the vanishing-off-range condition.  The assembly is the artifact's own
`Fintype.sum_of_injective`.

The negation appears in exactly two places, and both are the ones wanted: `g` is evaluated at
`-(source)`, which is harmless because the only constraint on `g` is that it vanishes off the
units and `-y` is a unit exactly when `y` is; and the kernel is evaluated at `-(root)`, which is
precisely the residue at which the seed will be chosen.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

variable {Label : Type*} {Labels : Finset Label} {root : Label → ℕ} {b a K : ℕ}

def ucAtomM (z : UnitChildIncidenceM Labels root b a K) : ℝ :=
  (3 : ℝ) ^ ucDepthM z * ((Tao.geom2PNatListPMF (ucDepthM z)) (ucWordM z)).toReal

def ucWeightM (outerWeight : Label → ℝ) (z : UnitChildIncidenceM Labels root b a K) : ℝ :=
  outerWeight (ucLabelM z) * ucAtomM z

/-- Rung five, at a unit-child incidence. -/
theorem transportAtM_apply_unitIncidence
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b) (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (z : UnitChildIncidenceM Labels root b a K) (q k : ℕ)
    (hlen : (ucWordM z).length ≤ q) (hk : k ≤ q - (ucWordM z).length)
    (g : ZMod (3 ^ k) → ℝ) :
    ndReferencePrefixTransportAt q (ucWordM z) hlen
        (fun v => g (Tao.taoZModThreeProjection hk v))
        (-(((root (ucLabelM z) : ℕ)) : ZMod (3 ^ q))) =
      ucAtomM z * g (-(((ucSourceM z : ℕ)) : ZMod (3 ^ k))) := by
  have ha : taoAffListM (ucWordM z).reverse ((ucSourceM z : ℕ) : ℚ)
      = ((root (ucLabelM z) : ℕ) : ℚ) := by
    simpa only [chronologicalWordM, toPhysicalM_word, toPhysicalM_label, ucSourceM] using
      (sourceM_odd_and_affine hrootOdd (toPhysicalM z)).2
  rw [transportAtM_apply_physical_source q k (ucWordM z) hlen hk ha g]
  unfold ucAtomM
  rw [ucWordM_length]

/-- **The mass identity at the negated residue.** -/
theorem sum_unitIncidenceM_mark_eq_filteredKernel
    (outerWeight : Label → ℝ) (k : ℕ)
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b) (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (hk1 : 1 ≤ k) (psi : List ℕ+ → ℝ) (g : ZMod (3 ^ k) → ℝ)
    (hunit : ∀ n : ℕ, ¬ IsUnit ((n : ℕ) : ZMod (3 ^ 1)) → g ((n : ℕ) : ZMod (3 ^ k)) = 0) :
    (∑ z : UnitChildIncidenceM Labels root b a K,
      ucWeightM outerWeight z * psi (ucWordM z) *
        g (-(((ucSourceM z : ℕ)) : ZMod (3 ^ k)))) =
      ∑ i : {i : Label // i ∈ Labels}, outerWeight i.val *
        ndRootCoreFilteredKernel b a K k psi g
          (-(((root i.val : ℕ)) : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k)))) := by
  classical
  set I := UnitChildIncidenceM Labels root b a K with hI
  set J := {i : Label // i ∈ Labels} × ndShiftedReferenceSelectedWords b a K with hJ
  set e : I → J := selectedWordM with he
  set f : I → ℝ := fun z => ucWeightM outerWeight z * psi (ucWordM z) *
    g (-(((ucSourceM z : ℕ)) : ZMod (3 ^ k))) with hf
  set h : J → ℝ := fun x => outerWeight x.1.val *
    (psi x.2.val * ndRootCoreTransportWord b a K k g x.2
      (-(((root x.1.val : ℕ)) :
        ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k))))) with hh
  have hzero : ∀ x ∉ Set.range e, h x = 0 := by
    intro x hx
    have hz : ndRootCoreTransportWord b a K k g x.2
        (-(((root x.1.val : ℕ)) :
          ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k)))) = 0 := by
      by_contra hn
      refine hx ?_
      obtain ⟨z, hzx⟩ := exists_unitIncidenceM_of_transportAt_ne_zero hrootOdd hb hrootLower
        (ndGeom2ShiftedWideSymmetricHorizon b + k) k hk1 g hunit x
        (by have hl := shiftedReferenceSelectedWords_length_le_horizon b a K x.2; omega)
        (by have hl := shiftedReferenceSelectedWords_length_le_horizon b a K x.2; omega) hn
      exact ⟨z, hzx⟩
    simp only [hh, hz, mul_zero]
  have hmatch : ∀ z, f z = h (e z) := by
    intro z
    have hl := shiftedReferenceSelectedWords_length_le_horizon b a K (e z).2
    change (ucWordM z).length ≤ ndGeom2ShiftedWideSymmetricHorizon b at hl
    have heval := transportAtM_apply_unitIncidence hrootOdd hb hrootLower z
      (ndGeom2ShiftedWideSymmetricHorizon b + k) k (by omega) (by omega) g
    change ndRootCoreTransportWord b a K k g (e z).2
      (-(((root (e z).1.val : ℕ)) :
        ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k)))) = _ at heval
    simp only [hf, hh, ucWeightM]
    rw [heval]
    simp only [he, selectedWordM_fst, selectedWordM_snd]
    ring
  calc (∑ z : I, f z) = ∑ x : J, h x :=
        Fintype.sum_of_injective e (selectedWordM_injective hrootOdd hb hrootLower) f h hzero hmatch
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [hh, ndRootCoreFilteredKernel, Finset.mul_sum]

end

end ThreeXMinusOne
