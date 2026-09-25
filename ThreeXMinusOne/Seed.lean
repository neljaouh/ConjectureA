import ThreeXMinusOne.Residue
import ThreeXMinusOne.MassKernel
import Erdos1135.ND.PositiveDensity.ExplicitUnitSupportedCoreSeed

/-!
# The `3x−1` seed at the negated residue

The quantitative input the mass-identity tower needs.

`MassKernel` showed the minus mass *is* the artifact's kernel read at `-(root)`.  That is only
useful if the kernel is *large* there.  The artifact supplies
`exists_unit_rootCoreBackwardMark_ge_full_product`: some residue `y`, a unit at level one, where
the backward mark beats the probability product.  For `3x+1` the seed is then chosen in class `y`.

Here the seed must be chosen in class `-y`, so that `-(root) ≡ y` puts the mark exactly where the
artifact's bound lives.  `Residue.exists_large_nonreturning_predecessorM_in_residue` produces
`3x−1` predecessors of any admissible target in *any* prescribed ternary class, so the class `-y`
is available; and `-y` is a unit at level one exactly when `y` is, so the unit side-condition
survives the flip.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

/-- **A `3x−1` seed whose negated residue carries the artifact's mark bound.** -/
theorem exists_markM_seed {a : ℕ} (ha : 0 < a) (hthree : ¬ 3 ∣ a)
    {b k : ℕ} (hk : 1 ≤ k) (cap width : ℕ → ℕ) (n X : ℕ) :
    ∃ r : ℕ, X < r ∧ Odd r ∧ ReachesM r a ∧
      (∀ t : ℕ, 0 < t → (syrM^[t]) r ≠ r) ∧
      IsUnit ((r : ℕ) : ZMod (3 ^ 1)) ∧
      ndRootCoreProbabilityProduct b cap width n ≤
        ndRootCoreBackwardMark b cap width k n
          (-((r : ℕ) : ZMod (3 ^ ndRootCoreBackwardConductor b k n))) := by
  classical
  set q := ndRootCoreBackwardConductor b k n with hqdef
  have hq : 1 ≤ q := hk.trans (explicitBackwardConductor_ge b k n)
  obtain ⟨y, hyunit, hymark⟩ :=
    exists_unit_rootCoreBackwardMark_ge_full_product (b := b) (k := k) hk cap width n
  -- choose the seed in the class of `-y`
  set resid : Fin (3 ^ q) := ⟨(-y).val, ZMod.val_lt (-y)⟩ with hresid
  obtain ⟨r, hrX, hrOdd, hrReach, hrRes, hrNoRet⟩ :=
    exists_large_nonreturning_predecessorM_in_residue ha hthree q X resid
  have hrcast : ((r : ℕ) : ZMod (3 ^ q)) = -y := by
    have h : r % 3 ^ q = (-y).val := hrRes
    calc ((r : ℕ) : ZMod (3 ^ q)) = ((r % 3 ^ q : ℕ) : ZMod (3 ^ q)) :=
          (ZMod.natCast_mod r (3 ^ q)).symm
      _ = (((-y).val : ℕ) : ZMod (3 ^ q)) := by rw [h]
      _ = -y := ZMod.natCast_zmod_val (-y)
  have hneg : -((r : ℕ) : ZMod (3 ^ q)) = y := by rw [hrcast]; ring
  refine ⟨r, hrX, hrOdd, hrReach, hrNoRet, ?_, ?_⟩
  · -- the unit condition survives the flip
    have hproj : ((r : ℕ) : ZMod (3 ^ 1)) = -((y.val : ℕ) : ZMod (3 ^ 1)) := by
      have h1 := Tao.taoZModThreeProjection_natCast hq r
      have h2 := Tao.taoZModThreeProjection_natCast hq y.val
      have hy : ((y.val : ℕ) : ZMod (3 ^ q)) = y := ZMod.natCast_zmod_val y
      calc ((r : ℕ) : ZMod (3 ^ 1))
          = Tao.taoZModThreeProjection hq ((r : ℕ) : ZMod (3 ^ q)) := h1.symm
        _ = Tao.taoZModThreeProjection hq (-y) := by rw [hrcast]
        _ = -(Tao.taoZModThreeProjection hq y) := by rw [map_neg]
        _ = -(Tao.taoZModThreeProjection hq ((y.val : ℕ) : ZMod (3 ^ q))) := by rw [hy]
        _ = -((y.val : ℕ) : ZMod (3 ^ 1)) := by rw [h2]
    rw [hproj]
    exact IsUnit.neg hyunit
  · rw [hneg]
    exact hymark

end ThreeXMinusOne
