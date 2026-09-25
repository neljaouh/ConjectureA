import ThreeXMinusOne.ForwardCoreMass
import ThreeXMinusOne.Seed
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricExplicitCoreProduct

/-!
# The seed's core mark

`exists_generalTarget_full_core_mark`, mirrored.

Layer 26 produces a seed `r` reaching the target, non-returning, and sitting in a ternary class
where the backward mark is at least the probability product.  Layer 30 says the singleton state
built on that seed has core mass exactly that mark.  Together: a single-root state whose core
mass is at least `255/256`.

**Two inputs need no porting.**  `ndRootCoreSingletonState` builds a state with one label, weight
one and the given root — it names no map.  And `coreProbabilityProduct_ge_255_div_256` concludes
about `ndRootCoreProbabilityProduct U.floor …`, which depends on the floor alone; the `+1`
iterate appears only inside its proof, and the two iterates have the same floor recursion anyway.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

/-- The singleton state's core mass is the backward mark at the negated residue. -/
theorem singletonStateM_coreMass_eq_backwardMark (b M : ℕ) (hb : 200 ≤ b) (hM : Odd M)
    (hl : 16 ^ b ≤ M) (cap width : ℕ → ℕ) (n k : ℕ) (hk : 1 ≤ k) :
    forwardCoreMassM (ndRootCoreSingletonState b M hb hM hl) cap width n k (fun _ => 1) =
      ndRootCoreBackwardMark b cap width k n
        (-((M : ℕ) : ZMod (3 ^ ndRootCoreBackwardConductor b k n))) := by
  rw [forwardCoreMassM_eq_backwardMarkM _ _ _ _ _ hk]
  change (∑ _i : Unit, (1 : ℝ) * 1 * ndRootCoreBackwardMark b cap width k n
    (-((M : ℕ) : ZMod (3 ^ ndRootCoreBackwardConductor b k n)))) = _
  simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_smul]

/-- **A seed whose singleton state carries core mass at least `255/256`.** -/
theorem exists_generalTargetM_full_core_mark {a b k : ℕ} (ha : 0 < a) (hthree : ¬ 3 ∣ a)
    (hb : 2 ^ 80 ≤ b) (hk : 1 ≤ k) (cap : ℕ → ℕ) (hcap : ∀ n, 16 + n / 100 ≤ cap n) (n : ℕ) :
    ∃ (r : ℕ) (hr : Odd r) (hl : 16 ^ b ≤ r),
      ReachesM r a ∧ (∀ t : ℕ, 0 < t → (syrM^[t]) r ≠ r) ∧
      IsUnit ((r : ℕ) : ZMod (3 ^ 1)) ∧
      (255 / 256 : ℝ) ≤
        forwardCoreMassM (ndRootCoreSingletonState b r
          ((by norm_num : (200 : ℕ) ≤ 2 ^ 80).trans hb) hr hl)
          cap ndRootCoreWidth n k (fun _ => 1) := by
  have hb200 : 200 ≤ b := (by norm_num : (200 : ℕ) ≤ 2 ^ 80).trans hb
  obtain ⟨r, hrX, hr, htarget, hnonreturn, hunit, hmark⟩ :=
    exists_markM_seed ha hthree (b := b) hk cap ndRootCoreWidth n (16 ^ b)
  have hl : 16 ^ b ≤ r := hrX.le
  refine ⟨r, hr, hl, htarget, hnonreturn, hunit, ?_⟩
  have hp : (255 / 256 : ℝ) ≤ ndRootCoreProbabilityProduct b cap ndRootCoreWidth n := by
    have := (ndRootCoreSingletonState b r hb200 hr hl).coreProbabilityProduct_ge_255_div_256
      (by change 2 ^ 80 ≤ b; exact hb) cap hcap n
    exact this
  rw [singletonStateM_coreMass_eq_backwardMark b r hb200 hr hl cap ndRootCoreWidth n k hk]
  exact hp.trans hmark

end

end ThreeXMinusOne
