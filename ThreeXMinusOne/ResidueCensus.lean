import ThreeXMinusOne.GoodMassFan
import ThreeXMinusOne.GoodCoreCharge
import ThreeXMinusOne.SourceFan
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalWeightedCensus

/-!
# The weighted residue census

`ndTerminalResidueFan` and `fullTerminal_weighted_residue_census_of_nonreturningSeed`, mirrored.

The terminal sources are spread over residue classes no worse than uniformly, up to a constant:
they lie in a window of length proportional to `X` and each residue class mod `3^q` meets such a
window in `O(X/3^q)` naturals.  That counting statement,
`terminal_source_residue_sum_le`, is about a finset of naturals and needs no porting.

**The window constant, reused rather than reproved.**  The artifact's version is stated for a
window `[X, 32X)`; the minus window is `[X, 64X)` (Layer 39).  Rather than reprove it, apply it
at `X' = 2X`: a source below `64X` is below `32·(2X)`, and `3^q ≤ X ≤ 2X`.  The constant
`33` becomes `66`, and that is the only cost.

The residue fan is the one genuinely new object: `+1` fans a residue by `y ↦ 4y + 1`, matching
`ndTerminalSourceFan`, and `3x−1` fans by `y ↦ 4y − 1`, matching Layer 40's `sourceFanM`.  Both
are bijections of `ZMod (3^q)` — `4` is invertible mod `3^q` — so both preserve the uniform mean.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

/-- The `3x−1` residue fan.  `+1` uses `y ↦ 4y + 1`. -/
def residueFanM (q j : ℕ) (y : ZMod (3 ^ q)) : ZMod (3 ^ q) :=
  ((fun z : ZMod (3 ^ q) => 4 * z - 1)^[j]) y

theorem residueFanM_natCast {x : ℕ} (hx : 1 ≤ x) (q j : ℕ) :
    residueFanM q j ((x : ℕ) : ZMod (3 ^ q)) = ((sourceFanM j x : ℕ) : ZMod (3 ^ q)) := by
  induction j with
  | zero => simp [residueFanM, sourceFanM]
  | succ j ih =>
      have hp := sourceFanM_pos hx j
      have h1 : (1 : ℕ) ≤ 4 * sourceFanM j x := by omega
      have hcast : ((4 * sourceFanM j x - 1 : ℕ) : ZMod (3 ^ q)) =
          4 * ((sourceFanM j x : ℕ) : ZMod (3 ^ q)) - 1 := by
        rw [Nat.cast_sub h1]
        push_cast
        ring
      rw [sourceFanM_succ]
      unfold residueFanM
      rw [Function.iterate_succ_apply']
      change 4 * residueFanM q j ((x : ℕ) : ZMod (3 ^ q)) - 1 = _
      rw [ih, hcast]

/-- The residue fan is a bijection, so it preserves the uniform mean. -/
theorem residueFanM_bijective (q j : ℕ) : Function.Bijective (residueFanM q j) := by
  haveI : NeZero (3 ^ q) := ⟨by positivity⟩
  have hunit : IsUnit (4 : ZMod (3 ^ q)) := by
    have h : ((4 : ℕ) : ZMod (3 ^ q)) = (4 : ZMod (3 ^ q)) := by push_cast; ring
    rw [← h]
    exact (ZMod.isUnit_iff_coprime 4 (3 ^ q)).mpr
      (Nat.Coprime.pow_right q (by decide : Nat.Coprime 4 3))
  have hstep : Function.Injective (fun z : ZMod (3 ^ q) => 4 * z - 1) := by
    intro a b h
    simp only at h
    have h4 : (4 : ZMod (3 ^ q)) * a = 4 * b := by linear_combination h
    exact hunit.mul_left_cancel h4
  have hinj : Function.Injective (residueFanM q j) := by
    induction j with
    | zero => exact fun a b h => h
    | succ j ih =>
        intro a b h
        unfold residueFanM at h
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
        exact ih (hstep h)
  exact Finite.injective_iff_bijective.mp hinj

theorem residueFanM_fullMean (q j : ℕ) (f : ZMod (3 ^ q) → ℝ) :
    ndTernaryUniformMean q (fun y => f (residueFanM q j y)) = ndTernaryUniformMean q f := by
  unfold ndTernaryUniformMean
  rw [(residueFanM_bijective q j).sum_comp f]

/-- **The weighted residue census.**  `+1`'s constant is `33`; the wider minus window gives `66`,
and the charge carries the generation excess. -/
theorem fullTerminalM_weighted_residue_census
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    (shift : (forwardIterateM U cap n).state.Label → ℕ) (K : ℕ)
    (hseed : ∀ i k, 0 < k → (syrM^[k]) (U.state.root i) ≠ U.state.root i)
    (q : ℕ) (X : ℝ) (hX : 0 < X) (hQ : ((3 ^ q : ℕ) : ℝ) ≤ X)
    (hsource : ∀ z : FullTerminalAtM U cap n shift K,
      X ≤ (sourceM z : ℝ) ∧ (sourceM z : ℝ) < 64 * X)
    (psi : ZMod (3 ^ q) → ℝ) (hp : ∀ y, 0 ≤ psi y) :
    letI := (forwardIterateM U cap n).state.labelFintype
    (∑ z : FullTerminalAtM U cap n shift K,
      weightM (forwardIterateM U cap n).state.outerWeight z *
        psi (((sourceM z : ℕ) : ZMod (3 ^ q)))) ≤
      66 * (generationExcessProductM U cap (n + 1) * U.parentSourcePotential) *
        ndTernaryUniformMean q psi := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  have hc := fullTerminalM_weighted_source_charge U cap n shift K hseed X
    (fun z => (hsource z).1) (fun x => psi ((x : ℕ) : ZMod (3 ^ q))) (fun x => hp _)
  have h2X : (0 : ℝ) < 2 * X := by linarith
  have hQ2 : ((3 ^ q : ℕ) : ℝ) ≤ 2 * X := by linarith
  have hs := terminal_source_residue_sum_le (fullTerminalSourcesM U cap n shift K) q (2 * X) h2X
    hQ2 (fun x hx => by
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
      have := (hsource z).2
      linarith) psi hp
  have hPnn : (0 : ℝ) ≤ generationExcessProductM U cap (n + 1) * U.parentSourcePotential :=
    mul_nonneg (generationExcessProductM_nonneg U cap (n + 1)) (parentSourcePotentialM_nonneg U)
  have hstep : generationExcessProductM U cap (n + 1) *
      (U.parentSourcePotential * ∑ x ∈ fullTerminalSourcesM U cap n shift K,
        psi ((x : ℕ) : ZMod (3 ^ q))) ≤
      generationExcessProductM U cap (n + 1) * U.parentSourcePotential *
        (33 * (2 * X) * ndTernaryUniformMean q psi) := by
    have := mul_le_mul_of_nonneg_left hs hPnn
    calc generationExcessProductM U cap (n + 1) *
          (U.parentSourcePotential * ∑ x ∈ fullTerminalSourcesM U cap n shift K,
            psi ((x : ℕ) : ZMod (3 ^ q)))
        = generationExcessProductM U cap (n + 1) * U.parentSourcePotential *
            (∑ x ∈ fullTerminalSourcesM U cap n shift K, psi ((x : ℕ) : ZMod (3 ^ q))) := by ring
      _ ≤ _ := this
  have hfinal := hc.trans hstep
  rw [← le_div_iff₀' hX] at hfinal
  refine hfinal.trans (le_of_eq ?_)
  field_simp
  ring

end

end ThreeXMinusOne
