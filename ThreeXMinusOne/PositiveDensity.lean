import ThreeXMinusOne.FrozenSeed
import ThreeXMinusOne.PublicCount
import ThreeXMinusOne.MassLowerBound
import Erdos1135.ND.PositiveDensity.PredecessorAnalyticSupport
import Erdos1135.ND.PositiveDensity.ExplicitNumericalSyracuseMixing

/-!
# `PredecessorDensity`

`generalTarget_predecessors_positive_lower_density`, mirrored: the `3x−1` predecessors of any
target `a` with `0 < a` and `3 ∤ a` have positive lower density.

Everything it consumes is now proved.  Layer 71 supplies the frozen seed; Layer 62 turns the
seed's margin into a lower bound on the terminal mass; Layer 47 turns that into a linear-in-`Y`
predecessor count.

Three of the artifact's inputs are used unchanged, because none of them mentions a map:
`explicitSyracuseMixing_six` (the numerical mixing estimate), `explicitMixing_quadratic`, and
`unitReferenceDensity_finite_upper`.  The height bound the count needs is obtained from
finiteness of the label type rather than from the artifact's explicit interval estimate — the
statement only asks that *some* `H` dominate finitely many reals.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

/-- **Positive lower density of `3x−1` predecessors** (M2 for the `3x−1` map). -/
theorem predecessors_positive_lower_density : PredecessorDensity := by
  classical
  intro a ha hthree
  set C : ℕ := explicitSyracuseMixingCoefficient with hCdef
  have hmix : Tao.syracFineScaleMixingAt 6 (C : ℝ) := explicitSyracuseMixing_six
  set b : ℕ := 2 ^ 80 with hbdef
  set N : ℕ := explicitLogarithmicSeedGeneration b C with hNdef
  obtain ⟨U, hfloor, hD, hspan, hreach, hnonret, hPpos, hgood⟩ :=
    exists_frozenSeedStateM (a := a) (b := b) ha hthree (le_refl _) C hmix (le_refl N)
  set cap : ℕ → ℕ := fun j => 16 + j / 100 with hcapdef
  have hcap : ∀ n, cap n ≤ 17 * (n + 1) := by
    intro n
    have hn := Nat.div_le_self n 100
    show 16 + n / 100 ≤ 17 * (n + 1)
    omega
  -- the conductor: large enough for the square budget
  set m : ℕ := 1408 * Nat.ceil U.parentSourcePotential * C + 1 with hmdef
  have hm : 1 ≤ m := by rw [hmdef]; omega
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hCnn : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
  have hPceil : U.parentSourcePotential ≤ (Nat.ceil U.parentSourcePotential : ℝ) :=
    Nat.le_ceil _
  have hceilnn : (0 : ℝ) ≤ (Nat.ceil U.parentSourcePotential : ℝ) := Nat.cast_nonneg _
  have hsquare : 176 * (excessBound * U.parentSourcePotential) * (C : ℝ) ≤
      (1 / 4 : ℝ) * (m : ℝ) ^ 2 := by
    have hE := excessBound_le_two
    have hEp := excessBound_pos.le
    have h1 : 176 * (excessBound * U.parentSourcePotential) * (C : ℝ) ≤
        352 * (Nat.ceil U.parentSourcePotential : ℝ) * (C : ℝ) := by
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hE) hPpos.le) hCnn,
        mul_nonneg (sub_nonneg.mpr hPceil) hCnn, hEp, hCnn, hPpos.le]
    have hmval : (m : ℝ) = 1408 * (Nat.ceil U.parentSourcePotential : ℝ) * (C : ℝ) + 1 := by
      rw [hmdef]; push_cast; ring
    have hmsq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith [hmR]
    have h2 : (352 : ℝ) * (Nat.ceil U.parentSourcePotential : ℝ) * (C : ℝ) ≤
        (1 / 4 : ℝ) * (m : ℝ) ^ 2 := by
      nlinarith [hmval, hmsq, hceilnn, hCnn]
    linarith
  have hquad : ndExplicitQuadraticMixingAt (C : ℝ) m := explicitMixing_quadratic hCnn hmix hm
  -- the generation threshold
  set J : ℕ := max (max (goodMarkedStartM b C N) (2 * m)) (1000000000 * (0 + 17 + 4)) with hJdef
  -- the height, from finiteness of the label type
  letI := (iterateM U cap J).state.labelFintype
  obtain ⟨H, hH⟩ : ∃ H : ℕ, ∀ i : (iterateM U cap J).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (iterateM U cap J).floor
        ((iterateM U cap J).state.root i) ≤ H := by
    by_cases hne : Nonempty ((iterateM U cap J).state.Label)
    · obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i : (iterateM U cap J).state.Label =>
        ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (iterateM U cap J).floor
          ((iterateM U cap J).state.root i))
      exact ⟨Nat.ceil (ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (iterateM U cap J).floor
        ((iterateM U cap J).state.root i₀)), fun i => (hi₀ i).trans (Nat.le_ceil _)⟩
    · exact ⟨0, fun i => absurd ⟨i⟩ hne⟩
  set eta : ℝ := 9 * (1 / 4 : ℝ) / (16 * ((3 ^ m : ℕ) : ℝ)) with hetadef
  have heta : 0 < eta := by rw [hetadef]; positivity
  refine ⟨eta / (64 * U.parentSourcePotential * generationExcessBound),
    div_pos heta (by
      have := generationExcessBound_pos
      have := hPpos
      positivity), 64 * (H + 1), ?_⟩
  intro Y hY
  refine generalTargetM_publicCount_from_mass U a hreach hnonret cap hspan hcap hPpos J H
    (by rw [hJdef]; exact le_max_right _ _) hH ?_ Y hY
  intro n hn X hX hi
  -- the conductor room
  have hroom : m ≤ (forwardIterateM U cap n).floor / 4 ∧
      (forwardIterateM U cap n).floor / 4 ≤ (forwardIterateM U cap n).floor := by
    have h := NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.explicitConductor_quarter_room
      U cap m n (by
      have := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
      have h2 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
      omega)
    rw [forwardIterateM_floor_eq]
    exact h
  have hmark := hgood n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn) X hX hi
  have hPle : generationExcessProductM U cap (n + 1) ≤ excessBound := by
    unfold excessBound
    exact generationExcessProductM_le U cap (n + 1)
  have hsquare' : 176 * (generationExcessProductM U cap (n + 1) * U.parentSourcePotential) *
      (C : ℝ) ≤ (1 / 4 : ℝ) * (m : ℝ) ^ 2 := by
    nlinarith [hsquare, mul_nonneg (mul_nonneg (sub_nonneg.mpr hPle) hPpos.le) hCnn,
      hPpos.le, hCnn, generationExcessProductM_nonneg U cap (n + 1), excessBound_pos.le]
  exact fullGoodCoreTerminalMassM_ge_of_square_budget_and_height U cap ndRootCoreWidth n (cap n)
    m ((forwardIterateM U cap n).floor / 4) hm hroom.1 hroom.2 hnonret hCnn
    (hquad _ hroom.1) (by norm_num) hsquare' (3 ^ m) (by positivity)
    (unitReferenceDensity_finite_upper m) X hX hi hmark

end

end ThreeXMinusOne
