import ThreeXMinusOne.GoodCoreCharge
import ThreeXMinusOne.Window
import ThreeXMinusOne.Reach
import Erdos1135.ND.PositiveDensity.A5SupportedTargetCounting

/-!
# The `3x−1` public predecessor count

`generalTarget_publicCount_from_mass`, mirrored.

Given a lower bound `eta` on the good-core terminal mass at every sufficiently late generation,
this produces a linear-in-`Y` lower bound on the number of `3x−1` predecessors of the target
below `Y`.  Everything it consumes is now in hand:

* the window generation — Layer 32;
* the source window `[X, 64X)` — Layer 39;
* the good-core census — Layer 46;
* sources are genuine predecessors — Layer 34's path plus Layer 10's `reachesM_syrM_iterate`;
* `finset_card_le_natCount_of_subset_range` — map-free, the artifact's own.

**The constants.**  `+1` takes `X = Y/32` and concludes with `eta / (32·potential)`.  The minus
window is twice as wide, so `X = Y/64` and the conclusion is `eta / (64·potential)`, further
divided by the generation excess of Layer 37 — which is `1 + 4.6×10^(-50)`.  The whole cost of
the sign reversal in the final density constant is therefore a factor two and a fifty-digit
rounding error.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

/-- A terminal source reaches whatever the generation-zero seed reaches. -/
theorem fullTerminalM_reaches_of_seed_reaches
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    (shift : (forwardIterateM U cap n).state.Label → ℕ) (K : ℕ) {a : ℕ}
    (hreach : ∀ i, ReachesM (U.state.root i) a) (z : FullTerminalAtM U cap n shift K) :
    sourceM z ∈ predecessorSetM a := by
  set p := fullTerminalPathM U cap n shift K z with hp
  have h1 : ReachesM (sourceM z) ((syrM^[p.depth]) (sourceM z)) :=
    reachesM_syrM_iterate p.sourceOdd p.depth
  rw [p.terminal_eq] at h1
  exact ⟨p.sourceOdd.pos, h1.trans (hreach _)⟩

/-- The absolute bound on the accumulated generation excess (Layer 37). -/
def generationExcessBound : ℝ := Real.exp (3 * (9 / 16 : ℝ) ^ 200 * (256 / 175 : ℝ))

theorem generationExcessBound_pos : 0 < generationExcessBound := Real.exp_pos _

/-- **The `3x−1` public count from a mass bound.**  `+1` has `32 · potential`; here the window is
twice as wide and the charge carries the generation excess, so it is
`64 · potential · (1 + 4.6×10^(-50))`. -/
theorem generalTargetM_publicCount_from_mass
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (a : ℕ)
    (hreach : ∀ i, ReachesM (U.state.root i) a)
    (hseed : ∀ i k, 0 < k → (syrM^[k]) (U.state.root i) ≠ U.state.root i)
    (cap : ℕ → ℕ) {e L : ℕ} (he : rootSpanM U e) (hcap : ∀ n, cap n ≤ L * (n + 1))
    {eta : ℝ} (hP : 0 < U.parentSourcePotential)
    (N H : ℕ) (hN : 1000000000 * (e + L + 4) ≤ N)
    (hH : ∀ i : (iterateM U cap N).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (iterateM U cap N).floor
        ((iterateM U cap N).state.root i) ≤ H)
    (hmass : ∀ n, N ≤ n →
      ∀ (X : ℝ) (hX : 0 < X)
        (hi : ∀ i : (forwardIterateM U cap n).state.Label,
          ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
            ((forwardIterateM U cap n).state.root i) < X ∧
          X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
            ((forwardIterateM U cap n).state.root i)),
        eta ≤ fullGoodCoreTerminalMassM U cap ndRootCoreWidth n
          ((forwardIterateM U cap n).fullTerminalShift X hX hi) 1) :
    ∀ Y : ℕ, 64 * (H + 1) ≤ Y →
      eta / (64 * U.parentSourcePotential * generationExcessBound) * Y ≤
        (Terras.natCount (predecessorSetM a) Y : ℝ) := by
  classical
  intro Y hY
  have hYlarge : 64 * ((H : ℝ) + 1) ≤ Y := by exact_mod_cast hY
  set X := (Y : ℝ) / 64 with hXdef
  have hX : 0 < X := by rw [hXdef]; have := Nat.cast_nonneg (α := ℝ) H; linarith
  have hHX : (H : ℝ) < X := by rw [hXdef]; linarith
  have h64 : (64 : ℝ) * X = (Y : ℝ) := by rw [hXdef]; ring
  obtain ⟨n, hn, hi⟩ := exists_unstopped_generationM_all_intervals_contain U he cap hcap
    N hN X (fun i => (hH i).trans_lt hHX)
  have hif : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) := by
    rw [forwardIterateM_eq_iterateM U cap n]
    exact hi
  letI := (forwardIterateM U cap n).state.labelFintype
  have hm : eta ≤ fullGoodCoreTerminalMassM U cap ndRootCoreWidth n
      ((forwardIterateM U cap n).fullTerminalShift X hX hif) 1 := hmass n hn X hX hif
  have hwindow : ∀ z : FullTerminalAtM U cap n
      ((forwardIterateM U cap n).fullTerminalShift X hX hif) 1,
      X ≤ (sourceM z : ℝ) ∧ (sourceM z : ℝ) < 64 * X :=
    fun z => fullTerminalM_source_window (forwardIterateM U cap n) X hX hif z
  have hrange : fullGoodCoreTerminalSourcesM U cap ndRootCoreWidth n
      ((forwardIterateM U cap n).fullTerminalShift X hX hif) 1 ⊆ Finset.range Y := by
    intro source hs
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hs
    have h := (hwindow z).2
    have hlt : (sourceM z : ℝ) < Y := by linarith [h, h64]
    exact Finset.mem_range.mpr (by exact_mod_cast hlt)
  have htargetS : (↑(fullGoodCoreTerminalSourcesM U cap ndRootCoreWidth n
      ((forwardIterateM U cap n).fullTerminalShift X hX hif) 1) : Set ℕ) ⊆
      predecessorSetM a := by
    intro source hs
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hs
    exact fullTerminalM_reaches_of_seed_reaches U cap n _ 1 hreach z
  have hcard : (fullGoodCoreTerminalSourcesM U cap ndRootCoreWidth n
      ((forwardIterateM U cap n).fullTerminalShift X hX hif) 1).card ≤
      Terras.natCount (predecessorSetM a) Y :=
    finset_card_le_natCount_of_subset_range hrange htargetS
  have hcharge := fullGoodCoreTerminalM_mass_mul_lower_le_potential_mul_card U cap
    ndRootCoreWidth n ((forwardIterateM U cap n).fullTerminalShift X hX hif) 1 hseed
    X hX (fun z => (hwindow z).1)
  have hE : generationExcessProductM U cap (n + 1) ≤ generationExcessBound :=
    generationExcessProductM_le U cap (n + 1)
  have hcardR : ((fullGoodCoreTerminalSourcesM U cap ndRootCoreWidth n
      ((forwardIterateM U cap n).fullTerminalShift X hX hif) 1).card : ℝ) ≤
      (Terras.natCount (predecessorSetM a) Y : ℝ) := by exact_mod_cast hcard
  have hnn : (0 : ℝ) ≤ U.parentSourcePotential *
      ((fullGoodCoreTerminalSourcesM U cap ndRootCoreWidth n
        ((forwardIterateM U cap n).fullTerminalShift X hX hif) 1).card : ℝ) :=
    mul_nonneg hP.le (Nat.cast_nonneg _)
  have hstep1 : X * eta ≤ generationExcessProductM U cap (n + 1) *
      (U.parentSourcePotential *
        ((fullGoodCoreTerminalSourcesM U cap ndRootCoreWidth n
          ((forwardIterateM U cap n).fullTerminalShift X hX hif) 1).card : ℝ)) :=
    (mul_le_mul_of_nonneg_left hm hX.le).trans hcharge
  have hstep2 : X * eta ≤ generationExcessBound *
      (U.parentSourcePotential * (Terras.natCount (predecessorSetM a) Y : ℝ)) := by
    refine hstep1.trans ?_
    have h1 : generationExcessProductM U cap (n + 1) *
        (U.parentSourcePotential *
          ((fullGoodCoreTerminalSourcesM U cap ndRootCoreWidth n
            ((forwardIterateM U cap n).fullTerminalShift X hX hif) 1).card : ℝ)) ≤
        generationExcessBound *
          (U.parentSourcePotential *
            ((fullGoodCoreTerminalSourcesM U cap ndRootCoreWidth n
              ((forwardIterateM U cap n).fullTerminalShift X hX hif) 1).card : ℝ)) :=
      mul_le_mul_of_nonneg_right hE hnn
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcardR hP.le)
      generationExcessBound_pos.le
  have hden : (0 : ℝ) < 64 * U.parentSourcePotential * generationExcessBound :=
    mul_pos (mul_pos (by norm_num) hP) generationExcessBound_pos
  rw [div_mul_eq_mul_div, div_le_iff₀ hden, ← h64]
  have h4 := mul_le_mul_of_nonneg_left hstep2 (by norm_num : (0 : ℝ) ≤ 64)
  nlinarith only [h4]

end

end ThreeXMinusOne
