import ThreeXMinusOne.SharpCharge
import ThreeXMinusOne.TerminalPath
import ThreeXMinusOne.MassKernel

/-!
# The telescoped terminal charge

`fullTerminal_source_mul_weight_le_frozenOwner`, mirrored — and the place where Layer 9 is
finally spent.

The `+1` statement is a clean telescope: a terminal source times its weight is at most the
generation-zero root times its outer weight, with constant `1`, because each generation's charge
step has constant `1`.  The `3x−1` charge step has constant `1 + 3·(9/16)^b` (Layer 35), so `n`
generations accumulate `∏ (1 + 3·(9/16)^{floor_k})`.

That product is exactly what `Generations.generation_product_le` bounds.  The floor starts at
`200` and gains at least `2` per generation, so the excesses are dominated by a geometric series
and the whole product is at most `exp(3·(9/16)^200·256/175) = 1 + 4.6 × 10^(-50)`, **uniformly in
the number of generations**.  So the minus telescope is the plus telescope with the constant `1`
replaced by an absolute constant indistinguishable from `1`.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

variable {Label : Type*} {Labels : Finset Label} {root base shift : Label → ℕ} {b a K : ℕ}

/-- The weight of a physical minus incidence. -/
def weightM (outerWeight : Label → ℝ) (z : IncidenceM Label root base shift K) : ℝ :=
  outerWeight (labelM z) * atomM z

/-- The sharp charge at a unit child, weighted. -/
theorem ucSourceM_mul_ucWeightM_le_parent (outerWeight : Label → ℝ)
    (hweight : ∀ i, 0 ≤ outerWeight i) (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (z : UnitChildIncidenceM Labels root b a K) :
    (ucSourceM z : ℝ) * ucWeightM outerWeight z ≤
      (1 + chargeExcessM b) * ((root (ucLabelM z) : ℝ) * outerWeight (ucLabelM z)) := by
  have hsharp := sourceM_mul_atomM_le_root_sharp_uniform (b₀ := b) hrootOdd (fun _ => hb)
    (fun i => hrootLower i) (fun _ => le_rfl) (toPhysicalM z)
  have hw := hweight (ucLabelM z)
  have hmul := mul_le_mul_of_nonneg_left hsharp hw
  have hucA : ucAtomM z = atomM (toPhysicalM z) := by
    simp only [ucAtomM, atomM, toPhysicalM_depth, toPhysicalM_word]
  simp only [ucWeightM, ucSourceM, hucA, toPhysicalM_label] at *
  nlinarith [hmul]

/-- The accumulated generation excess, peeled from the front. -/
def generationExcessProductM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (1 + chargeExcessM U.floor) *
      generationExcessProductM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n

theorem generationExcessProductM_nonneg (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) : 0 ≤ generationExcessProductM U cap n := by
  induction n generalizing U cap with
  | zero => norm_num [generationExcessProductM]
  | succ n ih =>
      have h := chargeExcessM_nonneg U.floor
      exact mul_nonneg (by linarith) (ih _ _)

theorem generationExcessProductM_eq_prod
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ) :
    generationExcessProductM U cap n =
      ∏ k ∈ Finset.range n, (1 + chargeExcessM (forwardIterateM U cap k).floor) := by
  induction n generalizing U cap with
  | zero => simp [generationExcessProductM]
  | succ n ih =>
      rw [generationExcessProductM, ih, Finset.prod_range_succ']
      simp only [forwardIterateM_zero, forwardIterateM_succ]
      ring

/-- **The whole product is `1 + 4.6 × 10^(-50)`, uniformly in `n`.** -/
theorem generationExcessProductM_le
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ) :
    generationExcessProductM U cap n ≤
      Real.exp (3 * (9 / 16 : ℝ) ^ 200 * (256 / 175 : ℝ)) := by
  rw [generationExcessProductM_eq_prod]
  refine generation_product_le (fun k => chargeExcessM (forwardIterateM U cap k).floor)
    (fun k => chargeExcessM_nonneg _) (fun k => (forwardIterateM U cap k).floor)
    (by simpa using U.floor_twoHundred) (fun k => ?_) (fun k => le_rfl) n
  dsimp only
  rw [forwardIterateM_eq_iterateM, forwardIterateM_eq_iterateM]
  exact iterateM_floor_step U cap k

/-- **The telescoped terminal charge.**  `+1` has this with the product replaced by `1`. -/
theorem fullTerminalM_source_mul_weight_le_owner
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    (shift : (forwardIterateM U cap n).state.Label → ℕ) (K : ℕ)
    (z : FullTerminalAtM U cap n shift K) :
    (sourceM z : ℝ) * weightM (forwardIterateM U cap n).state.outerWeight z ≤
      generationExcessProductM U cap (n + 1) *
        ((U.state.root (fullTerminalAncestorM z) : ℝ) *
          U.state.outerWeight (fullTerminalAncestorM z)) := by
  induction n generalizing U cap with
  | zero =>
      have hsharp := sourceM_mul_atomM_le_root_sharp_uniform (b₀ := U.floor)
        U.state.root_odd (fun _ => by have h := U.floor_twoHundred; omega)
        (fun i => (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans
          (U.state.rootLower i)) (fun _ => le_rfl) z
      have hw := U.state.weight_nonneg (labelM z)
      have h := mul_le_mul_of_nonneg_left hsharp hw
      have hgoal : (sourceM z : ℝ) * (U.state.outerWeight (labelM z) * atomM z) ≤
          (1 + chargeExcessM U.floor) *
            ((U.state.root (labelM z) : ℝ) * U.state.outerWeight (labelM z)) := by
        calc (sourceM z : ℝ) * (U.state.outerWeight (labelM z) * atomM z)
            = U.state.outerWeight (labelM z) * ((sourceM z : ℝ) * atomM z) := by ring
          _ ≤ U.state.outerWeight (labelM z) *
              ((1 + chargeExcessM U.floor) * (U.state.root (labelM z) : ℝ)) := h
          _ = (1 + chargeExcessM U.floor) *
              ((U.state.root (labelM z) : ℝ) * U.state.outerWeight (labelM z)) := by ring
      simp only [generationExcessProductM, weightM, fullTerminalAncestorM, forwardAncestorM,
        forwardIterateM_zero, mul_one]
      exact hgoal
  | succ n ih =>
      have ht := ih (U := nextFloorM U (cap 0)) (cap := ndGeom2RootSideCapTail cap) shift z
      set j := forwardAncestorM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n
        (labelM z) with hj
      have hchild : ((nextFloorM U (cap 0)).state.root j : ℝ) *
          (nextFloorM U (cap 0)).state.outerWeight j =
            (ucSourceM j : ℝ) * ucWeightM U.state.outerWeight j := by
        simp only [nextFloorM, nextM, ucWeightM, ucAtomM, atomM,
          toPhysicalM_depth, toPhysicalM_word]
      have hstep := ucSourceM_mul_ucWeightM_le_parent U.state.outerWeight
        U.state.weight_nonneg U.state.root_odd
        (by have h := U.floor_twoHundred; omega)
        (fun i => (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans
          (U.state.rootLower i)) j
      have hP := generationExcessProductM_nonneg (nextFloorM U (cap 0))
        (ndGeom2RootSideCapTail cap) (n + 1)
      have hchain : generationExcessProductM (nextFloorM U (cap 0))
            (ndGeom2RootSideCapTail cap) (n + 1) *
          ((nextFloorM U (cap 0)).state.root j * (nextFloorM U (cap 0)).state.outerWeight j) ≤
        generationExcessProductM U cap (n + 2) *
          ((U.state.root (ucLabelM j) : ℝ) * U.state.outerWeight (ucLabelM j)) := by
        rw [hchild]
        calc generationExcessProductM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) (n + 1) *
              ((ucSourceM j : ℝ) * ucWeightM U.state.outerWeight j)
            ≤ generationExcessProductM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) (n + 1) *
              ((1 + chargeExcessM U.floor) *
                ((U.state.root (ucLabelM j) : ℝ) * U.state.outerWeight (ucLabelM j))) :=
              mul_le_mul_of_nonneg_left hstep hP
          _ = generationExcessProductM U cap (n + 2) *
              ((U.state.root (ucLabelM j) : ℝ) * U.state.outerWeight (ucLabelM j)) := by
              simp only [generationExcessProductM]; ring
      exact ht.trans (by
        simpa only [hj, fullTerminalAncestorM, forwardAncestorM] using hchain)

end

end ThreeXMinusOne
