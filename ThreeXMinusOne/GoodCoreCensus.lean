import ThreeXMinusOne.CoreTerminalMass
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalDepthShiftCensus

/-!
# The good-core terminal census

The weights, mass and source set of `Geom2ShiftedWideSymmetricTerminalDepthShiftCensus`,
mirrored.

Two filters are applied to a terminal incidence before it is counted: the *core* filter, which
Layers 29–30 carry as a real factor along the descent, and the *depth-shift* filter
`ndTerminalDepthShiftGood`, which asks that the terminal depth sit in the band the chosen shift
index selects.  The second is word-and-depth only — it never sees a root or a residue — so
`ndTerminalDepthShiftGood` and its indicator are the artifact's own, used verbatim.

The source set is where the two filters have to become a *decidable predicate* rather than a
weight, because a `Finset.filter` needs one.  The `3x−1` core filter is a real number, so the
condition is `0 < forwardCoreFactorM …` — equivalent to the `+1` `forwardCore …` because the
factor is a product of `{0,1}`-valued word filters, and stated this way it needs no `Decidable`
instance beyond `Classical`.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

private theorem rootCoreWordFilter_le_one (b m : ℕ) (w : List ℕ+) :
    ndRootCoreWordFilter b m w ≤ 1 := by
  unfold ndRootCoreWordFilter
  split_ifs <;> norm_num

theorem forwardCoreFactorM_le_one (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (z : (forwardIterateM U cap n).state.Label) :
    forwardCoreFactorM U cap width n z ≤ 1 := by
  induction n generalizing U cap with
  | zero => norm_num [forwardCoreFactorM]
  | succ n ih =>
      have h1 := rootCoreWordFilter_le_one U.floor (width U.floor)
        (ucWordM (forwardFirstIncidenceM U cap n z))
      have h0 := rootCoreWordFilter_nonneg U.floor (width U.floor)
        (ucWordM (forwardFirstIncidenceM U cap n z))
      have h2 := ih (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) z
      have h3 := forwardCoreFactorM_nonneg (nextFloorM U (cap 0))
        (ndGeom2RootSideCapTail cap) width n z
      change ndRootCoreWordFilter U.floor (width U.floor) _ *
        forwardCoreFactorM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) width n z ≤ 1
      nlinarith

theorem forwardCoreOuterWeightM_le_original
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ) (n : ℕ)
    (i : (forwardIterateM U cap n).state.Label) :
    forwardCoreOuterWeightM U cap width n i ≤ (forwardIterateM U cap n).state.outerWeight i := by
  unfold forwardCoreOuterWeightM
  have h1 := forwardCoreFactorM_le_one U cap width n i
  have h2 := (forwardIterateM U cap n).state.weight_nonneg i
  nlinarith

/-- The terminal weight after both filters. -/
def fullGoodCoreTerminalWeightM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (shift : (forwardIterateM U cap n).state.Label → ℕ) (K : ℕ)
    (z : FullTerminalAtM U cap n shift K) : ℝ :=
  weightM (forwardCoreOuterWeightM U cap width n) z *
    ndTerminalDepthShiftIndicator (forwardIterateM U cap n).floor (shift (labelM z)) (depthM z)

theorem fullGoodCoreTerminalWeightM_nonneg
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ) (n : ℕ)
    (shift : (forwardIterateM U cap n).state.Label → ℕ) (K : ℕ)
    (z : FullTerminalAtM U cap n shift K) :
    0 ≤ fullGoodCoreTerminalWeightM U cap width n shift K z :=
  mul_nonneg (weightM_nonneg _ (forwardCoreOuterWeightM_nonneg U cap width n) z)
    (terminalDepthShiftIndicator_nonneg _ _ _)

theorem fullGoodCoreTerminalWeightM_le_original
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ) (n : ℕ)
    (shift : (forwardIterateM U cap n).state.Label → ℕ) (K : ℕ)
    (z : FullTerminalAtM U cap n shift K) :
    fullGoodCoreTerminalWeightM U cap width n shift K z ≤
      weightM (forwardIterateM U cap n).state.outerWeight z := by
  have hw := weightM_nonneg _ (forwardCoreOuterWeightM_nonneg U cap width n) z
  refine (mul_le_mul_of_nonneg_left (terminalDepthShiftIndicator_le_one _ _ _) hw).trans ?_
  rw [mul_one]
  unfold weightM
  have h1 := forwardCoreOuterWeightM_le_original U cap width n (labelM z)
  have h2 := atomM_nonneg z
  nlinarith

/-- The good-core terminal mass. -/
def fullGoodCoreTerminalMassM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (shift : (forwardIterateM U cap n).state.Label → ℕ) (K : ℕ) :
    ℝ := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  exact ∑ z : FullTerminalAtM U cap n shift K, fullGoodCoreTerminalWeightM U cap width n shift K z

/-- The sources that survive both filters. -/
def fullGoodCoreTerminalSourcesM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (shift : (forwardIterateM U cap n).state.Label → ℕ) (K : ℕ) :
    Finset ℕ := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  exact (Finset.univ.filter fun z : FullTerminalAtM U cap n shift K =>
    0 < forwardCoreFactorM U cap width n (labelM z) ∧
      ndTerminalDepthShiftGood (forwardIterateM U cap n).floor (shift (labelM z))
        (depthM z)).image sourceM

theorem fullGoodCoreTerminalSourcesM_subset
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ) (n : ℕ)
    (shift : (forwardIterateM U cap n).state.Label → ℕ) (K : ℕ) :
    fullGoodCoreTerminalSourcesM U cap width n shift K ⊆
      fullTerminalSourcesM U cap n shift K := by
  classical
  exact Finset.image_mono _ (Finset.filter_subset _ _)

end

end ThreeXMinusOne
