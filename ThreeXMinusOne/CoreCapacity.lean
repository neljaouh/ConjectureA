import ThreeXMinusOne.CoreBand

/-!
# The core histogram and its capacity budget

`forwardCoreHistogram`, `forwardCoreHistogram_le_sum_groups`,
`threePow_mul_forwardCoreHistogram_le_rootUniform`, `coreCapacityBudget`,
`forwardCoreHistogram_pairing` and `abs_coreHistogram_pairing_le_capacity_fullL1`, mirrored.

The core histogram is the weight the surviving descents put on one residue class.  Layer 54
confines each surviving descent to a bounded grid of (length, weight) pairs, Layer 53 bounds each
grid cell's contribution, and `rootCorePairs_card_le` — map-free, the artifact's own — bounds the
number of cells.  Multiplying gives the capacity budget: no single residue class carries more
than `budget / 3^q` of the weight, so pairing the histogram against any function is controlled by
that function's mean.

The budget differs from `+1`'s only in the factor Layer 52 introduced: where `+1` has
`16^floor·(9/16)^floor_n`, the minus budget has `excess(n)·16^floor·(9/16)^floor_n`, with the
excess bounded by `1 + 4.6×10^(-50)` uniformly.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

variable (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ) (n : ℕ)

/-- The total outer weight at generation zero. -/
def denominatorM : ℝ := by
  classical
  letI := U.state.labelFintype
  exact ∑ i : U.state.Label, U.state.outerWeight i

theorem denominatorM_nonneg : 0 ≤ denominatorM U := by
  classical
  letI := U.state.labelFintype
  exact Finset.sum_nonneg fun i _ => U.state.weight_nonneg i

/-- The weight the surviving descents put on one residue class. -/
def forwardCoreHistogramM (q : ℕ) (y : ZMod (3 ^ q)) : ℝ := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  exact ∑ z ∈ Finset.univ.filter (fun z => forwardCoreM U cap width n z ∧
      (((forwardIterateM U cap n).state.root z : ℕ) : ZMod (3 ^ q)) = y),
    (forwardIterateM U cap n).state.outerWeight z

theorem forwardCoreHistogramM_nonneg (q : ℕ) (y : ZMod (3 ^ q)) :
    0 ≤ forwardCoreHistogramM U cap width n q y := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  exact Finset.sum_nonneg fun z _ => (forwardIterateM U cap n).state.weight_nonneg z

theorem forwardCoreHistogramM_le_sum_groups (q : ℕ) (y : ZMod (3 ^ q)) :
    forwardCoreHistogramM U cap width n q y ≤
      letI := U.state.labelFintype;
      ∑ i, ∑ p ∈ ndRootCorePairs (coreBaseSumM U cap n) (coreWidthSumM U cap width n)
        (ndRootCoreCapSum cap n) n, forwardRootGroupHistogramM U cap n i p.1 p.2 q y := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  letI := U.state.labelFintype
  set G := ndRootCorePairs (coreBaseSumM U cap n) (coreWidthSumM U cap width n)
    (ndRootCoreCapSum cap n) n with hG
  set P := (Finset.univ : Finset U.state.Label).product G with hP
  set S := Finset.univ.filter (fun z : (forwardIterateM U cap n).state.Label =>
    forwardCoreM U cap width n z ∧
      (((forwardIterateM U cap n).state.root z : ℕ) : ZMod (3 ^ q)) = y) with hS
  set key := fun z : (forwardIterateM U cap n).state.Label => (forwardAncestorM U cap n z,
    ((forwardWordM U cap n z).length, Tao.taoTupleWeight (forwardWordM U cap n z))) with hkey
  have hcover : ∀ z ∈ S, key z ∈ P := by
    intro z hz
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
      forwardCoreM_pair_mem U cap width n z (Finset.mem_filter.mp hz).2.1⟩
  calc forwardCoreHistogramM U cap width n q y
      = ∑ z ∈ S, ∑ p ∈ P,
          if key z = p then (forwardIterateM U cap n).state.outerWeight z else 0 := by
        refine Finset.sum_congr rfl fun z hz => ?_
        simp only [Finset.sum_ite_eq, hcover z hz, if_true]
    _ = ∑ p ∈ P, ∑ z ∈ S,
          if key z = p then (forwardIterateM U cap n).state.outerWeight z else 0 :=
        Finset.sum_comm
    _ ≤ ∑ p ∈ P, forwardRootGroupHistogramM U cap n p.1 p.2.1 p.2.2 q y := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [← Finset.sum_filter]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z _ _ =>
          (forwardIterateM U cap n).state.weight_nonneg z)
        intro z hz
        obtain ⟨hzS, hk⟩ := Finset.mem_filter.mp hz
        have ha : forwardAncestorM U cap n z = p.1 := congrArg Prod.fst hk
        have hd : (forwardWordM U cap n z).length = p.2.1 := congrArg (fun x => x.2.1) hk
        have hA : Tao.taoTupleWeight (forwardWordM U cap n z) = p.2.2 :=
          congrArg (fun x => x.2.2) hk
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hd, hA⟩,
          (Finset.mem_filter.mp hzS).2.2⟩
    _ = _ := Finset.sum_product _ _ _

/-- The capacity budget.  `+1` has the excess product as `1`. -/
def coreCapacityBudgetM : ℝ :=
  denominatorM U * (((2 * coreWidthSumM U cap width n + 1) *
    (ndRootCoreCapSum cap n + 4 * n + 1) : ℕ) : ℝ) *
      ((2 : ℝ) ^ (U.floor + 1) + generationExcessProductM U cap n * (16 : ℝ) ^ U.floor *
        (9 / 16 : ℝ) ^ (forwardIterateM U cap n).floor)

theorem coreCapacityBudgetM_nonneg : 0 ≤ coreCapacityBudgetM U cap width n := by
  have hP := generationExcessProductM_nonneg U cap n
  have hD := denominatorM_nonneg U
  unfold coreCapacityBudgetM
  have hlast : (0 : ℝ) ≤ (2 : ℝ) ^ (U.floor + 1) +
      generationExcessProductM U cap n * (16 : ℝ) ^ U.floor *
        (9 / 16 : ℝ) ^ (forwardIterateM U cap n).floor := by positivity
  positivity

theorem threePow_mul_forwardCoreHistogramM_le_rootUniform (q : ℕ)
    (hq : q ≤ 2 * (forwardIterateM U cap n).floor) (y : ZMod (3 ^ q)) :
    (3 : ℝ) ^ q * forwardCoreHistogramM U cap width n q y ≤
      coreCapacityBudgetM U cap width n := by
  classical
  letI := U.state.labelFintype
  set G := ndRootCorePairs (coreBaseSumM U cap n) (coreWidthSumM U cap width n)
    (ndRootCoreCapSum cap n) n with hG
  set C := (2 : ℝ) ^ (U.floor + 1) + generationExcessProductM U cap n * (16 : ℝ) ^ U.floor *
    (9 / 16 : ℝ) ^ (forwardIterateM U cap n).floor with hC
  have hCnn : 0 ≤ C := by
    have := generationExcessProductM_nonneg U cap n
    rw [hC]; positivity
  have hD := denominatorM_nonneg U
  calc (3 : ℝ) ^ q * forwardCoreHistogramM U cap width n q y
      ≤ ∑ i : U.state.Label, ∑ p ∈ G,
          (3 : ℝ) ^ q * forwardRootGroupHistogramM U cap n i p.1 p.2 q y := by
        simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left
          (forwardCoreHistogramM_le_sum_groups U cap width n q y)
          (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ q)
    _ ≤ ∑ i : U.state.Label, ∑ _p ∈ G, U.state.outerWeight i * C := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun p _ => ?_
        exact threePow_mul_forwardRootGroupHistogramM_le_rootUniform_edge U cap n i p.1 p.2 q hq y
    _ = denominatorM U * (G.card : ℝ) * C := by
        change _ = (∑ i : U.state.Label, U.state.outerWeight i) * (G.card : ℝ) * C
        simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
        ring
    _ ≤ coreCapacityBudgetM U cap width n := by
        refine mul_le_mul_of_nonneg_right ?_ hCnn
        refine mul_le_mul_of_nonneg_left ?_ hD
        exact_mod_cast rootCorePairs_card_le (coreBaseSumM U cap n)
          (coreWidthSumM U cap width n) (ndRootCoreCapSum cap n) n

theorem forwardCoreHistogramM_pairing (q : ℕ) (g : ZMod (3 ^ q) → ℝ) :
    (∑ y, forwardCoreHistogramM U cap width n q y * g y) =
      letI := (forwardIterateM U cap n).state.labelFintype;
      ∑ i, forwardCoreOuterWeightM U cap width n i *
        g ((((forwardIterateM U cap n).state.root i : ℕ) : ZMod (3 ^ q))) := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  unfold forwardCoreHistogramM
  simp_rw [Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hc : forwardCoreM U cap width n i
  · have hfac : forwardCoreFactorM U cap width n i = 1 := by
      have hpos := (forwardCoreFactorM_pos_iff U cap width n i).mpr hc
      have hle := forwardCoreFactorM_le_one U cap width n i
      -- the factor is a product of `{0,1}` values, so positive forces `1`
      by_contra hne
      have hlt : forwardCoreFactorM U cap width n i < 1 := lt_of_le_of_ne hle hne
      exact absurd (forwardCoreFactorM_eq_one_of_pos U cap width n i hpos) hne
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, hc, and_true,
      forwardCoreOuterWeightM, hfac, one_mul]
    simp
  · simp only [hc, false_and, if_false, Finset.sum_const_zero]
    have hfac : forwardCoreFactorM U cap width n i = 0 := by
      by_contra hne
      have hnn := forwardCoreFactorM_nonneg U cap width n i
      exact hc ((forwardCoreFactorM_pos_iff U cap width n i).mp (lt_of_le_of_ne hnn (Ne.symm hne)))
    simp [forwardCoreOuterWeightM, hfac]

theorem abs_coreHistogramM_pairing_le_capacity (q : ℕ)
    (hq : q ≤ 2 * (forwardIterateM U cap n).floor) (g : ZMod (3 ^ q) → ℝ) :
    |∑ y, forwardCoreHistogramM U cap width n q y * g y| ≤
      coreCapacityBudgetM U cap width n * ndTernaryUniformMean q (fun y => |g y|) := by
  have hqpos : (0 : ℝ) < 3 ^ q := by positivity
  have hcap (y : ZMod (3 ^ q)) : forwardCoreHistogramM U cap width n q y ≤
      coreCapacityBudgetM U cap width n / (3 : ℝ) ^ q := by
    apply (le_div_iff₀ hqpos).mpr
    simpa only [mul_comm] using
      threePow_mul_forwardCoreHistogramM_le_rootUniform U cap width n q hq y
  calc |∑ y, forwardCoreHistogramM U cap width n q y * g y|
      ≤ ∑ y, |forwardCoreHistogramM U cap width n q y * g y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, forwardCoreHistogramM U cap width n q y * |g y| := by
        simp only [abs_mul, abs_of_nonneg (forwardCoreHistogramM_nonneg U cap width n q _)]
    _ ≤ ∑ y, coreCapacityBudgetM U cap width n / (3 : ℝ) ^ q * |g y| :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (hcap y) (abs_nonneg _)
    _ = _ := by
        rw [← Finset.mul_sum]
        unfold ndTernaryUniformMean ndTernaryUniformScale
        push_cast
        ring

end

end ThreeXMinusOne
