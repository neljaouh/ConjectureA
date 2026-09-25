import ThreeXMinusOne.RootHistogram
import ThreeXMinusOne.SelectedWord
import ThreeXMinusOne.GoodCoreCensus
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootUniformCoreCapacity

/-!
# The core band, and the bridge from the filter factor to it

`coreBaseSum`, `coreWidthSum`, `forwardCore`, `forwardCore_depth_band`, `forwardWord_total_band`
and `forwardCore_pair_mem`, mirrored.

The capacity argument needs each surviving descent to land in a bounded grid of
(length, weight) pairs.  Length is bounded by the core filter itself; weight is bounded by the
selected-word band, which is word-only and so is the artifact's own
(`rootCore_selectedWord_total_band`, fed by Layer 22's `selectedWordM`).

**The bridge.**  Layers 29 and 44 carry the core filter as a real factor, while the grid argument
wants a proposition.  `forwardCoreM` is that proposition, and `forwardCoreFactorM_pos_iff` says
the two agree: the factor is a product of `{0,1}`-valued band indicators, so it is positive
exactly when every band holds.  That is the reason the real-valued encoding cost nothing — it
carries the same information, and converting is one induction.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

/-- Accumulated floors along the descent. -/
def coreBaseSumM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) :
    ℕ → ℕ
  | 0 => 0
  | n + 1 => U.floor + coreBaseSumM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n

/-- Accumulated band widths along the descent. -/
def coreWidthSumM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => width U.floor +
      coreWidthSumM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) width n

/-- The core condition as a proposition. -/
def forwardCoreM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) : (n : ℕ) → (forwardIterateM U cap n).state.Label → Prop
  | 0, _ => True
  | n + 1, z =>
      let d := ucDepthM (forwardFirstIncidenceM U cap n z)
      U.floor ≤ d + width U.floor ∧ d ≤ U.floor + width U.floor ∧
        forwardCoreM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) width n z

/-- **The bridge**: the real filter factor is positive exactly on the core. -/
theorem forwardCoreFactorM_pos_iff (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (z : (forwardIterateM U cap n).state.Label) :
    0 < forwardCoreFactorM U cap width n z ↔ forwardCoreM U cap width n z := by
  induction n generalizing U cap with
  | zero => simp [forwardCoreFactorM, forwardCoreM]
  | succ n ih =>
      have ih' := ih (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) z
      have hnn := forwardCoreFactorM_nonneg (nextFloorM U (cap 0))
        (ndGeom2RootSideCapTail cap) width n z
      constructor
      · intro h
        change 0 < ndRootCoreWordFilter U.floor (width U.floor)
          (ucWordM (forwardFirstIncidenceM U cap n z)) *
          forwardCoreFactorM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) width n z at h
        have hf : 0 < ndRootCoreWordFilter U.floor (width U.floor)
            (ucWordM (forwardFirstIncidenceM U cap n z)) := by
          by_contra hc
          have : ndRootCoreWordFilter U.floor (width U.floor)
              (ucWordM (forwardFirstIncidenceM U cap n z)) = 0 := by
            have := rootCoreWordFilter_nonneg U.floor (width U.floor)
              (ucWordM (forwardFirstIncidenceM U cap n z))
            linarith
          rw [this, zero_mul] at h
          exact lt_irrefl _ h
        have htail : 0 < forwardCoreFactorM (nextFloorM U (cap 0))
            (ndGeom2RootSideCapTail cap) width n z := by
          rcases lt_or_eq_of_le hnn with hp | he
          · exact hp
          · rw [← he, mul_zero] at h; exact absurd h (lt_irrefl _)
        have hband : ndRootCoreWordFilter U.floor (width U.floor)
            (ucWordM (forwardFirstIncidenceM U cap n z)) = 1 := by
          unfold ndRootCoreWordFilter at hf ⊢
          split_ifs at hf ⊢ with hb
          · rfl
          · exact absurd hf (lt_irrefl _)
        have hb : U.floor ≤ (ucWordM (forwardFirstIncidenceM U cap n z)).length + width U.floor ∧
            (ucWordM (forwardFirstIncidenceM U cap n z)).length ≤ U.floor + width U.floor := by
          unfold ndRootCoreWordFilter at hband
          split_ifs at hband with hc
          · exact hc
          · norm_num at hband
        rw [ucWordM_length] at hb
        exact ⟨hb.1, hb.2, ih'.mp htail⟩
      · intro h
        obtain ⟨h1, h2, h3⟩ := h
        change 0 < ndRootCoreWordFilter U.floor (width U.floor)
          (ucWordM (forwardFirstIncidenceM U cap n z)) *
          forwardCoreFactorM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) width n z
        have hband : ndRootCoreWordFilter U.floor (width U.floor)
            (ucWordM (forwardFirstIncidenceM U cap n z)) = 1 := by
          unfold ndRootCoreWordFilter
          rw [if_pos]
          rw [ucWordM_length]
          exact ⟨h1, h2⟩
        rw [hband, one_mul]
        exact ih'.mpr h3

/-- The factor is a product of `{0,1}` values, so positive forces exactly `1`. -/
theorem forwardCoreFactorM_eq_one_of_pos
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ) (n : ℕ)
    (z : (forwardIterateM U cap n).state.Label)
    (h : 0 < forwardCoreFactorM U cap width n z) :
    forwardCoreFactorM U cap width n z = 1 := by
  induction n generalizing U cap with
  | zero => rfl
  | succ n ih =>
      change 0 < ndRootCoreWordFilter U.floor (width U.floor)
        (ucWordM (forwardFirstIncidenceM U cap n z)) *
        forwardCoreFactorM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) width n z at h
      have hfnn := rootCoreWordFilter_nonneg U.floor (width U.floor)
        (ucWordM (forwardFirstIncidenceM U cap n z))
      have htnn := forwardCoreFactorM_nonneg (nextFloorM U (cap 0))
        (ndGeom2RootSideCapTail cap) width n z
      have hf : 0 < ndRootCoreWordFilter U.floor (width U.floor)
          (ucWordM (forwardFirstIncidenceM U cap n z)) := by
        rcases lt_or_eq_of_le hfnn with hp | he
        · exact hp
        · rw [← he, zero_mul] at h; exact absurd h (lt_irrefl _)
      have ht : 0 < forwardCoreFactorM (nextFloorM U (cap 0))
          (ndGeom2RootSideCapTail cap) width n z := by
        rcases lt_or_eq_of_le htnn with hp | he
        · exact hp
        · rw [← he, mul_zero] at h; exact absurd h (lt_irrefl _)
      have hf1 : ndRootCoreWordFilter U.floor (width U.floor)
          (ucWordM (forwardFirstIncidenceM U cap n z)) = 1 := by
        unfold ndRootCoreWordFilter at hf ⊢
        split_ifs at hf ⊢
        · rfl
        · exact absurd hf (lt_irrefl _)
      change ndRootCoreWordFilter U.floor (width U.floor)
        (ucWordM (forwardFirstIncidenceM U cap n z)) *
        forwardCoreFactorM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) width n z = 1
      rw [hf1, one_mul]
      exact ih _ _ z ht

/-- The length band along a whole descent. -/
theorem forwardCoreM_depth_band (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (z : (forwardIterateM U cap n).state.Label)
    (hz : forwardCoreM U cap width n z) :
    coreBaseSumM U cap n ≤ (forwardWordM U cap n z).length + coreWidthSumM U cap width n ∧
      (forwardWordM U cap n z).length ≤ coreBaseSumM U cap n + coreWidthSumM U cap width n := by
  induction n generalizing U cap with
  | zero => simp [coreBaseSumM, coreWidthSumM, forwardWordM]
  | succ n ih =>
      have h := ih (U := nextFloorM U (cap 0)) (cap := ndGeom2RootSideCapTail cap) z hz.2.2
      simp only [forwardWordM, List.length_append, ucWordM_length, coreBaseSumM, coreWidthSumM]
      have hl := hz.1
      have hu := hz.2.1
      constructor <;> omega

/-- The weight band along a whole descent.  Word-only input, so the artifact's own. -/
theorem forwardWordM_total_band (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (z : (forwardIterateM U cap n).state.Label) :
    2 * coreBaseSumM U cap n + ndBalancedTotal (forwardWordM U cap n z).length ≤
        Tao.taoTupleWeight (forwardWordM U cap n z) +
          ndBalancedTotal (coreBaseSumM U cap n) + 2 * n ∧
      Tao.taoTupleWeight (forwardWordM U cap n z) + ndBalancedTotal (coreBaseSumM U cap n) ≤
        2 * coreBaseSumM U cap n + ndBalancedTotal (forwardWordM U cap n z).length +
          ndRootCoreCapSum cap n + 2 * n := by
  induction n generalizing U cap with
  | zero => simp [coreBaseSumM, forwardWordM, ndRootCoreCapSum]
  | succ n ih =>
      set iz := forwardFirstIncidenceM U cap n z with hiz
      set w := ucWordM iz with hw
      set v := forwardWordM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n z with hv
      set B := coreBaseSumM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n with hB
      have hband := rootCore_selectedWord_total_band (selectedWordM iz).2.property
      have ht := ih (U := nextFloorM U (cap 0)) (cap := ndGeom2RootSideCapTail cap) z
      rw [← hv, ← hB] at ht
      have hdlo := ndBalancedTotal_add_le w.length v.length
      have hdhi := rootCore_balanced_add_reverse_le w.length v.length
      have hblo := ndBalancedTotal_add_le U.floor B
      have hbhi := rootCore_balanced_add_reverse_le U.floor B
      change 2 * U.floor + ndBalancedTotal w.length ≤
          Tao.taoTupleWeight w + ndBalancedTotal U.floor + 1 ∧
        Tao.taoTupleWeight w + ndBalancedTotal U.floor ≤
          2 * U.floor + ndBalancedTotal w.length + cap 0 + 1 at hband
      simp only [forwardWordM, List.length_append, Tao.taoTupleWeight_append, coreBaseSumM,
        ndRootCoreCapSum]
      change 2 * (U.floor + B) + ndBalancedTotal (w.length + v.length) ≤
          Tao.taoTupleWeight w + Tao.taoTupleWeight v +
            ndBalancedTotal (U.floor + B) + 2 * (n + 1) ∧
        Tao.taoTupleWeight w + Tao.taoTupleWeight v + ndBalancedTotal (U.floor + B) ≤
          2 * (U.floor + B) + ndBalancedTotal (w.length + v.length) +
            (cap 0 + ndRootCoreCapSum (ndGeom2RootSideCapTail cap) n) + 2 * (n + 1)
      constructor <;> omega

theorem forwardCoreM_pair_mem (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (z : (forwardIterateM U cap n).state.Label)
    (hz : forwardCoreM U cap width n z) :
    ((forwardWordM U cap n z).length, Tao.taoTupleWeight (forwardWordM U cap n z)) ∈
      ndRootCorePairs (coreBaseSumM U cap n) (coreWidthSumM U cap width n)
        (ndRootCoreCapSum cap n) n := by
  have hd := forwardCoreM_depth_band U cap width n z hz
  have ha := forwardWordM_total_band U cap n z
  exact rootCorePairs_mem hd.1 hd.2 ha.1 ha.2

end

end ThreeXMinusOne
