import ThreeXMinusOne.BudgetBridge
import ThreeXMinusOne.CoreCapacity
import ThreeXMinusOne.ForwardCoreMass

/-!
# The core-mass increment

`forwardLastIncidenceEquiv`, `forwardCoreMarkedMass_succ_eq_kernel`,
`forwardCoreHistogram_referenceMark_pairing` and
`forwardCoreMarkedMass_increment_eq_histogram`, mirrored.

The variation argument needs the *difference* between consecutive core masses to be a single
pairing of the core histogram against a kernel difference.  Getting there means reading the
`(n+1)`-st generation from the back — as one more unit-child step on the `n`-th — rather than
from the front, which is how Layer 30 built it.  `forwardIterateM_succ_eq_next` is that
reconciliation, and it follows from Layer 28's `forwardIterateM_eq_iterateM` in one line.

The residue flip appears exactly where it has all along: the kernel is read at `−(root)`, and
Layer 55's histogram pairing is stated at the positive residue, so the negated pairing of
Layer 56 is what gets used.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

/-- The back-peeling view of one more generation. -/
theorem forwardIterateM_succ_eq_next
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ) :
    forwardIterateM U cap (n + 1) = nextFloorM (forwardIterateM U cap n) (cap n) := by
  rw [forwardIterateM_eq_iterateM, forwardIterateM_eq_iterateM]
  rfl

def forwardLastIncidenceEquivM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    (forwardIterateM U cap (n + 1)).state.Label ≃
      (nextFloorM (forwardIterateM U cap n) (cap n)).state.Label :=
  Equiv.cast (congrArg (fun V => V.state.Label) (forwardIterateM_succ_eq_next U cap n))

def forwardLastParentM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (z : (forwardIterateM U cap (n + 1)).state.Label) :
    (forwardIterateM U cap n).state.Label :=
  ucLabelM (forwardLastIncidenceEquivM U cap n z)

theorem forwardFirstIncidenceM_lastParent_eq
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    (z : (forwardIterateM U cap (n + 2)).state.Label) :
    forwardFirstIncidenceM U cap n (forwardLastParentM U cap (n + 1) z) =
      forwardFirstIncidenceM U cap (n + 1) z := by
  induction n generalizing U cap with
  | zero => rfl
  | succ n ih =>
      change ucLabelM (forwardFirstIncidenceM (nextFloorM U (cap 0))
          (ndGeom2RootSideCapTail cap) n
          (forwardLastParentM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) (n + 1) z)) =
        ucLabelM (forwardFirstIncidenceM (nextFloorM U (cap 0))
          (ndGeom2RootSideCapTail cap) (n + 1) z)
      exact congrArg ucLabelM (ih (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) z)

theorem forwardCoreM_iff_last_parent_and_strip
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ) (n : ℕ)
    (z : (forwardIterateM U cap (n + 1)).state.Label) :
    forwardCoreM U cap width (n + 1) z ↔
      forwardCoreM U cap width n (forwardLastParentM U cap n z) ∧
        ((forwardIterateM U cap n).floor ≤
            (ucWordM (forwardLastIncidenceEquivM U cap n z)).length +
              width (forwardIterateM U cap n).floor ∧
          (ucWordM (forwardLastIncidenceEquivM U cap n z)).length ≤
            (forwardIterateM U cap n).floor + width (forwardIterateM U cap n).floor) := by
  induction n generalizing U cap with
  | zero =>
      simp only [forwardCoreM, ucWordM_length, and_true, true_and]
      rfl
  | succ n ih =>
      have ht := ih (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) z
      have hf := forwardFirstIncidenceM_lastParent_eq U cap n z
      simp only [forwardCoreM]
      rw [hf]
      change (_ ∧ _ ∧ forwardCoreM (nextFloorM U (cap 0))
          (ndGeom2RootSideCapTail cap) width (n + 1) z) ↔
        (_ ∧ _ ∧ forwardCoreM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) width n
          (forwardLastParentM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n z)) ∧ _
      rw [ht]
      tauto

private theorem state_cast_weightM
    {V W : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState} (h : V = W) (z : V.state.Label) :
    W.state.outerWeight (Equiv.cast (congrArg (fun T => T.state.Label) h) z) =
      V.state.outerWeight z := by
  cases h; rfl

private theorem state_cast_rootM
    {V W : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState} (h : V = W) (z : V.state.Label) :
    W.state.root (Equiv.cast (congrArg (fun T => T.state.Label) h) z) = V.state.root z := by
  cases h; rfl

theorem forwardLastIncidenceM_weight_eq
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    (z : (forwardIterateM U cap (n + 1)).state.Label) :
    ucWeightM (forwardIterateM U cap n).state.outerWeight (forwardLastIncidenceEquivM U cap n z) =
      (forwardIterateM U cap (n + 1)).state.outerWeight z :=
  state_cast_weightM (forwardIterateM_succ_eq_next U cap n) z

theorem forwardLastIncidenceM_source_eq
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    (z : (forwardIterateM U cap (n + 1)).state.Label) :
    ucSourceM (forwardLastIncidenceEquivM U cap n z) =
      (forwardIterateM U cap (n + 1)).state.root z :=
  state_cast_rootM (forwardIterateM_succ_eq_next U cap n) z

open Classical in
/-- The real filter factor *is* the `+1` indicator: this is what lets the rest of the variation
argument be a direct mirror. -/
theorem forwardCoreFactorM_eq_ite (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (z : (forwardIterateM U cap n).state.Label) :
    forwardCoreFactorM U cap width n z =
      if forwardCoreM U cap width n z then 1 else 0 := by
  classical
  by_cases h : forwardCoreM U cap width n z
  · rw [if_pos h]
    exact forwardCoreFactorM_eq_one_of_pos U cap width n z
      ((forwardCoreFactorM_pos_iff U cap width n z).mpr h)
  · rw [if_neg h]
    by_contra hne
    exact h ((forwardCoreFactorM_pos_iff U cap width n z).mp
      (lt_of_le_of_ne (forwardCoreFactorM_nonneg U cap width n z) (Ne.symm hne)))

open Classical in
theorem forwardCoreOuterWeightM_eq_ite (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) (i : (forwardIterateM U cap n).state.Label) :
    forwardCoreOuterWeightM U cap width n i =
      if forwardCoreM U cap width n i then (forwardIterateM U cap n).state.outerWeight i else 0 := by
  classical
  unfold forwardCoreOuterWeightM
  rw [forwardCoreFactorM_eq_ite]
  split_ifs <;> ring

/-- The core mass, written against the core-filtered outer weight. -/
theorem forwardCoreMassM_eq_outerWeight_sum
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ) (n k : ℕ) :
    forwardCoreMassM U cap width n k (fun _ => 1) =
      letI := (forwardIterateM U cap n).state.labelFintype
      ∑ z, forwardCoreOuterWeightM U cap width n z *
        ndSyracuseUnitReferenceDensity k
          (-(((forwardIterateM U cap n).state.root z : ℕ) : ZMod (3 ^ k))) := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  unfold forwardCoreMassM forwardCoreOuterWeightM
  exact Finset.sum_congr rfl fun z _ => by ring

/-- **One more generation, read from the back.** -/
theorem forwardCoreMassM_succ_eq_kernel
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ) (n k : ℕ)
    (hk : 1 ≤ k) :
    forwardCoreMassM U cap width (n + 1) k (fun _ => 1) =
      letI := (forwardIterateM U cap n).state.labelFintype
      ∑ i, forwardCoreOuterWeightM U cap width n i *
        ndRootCoreFilteredKernel (forwardIterateM U cap n).floor
          (ndGeom2ShiftedWideSymmetricShiftRadius (forwardIterateM U cap n).floor) (cap n) k
          (ndRootCoreWordFilter (forwardIterateM U cap n).floor
            (width (forwardIterateM U cap n).floor))
          (ndSyracuseUnitReferenceDensity k)
          (-((((forwardIterateM U cap n).state.root i : ℕ)) :
            ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon (forwardIterateM U cap n).floor
              + k)))) := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  letI := (nextFloorM (forwardIterateM U cap n) (cap n)).state.labelFintype
  letI := (forwardIterateM U cap (n + 1)).state.labelFintype
  set f : (nextFloorM (forwardIterateM U cap n) (cap n)).state.Label → ℝ := fun z =>
    ucWeightM (forwardCoreOuterWeightM U cap width n) z *
      ndRootCoreWordFilter (forwardIterateM U cap n).floor
        (width (forwardIterateM U cap n).floor) (ucWordM z) *
      ndSyracuseUnitReferenceDensity k (-(((ucSourceM z : ℕ)) : ZMod (3 ^ k))) with hf
  have hs : forwardCoreMassM U cap width (n + 1) k (fun _ => 1) =
      ∑ z : (nextFloorM (forwardIterateM U cap n) (cap n)).state.Label, f z := by
    rw [forwardCoreMassM_eq_outerWeight_sum]
    refine Fintype.sum_equiv (forwardLastIncidenceEquivM U cap n) _ _ ?_
    intro z
    have hiff := forwardCoreM_iff_last_parent_and_strip U cap width n z
    have hW := forwardLastIncidenceM_weight_eq U cap n z
    have hS := forwardLastIncidenceM_source_eq U cap n z
    set e := forwardLastIncidenceEquivM U cap n z with he
    by_cases hP : forwardCoreM U cap width n (ucLabelM e)
    · by_cases hB : (forwardIterateM U cap n).floor ≤
          (ucWordM e).length + width (forwardIterateM U cap n).floor ∧
          (ucWordM e).length ≤
            (forwardIterateM U cap n).floor + width (forwardIterateM U cap n).floor
      · have hfil : ndRootCoreWordFilter (forwardIterateM U cap n).floor
            (width (forwardIterateM U cap n).floor) (ucWordM e) = 1 := by
          unfold ndRootCoreWordFilter
          rw [if_pos ⟨by omega, by omega⟩]
        rw [forwardCoreOuterWeightM_eq_ite, if_pos (hiff.mpr ⟨hP, hB⟩), ← hW, ← hS]
        simp only [hf, forwardCoreOuterWeightM_eq_ite, ucWeightM, forwardLastParentM,
          if_pos hP, hfil]
        ring
      · have hfil : ndRootCoreWordFilter (forwardIterateM U cap n).floor
            (width (forwardIterateM U cap n).floor) (ucWordM e) = 0 := by
          unfold ndRootCoreWordFilter
          rw [if_neg]
          intro hc
          exact hB ⟨by omega, by omega⟩
        rw [forwardCoreOuterWeightM_eq_ite, if_neg (fun hc => hB (hiff.mp hc).2)]
        simp only [hf, ucWeightM, hfil]
        ring
    · rw [forwardCoreOuterWeightM_eq_ite, if_neg (fun hc => hP (hiff.mp hc).1)]
      simp only [hf, forwardCoreOuterWeightM_eq_ite, ucWeightM, forwardLastParentM, if_neg hP]
      ring
  have hkey := sum_unitIncidenceM_mark_eq_filteredKernel
    (Labels := (Finset.univ : Finset (forwardIterateM U cap n).state.Label))
    (root := (forwardIterateM U cap n).state.root)
    (b := (forwardIterateM U cap n).floor)
    (a := ndGeom2ShiftedWideSymmetricShiftRadius (forwardIterateM U cap n).floor) (K := cap n)
    (forwardCoreOuterWeightM U cap width n) k
    (forwardIterateM U cap n).state.root_odd
    (by have h := (forwardIterateM U cap n).floor_twoHundred; omega)
    (fun i => (Nat.pow_le_pow_right (by norm_num)
      ((forwardIterateM U cap n).floor_le_base i)).trans
      ((forwardIterateM U cap n).state.rootLower i))
    hk
    (ndRootCoreWordFilter (forwardIterateM U cap n).floor
      (width (forwardIterateM U cap n).floor))
    (ndSyracuseUnitReferenceDensity k)
    (unitReferenceDensity_natCast_eq_zero_of_not_unit hk)
  rw [hs]
  change (∑ z : (nextFloorM (forwardIterateM U cap n) (cap n)).state.Label, f z) = _ at hkey
  rw [hkey]
  change (∑ i : {i : (forwardIterateM U cap n).state.Label //
    i ∈ (Finset.univ : Finset (forwardIterateM U cap n).state.Label)}, _) = _
  exact (Finset.sum_subtype Finset.univ (fun _ => Iff.rfl) (fun i =>
    forwardCoreOuterWeightM U cap width n i *
      ndRootCoreFilteredKernel (forwardIterateM U cap n).floor
        (ndGeom2ShiftedWideSymmetricShiftRadius (forwardIterateM U cap n).floor) (cap n) k
        (ndRootCoreWordFilter (forwardIterateM U cap n).floor
          (width (forwardIterateM U cap n).floor))
        (ndSyracuseUnitReferenceDensity k)
        (-((((forwardIterateM U cap n).state.root i : ℕ)) :
          ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon (forwardIterateM U cap n).floor
            + k)))))).symm

/-- Pairing the histogram against the coarse reference mark, at the negated residue. -/
theorem forwardCoreHistogramM_referenceMark_pairing
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ)
    (n k q : ℕ) (hkq : k ≤ q) :
    (∑ y, forwardCoreHistogramM U cap width n q y *
        ndSyracuseUnitReferenceDensity k (Tao.taoZModThreeProjection hkq (-y))) =
      forwardCoreMassM U cap width n k (fun _ => 1) := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  rw [forwardCoreHistogramM_pairing U cap width n q
    (fun y => ndSyracuseUnitReferenceDensity k (Tao.taoZModThreeProjection hkq (-y))),
    forwardCoreMassM_eq_outerWeight_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  rw [map_neg, Tao.taoZModThreeProjection_natCast]

/-- **The increment is a single histogram pairing.**  This is what the variation argument
integrates. -/
theorem forwardCoreMassM_increment_eq_histogram
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ)
    (n k ell : ℕ) (hk : 1 ≤ k)
    (hell : ell ≤ ndGeom2ShiftedWideSymmetricHorizon (forwardIterateM U cap n).floor + k) :
    forwardCoreMassM U cap width (n + 1) k (fun _ => 1) -
        forwardCoreMassM U cap width n ell (fun _ => 1) =
      ∑ y, forwardCoreHistogramM U cap width n
          (ndGeom2ShiftedWideSymmetricHorizon (forwardIterateM U cap n).floor + k) y *
        (ndRootCoreFilteredKernel (forwardIterateM U cap n).floor
            (ndGeom2ShiftedWideSymmetricShiftRadius (forwardIterateM U cap n).floor) (cap n) k
            (ndRootCoreWordFilter (forwardIterateM U cap n).floor
              (width (forwardIterateM U cap n).floor))
            (ndSyracuseUnitReferenceDensity k) (-y) -
          ndSyracuseUnitReferenceDensity ell (Tao.taoZModThreeProjection hell (-y))) := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,
    forwardCoreHistogramM_referenceMark_pairing U cap width n ell _ hell,
    forwardCoreMassM_succ_eq_kernel U cap width n k hk,
    forwardCoreHistogramM_pairing U cap width n _
      (fun y => ndRootCoreFilteredKernel (forwardIterateM U cap n).floor
        (ndGeom2ShiftedWideSymmetricShiftRadius (forwardIterateM U cap n).floor) (cap n) k
        (ndRootCoreWordFilter (forwardIterateM U cap n).floor
          (width (forwardIterateM U cap n).floor))
        (ndSyracuseUnitReferenceDensity k) (-y))]

end

end ThreeXMinusOne
