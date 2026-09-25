import ThreeXMinusOne.SourceTariff
import ThreeXMinusOne.IterateState
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideUniformFloorGeometricIntervalStoppingGeometry

/-!
# The `3x−1` window: a generation whose intervals all straddle `X`

`Geom2ShiftedWideSymmetricRootSideGeometricSynchronizedIntervals`, mirrored.

This is the second of the two things `Assembly.count_ge_of_incidence_family` still wants (the
first is the mass, Layer 30).  It produces a generation `n` at which *every* label's physical
interval contains a prescribed `X` — so the sources of that generation all land in one window.

The `+1` file mentions the map zero times, but it is stated over `U.iterate` and `U.next`, so it
is not reusable as it stands: the minus construction is a different inhabitant of the same
wrapper.  What *is* reusable, verbatim, is the arithmetic core
`ndGeom2ShiftedWideSymmetric_geometricIntervalMin_lt_intervalMax_of_shellUpper`, which is stated
over bare naturals `{b K M N}`.  So this file is the generational scaffolding around a shared
arithmetic centre.

**Where the factor two goes.**  `SourceTariff` gives `2 ^ (K + 2)` where `+1` has `2 ^ (K + 1)`.
The arithmetic core takes its upper bound in the form `2 ^ (K + 1)`, so the minus side spends
the extra factor by shifting the cap slot: it is applied at `K + 1`, which costs one more unit
of budget, `e + K + 1 ≤ floor / 200` rather than `e + K ≤ floor / 200`.  The span budget
accordingly grows by `4` per generation instead of `3`, and the generation threshold reads
`e + L + 4` rather than `e + L + 3`.  Nothing else moves.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

/-- All roots of a state lie within a factor `2 ^ e` of each other. -/
def rootSpanM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (e : ℕ) : Prop :=
  ∀ i j : U.state.Label, U.state.root i ≤ 2 ^ e * U.state.root j

private theorem nextFloorM_root_lower (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) :
    ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
  (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans (U.state.rootLower i)

private theorem nextFloorM_source_upper
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (K : ℕ)
    (z : (nextFloorM U K).state.Label) :
    3 ^ U.floor * (nextFloorM U K).state.root z ≤
      2 ^ (K + 2) * 4 ^ U.floor * U.state.root (ucLabelM z) :=
  threePow_mul_ucSourceM_le_twoPow_capTwo_mul_fourPow_mul_parent
    U.state.root_odd (by have h := U.floor_twoHundred; omega) (nextFloorM_root_lower U) z

private theorem nextFloorM_source_lower
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (K : ℕ)
    (z : (nextFloorM U K).state.Label) :
    4 ^ U.floor * U.state.root (ucLabelM z) ≤
      4 * 3 ^ U.floor * (nextFloorM U K).state.root z :=
  fourPow_mul_parent_le_four_mul_threePow_mul_ucSourceM
    U.state.root_odd (by have h := U.floor_twoHundred; omega) (nextFloorM_root_lower U) z

/-- **The span grows by `cap + 4` per generation** (`+1` has `cap + 3`). -/
theorem nextFloorM_rootSpan (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    {e : ℕ} (he : rootSpanM U e) (K : ℕ) : rootSpanM (nextFloorM U K) (e + K + 4) := by
  intro z z'
  have h := calc
    3 ^ U.floor * (nextFloorM U K).state.root z ≤
        2 ^ (K + 2) * 4 ^ U.floor * U.state.root (ucLabelM z) :=
      nextFloorM_source_upper U K z
    _ ≤ 2 ^ (K + 2) * 4 ^ U.floor * (2 ^ e * U.state.root (ucLabelM z')) :=
      Nat.mul_le_mul_left _ (he _ _)
    _ = 2 ^ (K + 2 + e) * (4 ^ U.floor * U.state.root (ucLabelM z')) := by
      rw [pow_add]; ring
    _ ≤ 2 ^ (K + 2 + e) * (4 * 3 ^ U.floor * (nextFloorM U K).state.root z') :=
      Nat.mul_le_mul_left _ (nextFloorM_source_lower U K z')
    _ = 3 ^ U.floor * (2 ^ (e + K + 4) * (nextFloorM U K).state.root z') := by
      have hexp : e + K + 4 = (K + 2 + e) + 2 := by omega
      rw [hexp, pow_add]
      ring
  exact Nat.le_of_mul_le_mul_left h (by positivity)

/-- The accumulated span budget. -/
def rootSpanBudgetM (e : ℕ) (cap : ℕ → ℕ) (n : ℕ) : ℕ :=
  e + ∑ j ∈ Finset.range n, (cap j + 4)

theorem iterateM_rootSpan (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    {e : ℕ} (he : rootSpanM U e) (cap : ℕ → ℕ) (n : ℕ) :
    rootSpanM (iterateM U cap n) (rootSpanBudgetM e cap n) := by
  induction n with
  | zero => simpa [iterateM, rootSpanBudgetM] using he
  | succ n ih =>
      simpa [iterateM, rootSpanBudgetM, Finset.sum_range_succ, Nat.add_assoc]
        using nextFloorM_rootSpan (iterateM U cap n) ih (cap n)

theorem rootSpanBudgetM_le_quadratic (e L : ℕ) (cap : ℕ → ℕ) (hc : ∀ n, cap n ≤ L * (n + 1))
    (n : ℕ) : rootSpanBudgetM e cap n ≤ (e + L + 4) * (n + 1) ^ 2 := by
  induction n with
  | zero => simp [rootSpanBudgetM]; omega
  | succ n ih =>
      have hc' := hc n
      have hn : 0 ≤ n := Nat.zero_le n
      simp only [rootSpanBudgetM, Finset.sum_range_succ] at ih ⊢
      nlinarith

/-- One generation multiplies the floor by at least `201/200`. -/
theorem iterateM_twoHundredOne_mul_floor_le_twoHundred_mul_next
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ) :
    201 * (iterateM U cap n).floor ≤ 200 * (iterateM U cap (n + 1)).floor := by
  have h := (iterateM U cap n).floor_twoHundred
  change 201 * (iterateM U cap n).floor ≤
    200 * ((iterateM U cap n).floor + (iterateM U cap n).floor / 100)
  omega

private theorem cubic_growth_stepM (n : ℕ) : 200 * (n + 1001) ^ 3 ≤ 201 * (n + 1000) ^ 3 := by
  nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]

theorem iterateM_floor_cubic_lower (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    U.floor * (n + 1000) ^ 3 ≤ 1000000000 * (iterateM U cap n).floor := by
  induction n with
  | zero => simp [iterateM]; omega
  | succ n ih =>
      have hg := iterateM_twoHundredOne_mul_floor_le_twoHundred_mul_next U cap n
      have hc := Nat.mul_le_mul_left U.floor (cubic_growth_stepM n)
      have hi := Nat.mul_le_mul_left 201 ih
      have ht := Nat.mul_le_mul_left 1000000000 hg
      nlinarith

/-- The budget stays inside `floor / 200`, with one unit of slack for the wider minus tariff. -/
theorem rootSpanBudgetM_add_cap_le_floor_div_twoHundred
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (e L : ℕ) (cap : ℕ → ℕ)
    (hc : ∀ n, cap n ≤ L * (n + 1)) (n : ℕ) (hn : 1000000000 * (e + L + 4) ≤ n) :
    rootSpanBudgetM e cap n + cap n + 1 ≤ (iterateM U cap n).floor / 200 := by
  have hbudget : rootSpanBudgetM e cap n + cap n + 1 ≤ (e + L + 4) * (n + 1000) ^ 2 := by
    have h := rootSpanBudgetM_le_quadratic e L cap hc (n + 1)
    have hmono : (n + 1 + 1) ^ 2 ≤ (n + 1000) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h' := h.trans (Nat.mul_le_mul_left (e + L + 4) hmono)
    simp only [rootSpanBudgetM, Finset.sum_range_succ] at h' ⊢
    omega
  have hb := U.floor_twoHundred
  have hg := iterateM_floor_cubic_lower U cap n
  have hl : 200 * (n + 1000) ^ 3 ≤ 1000000000 * (iterateM U cap n).floor :=
    (Nat.mul_le_mul_right ((n + 1000) ^ 3) hb).trans hg
  have ht : 1000000000 * (e + L + 4) ≤ n + 1000 := by omega
  have hp := Nat.mul_le_mul_right (200 * (n + 1000) ^ 2) ht
  have hscale : 1000000000 * (200 * ((e + L + 4) * (n + 1000) ^ 2)) ≤
      200 * (n + 1000) ^ 3 := by
    calc 1000000000 * (200 * ((e + L + 4) * (n + 1000) ^ 2))
        = (1000000000 * (e + L + 4)) * (200 * (n + 1000) ^ 2) := by ring
      _ ≤ (n + 1000) * (200 * (n + 1000) ^ 2) := hp
      _ = 200 * (n + 1000) ^ 3 := by ring
  have hsmall : 200 * ((e + L + 4) * (n + 1000) ^ 2) ≤ (iterateM U cap n).floor :=
    Nat.le_of_mul_le_mul_left (hscale.trans hl) (by norm_num)
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 200)).2 (by
    simpa [Nat.mul_comm] using (Nat.mul_le_mul_left 200 hbudget).trans hsmall)

/-- **Every child interval starts below every parent interval's top.** -/
theorem nextFloorM_intervalMin_lt_every_parentIntervalMax
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) {e K : ℕ} (he : rootSpanM U e)
    (hb : 600 ≤ U.floor) (hbudget : e + K + 1 ≤ U.floor / 200)
    (z : (nextFloorM U K).state.Label) (i : U.state.Label) :
    ndGeom2ShiftedWideSymmetricPhysicalIntervalMin
        (nextFloorM U K).floor ((nextFloorM U K).state.root z) <
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMax U.floor (U.state.root i) := by
  have hu := nextFloorM_source_upper U K z
  have hs := he (ucLabelM z) i
  have hsource : 3 ^ U.floor * (nextFloorM U K).state.root z ≤
      2 ^ ((e + K + 1) + 1) * 4 ^ U.floor * U.state.root i := by
    calc 3 ^ U.floor * (nextFloorM U K).state.root z
        ≤ 2 ^ (K + 2) * 4 ^ U.floor * (2 ^ e * U.state.root i) :=
          hu.trans (Nat.mul_le_mul_left _ hs)
      _ = 2 ^ ((e + K + 1) + 1) * 4 ^ U.floor * U.state.root i := by
          rw [show e + K + 1 + 1 = K + 2 + e by omega, pow_add]
          ring
  exact ndGeom2ShiftedWideSymmetric_geometricIntervalMin_lt_intervalMax_of_shellUpper
    hb hbudget (Odd.pos (U.state.root_odd i)) hsource

theorem floor_add_two_mul_le_iterateM_floor
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ) :
    U.floor + 2 * n ≤ (iterateM U cap n).floor := by
  induction n with
  | zero => simp [iterateM]
  | succ n ih =>
      have h := (iterateM U cap n).floor_twoHundred
      have : (iterateM U cap (n + 1)).floor =
        (iterateM U cap n).floor + (iterateM U cap n).floor / 100 := rfl
      omega

theorem iterateM_eventual_all_parent_overlap
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) {e L : ℕ} (he : rootSpanM U e)
    (cap : ℕ → ℕ) (hc : ∀ n, cap n ≤ L * (n + 1))
    (n : ℕ) (hn : 1000000000 * (e + L + 4) ≤ n)
    (z : (iterateM U cap (n + 1)).state.Label) (i : (iterateM U cap n).state.Label) :
    ndGeom2ShiftedWideSymmetricPhysicalIntervalMin
        (iterateM U cap (n + 1)).floor ((iterateM U cap (n + 1)).state.root z) <
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
        (iterateM U cap n).floor ((iterateM U cap n).state.root i) := by
  have hf := floor_add_two_mul_le_iterateM_floor U cap n
  have hb := U.floor_twoHundred
  exact nextFloorM_intervalMin_lt_every_parentIntervalMax (iterateM U cap n)
    (iterateM_rootSpan U he cap n) (by omega)
    (rootSpanBudgetM_add_cap_le_floor_div_twoHundred U e L cap hc n hn) z i

private theorem exists_generationM_all_intervalMax_ge
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (N : ℕ) (X : ℝ) :
    ∃ t, ∀ i : (iterateM U cap (N + t)).state.Label,
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
        (iterateM U cap (N + t)).floor ((iterateM U cap (N + t)).state.root i) := by
  obtain ⟨t, ht⟩ := exists_nat_gt X
  refine ⟨t, fun i => ?_⟩
  have hf : t ≤ (iterateM U cap (N + t)).floor := by
    have h := floor_add_two_mul_le_iterateM_floor U cap (N + t)
    have hb := U.floor_twoHundred
    omega
  have hr : 16 ^ (iterateM U cap (N + t)).floor ≤ (iterateM U cap (N + t)).state.root i :=
    (Nat.pow_le_pow_right (by norm_num)
      ((iterateM U cap (N + t)).floor_le_base i)).trans
      ((iterateM U cap (N + t)).state.rootLower i)
  have hp : t ≤ 2 ^ (iterateM U cap (N + t)).floor :=
    hf.trans (show (iterateM U cap (N + t)).floor < 2 ^ (iterateM U cap (N + t)).floor from
      Nat.lt_two_pow_self).le
  have hpReal : (t : ℝ) ≤ ((2 ^ (iterateM U cap (N + t)).floor : ℕ) : ℝ) := by exact_mod_cast hp
  exact ht.le.trans (hpReal.trans
    (twoPow_base_le_ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
      (by have h := (iterateM U cap (N + t)).floor_twoHundred; omega) hr))

/-- **The window.**  Some generation past `N` has every physical interval straddling `X`. -/
theorem exists_unstopped_generationM_all_intervals_contain
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) {e L : ℕ} (he : rootSpanM U e)
    (cap : ℕ → ℕ) (hc : ∀ n, cap n ≤ L * (n + 1))
    (N : ℕ) (hN : 1000000000 * (e + L + 4) ≤ N) (X : ℝ)
    (hstart : ∀ i : (iterateM U cap N).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
        (iterateM U cap N).floor ((iterateM U cap N).state.root i) < X) :
    ∃ n, N ≤ n ∧ ∀ i : (iterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin
          (iterateM U cap n).floor ((iterateM U cap n).state.root i) < X ∧
        X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
          (iterateM U cap n).floor ((iterateM U cap n).state.root i) := by
  classical
  let P := fun t => ∀ i : (iterateM U cap (N + t)).state.Label,
    X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
      (iterateM U cap (N + t)).floor ((iterateM U cap (N + t)).state.root i)
  have hex : ∃ t, P t := exists_generationM_all_intervalMax_ge U cap N X
  generalize htdef : Nat.find hex = t
  have ht : P t := htdef ▸ Nat.find_spec hex
  cases t with
  | zero =>
      refine ⟨N, le_rfl, fun i => ?_⟩
      have ht' : ∀ i : (iterateM U cap N).state.Label,
          X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
            (iterateM U cap N).floor ((iterateM U cap N).state.root i) := by
        simpa only [P, Nat.add_zero] using ht
      exact False.elim (not_lt_of_ge (ht' i) (hstart i))
  | succ m =>
      have hnot : ¬ P m := Nat.find_min hex (by omega)
      dsimp only [P] at hnot
      push Not at hnot
      obtain ⟨j, hj⟩ := hnot
      refine ⟨N + m + 1, by omega, fun i => ?_⟩
      have ht' : ∀ i : (iterateM U cap (N + m + 1)).state.Label,
          X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
            (iterateM U cap (N + m + 1)).floor
            ((iterateM U cap (N + m + 1)).state.root i) := by
        simpa only [P, Nat.succ_eq_add_one, Nat.add_assoc] using ht
      exact ⟨(iterateM_eventual_all_parent_overlap U he cap hc
        (N + m) (by omega) i j).trans hj, ht' i⟩

end

end ThreeXMinusOne
