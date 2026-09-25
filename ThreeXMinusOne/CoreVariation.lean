import ThreeXMinusOne.CoreIncrement
import ThreeXMinusOne.AdaptivePairing
import Erdos1135.ND.PositiveDensity.ExplicitCoreVariation

/-!
# The core mass varies slowly

`explicit_coreMarkedMass_increment_rate`, `explicit_core_increment_le_majorant` and
`explicit_core_marked_difference`, mirrored.

Layer 65 made the increment a single histogram pairing; Layer 55 bounds such a pairing by the
capacity budget times the mean of what it is paired against; and the mean in question is bounded
by the artifact's own `explicitCoreFilteredKernel_rate`, which quantifies over bare naturals and
mentions no map at all.  Layer 64 then turns the plus budget's whole geometric chain into the
minus one at the cost of a single factor `E = 1 + 4.6 × 10^(-50)`.

So the minus variation majorant is `E ·` the `+1` majorant, and it is summable for the same
reason.  **The residue flip contributes exactly one step**: the minus increment is paired against
`y ↦ (kernel − reference)(−y)`, and negation preserves the uniform mean, so the artifact's rate
bound applies to it unchanged.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

/-- The core-mass sequence, read at the quarter conductor. -/
def coreMarkedSequenceM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n : ℕ) : ℝ :=
  forwardCoreMassM U cap width n ((forwardIterateM U cap n).floor / 4) (fun _ => 1)

/-- **The increment rate.**  `+1`'s budget replaced by the minus one. -/
theorem explicit_coreMassM_increment_rate {A : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt A C)
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ)
    (n k ell : ℕ)
    (hm : 16 ≤ width (forwardIterateM U cap n).floor)
    (hmw : width (forwardIterateM U cap n).floor ≤
      ndGeom2ShiftedWideSymmetricWidth (forwardIterateM U cap n).floor)
    (hk : 1 ≤ k) (hellpos : 1 ≤ ell)
    (hq : ndGeom2ShiftedWideSymmetricHorizon (forwardIterateM U cap n).floor + k ≤
      2 * (forwardIterateM U cap n).floor)
    (hell : ell ≤ ndGeom2ShiftedWideSymmetricHorizon (forwardIterateM U cap n).floor + k) :
    |forwardCoreMassM U cap width (n + 1) k (fun _ => 1) -
        forwardCoreMassM U cap width n ell (fun _ => 1)| ≤
      coreCapacityBudgetM U cap width n * ((2 / 3 : ℝ) *
        (C / (k : ℝ) ^ A + C / (ell : ℝ) ^ A +
          (4 * ((forwardIterateM U cap n).floor : ℝ) + 4) *
            Real.exp (-((width (forwardIterateM U cap n).floor : ℝ) ^ 2 /
              (576 * ((forwardIterateM U cap n).floor : ℝ)))) +
          (1 / 2 : ℝ) ^ (cap n + 1))) := by
  classical
  set b := (forwardIterateM U cap n).floor with hb
  set q := ndGeom2ShiftedWideSymmetricHorizon b + k with hqdef
  set F : ZMod (3 ^ q) → ℝ := fun y =>
    ndRootCoreFilteredKernel b (ndGeom2ShiftedWideSymmetricShiftRadius b) (cap n) k
      (ndRootCoreWordFilter b (width b)) (ndSyracuseUnitReferenceDensity k) y -
      ndSyracuseUnitReferenceDensity ell (Tao.taoZModThreeProjection hell y) with hF
  rw [forwardCoreMassM_increment_eq_histogram U cap width n k ell hk hell]
  refine (abs_coreHistogramM_pairing_le_capacity U cap width n q hq (fun y => F (-y))).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (coreCapacityBudgetM_nonneg U cap width n)
  rw [show (fun y => |F (-y)|) = (fun y => (fun w => |F w|) (-y)) from rfl,
    ndTernaryUniformMean_neg q (fun w => |F w|)]
  exact explicitCoreFilteredKernel_rate hC hmix b (width b) (cap n) k ell
    (forwardIterateM U cap n).floor_twoHundred hm hmw hk hellpos hell

/-- The quarter-conductor form, one generation to the next. -/
theorem explicit_quarter_coreMarkedSequenceM_increment_rate {A : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt A C)
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ) (n : ℕ)
    (hm : 16 ≤ width (forwardIterateM U cap n).floor)
    (hmw : width (forwardIterateM U cap n).floor ≤
      ndGeom2ShiftedWideSymmetricWidth (forwardIterateM U cap n).floor) :
    |coreMarkedSequenceM U cap width (n + 1) - coreMarkedSequenceM U cap width n| ≤
      coreCapacityBudgetM U cap width n * ((2 / 3 : ℝ) *
        (C / ((((forwardIterateM U cap n).floor + (forwardIterateM U cap n).floor / 100) / 4 : ℕ) :
            ℝ) ^ A +
          C / (((forwardIterateM U cap n).floor / 4 : ℕ) : ℝ) ^ A +
          (4 * ((forwardIterateM U cap n).floor : ℝ) + 4) *
            Real.exp (-((width (forwardIterateM U cap n).floor : ℝ) ^ 2 /
              (576 * ((forwardIterateM U cap n).floor : ℝ)))) +
          (1 / 2 : ℝ) ^ (cap n + 1))) := by
  have hb : 200 ≤ (forwardIterateM U cap n).floor :=
    (forwardIterateM U cap n).floor_twoHundred
  have hr := explicit_coreMassM_increment_rate hC hmix U cap width n
    (((forwardIterateM U cap n).floor + (forwardIterateM U cap n).floor / 100) / 4)
    ((forwardIterateM U cap n).floor / 4) hm hmw (by omega) (by omega)
    (by
      have h := shiftedReference_quarter_next_conductor_le_two_mul (forwardIterateM U cap n).floor
      exact h)
    (by omega)
  unfold coreMarkedSequenceM
  rw [forwardIterateM_succ_eq_next U cap n]
  exact hr

/-- **The increment is below `E ·` the `+1` majorant.** -/
theorem explicit_coreM_increment_le_majorant {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt 6 C)
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (hb : 32 ^ 5 ≤ U.floor)
    (cap : ℕ → ℕ) (L K0 : ℕ) (hcap : ∀ n, cap n ≤ L * (n + 1))
    (hcaplo : ∀ n, K0 + n / 100 ≤ cap n) (n : ℕ) :
    |coreMarkedSequenceM U cap ndRootCoreWidth (n + 1) -
        coreMarkedSequenceM U cap ndRootCoreWidth n| ≤
      excessBound * (U.denominator * ndRootCoreVariationMajorant U.floor L K0 C n) := by
  have hfloor := forwardIterateM_floor_eq U cap n
  have hmguard := U.forward_core_width_guard hb cap n
  have hm : 16 ≤ ndRootCoreWidth (forwardIterateM U cap n).floor := by rw [hfloor]; exact hmguard.1
  have hmw : ndRootCoreWidth (forwardIterateM U cap n).floor ≤
      ndGeom2ShiftedWideSymmetricWidth (forwardIterateM U cap n).floor := by
    rw [hfloor]; exact hmguard.2
  have hr := explicit_quarter_coreMarkedSequenceM_increment_rate hC hmix U cap ndRootCoreWidth n
    hm hmw
  rw [hfloor] at hr
  set b := (U.forwardIterate cap n).floor with hbdef
  have hbudget := U.coreCapacityBudget_le_geometric cap L hcap n
  have he := rootCore_quarter_error_le (b := b) (U.forwardIterate cap n).floor_twoHundred hC
  have hi : 1 / (b : ℝ) ^ 6 ≤ (1 / (U.floor : ℝ) ^ 6) * ((200 / 201 : ℝ) ^ 6) ^ n := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / (b : ℝ))
      (U.core_inverse_floor_le_geometric cap n) 6
    simpa only [div_pow, one_pow, mul_pow, ← pow_mul, Nat.mul_comm] using hh
  have hp : 0 ≤ 2 * C * 8 ^ 6 + ndRootCoreStripConstant := by
    unfold ndRootCoreStripConstant; positivity
  have herror := mul_le_mul_of_nonneg_left hi hp
  have hct := rootCore_cap_failure_le_geometric cap K0 hcaplo n
  have hD : 0 ≤ U.denominator := by
    classical
    letI := U.state.labelFintype
    exact Finset.sum_nonneg fun i _ => U.state.weight_nonneg i
  have herr : C / (((b + b / 100) / 4 : ℕ) : ℝ) ^ 6 + C / ((b / 4 : ℕ) : ℝ) ^ 6 +
      (4 * (b : ℝ) + 4) * Real.exp (-((ndRootCoreWidth b : ℝ) ^ 2 / (576 * (b : ℝ)))) +
      (1 / 2 : ℝ) ^ (cap n + 1) ≤
      ((2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (U.floor : ℝ) ^ 6) *
        ((200 / 201 : ℝ) ^ 6) ^ n +
        (1 / 2 : ℝ) ^ K0 * ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n := by
    rw [mul_one_div] at herror
    have hh : (2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (b : ℝ) ^ 6 ≤
        ((2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (U.floor : ℝ) ^ 6) *
          ((200 / 201 : ℝ) ^ 6) ^ n := by
      convert herror using 1; ring
    linarith
  have herrnn : (0 : ℝ) ≤ (2 / 3 : ℝ) *
      (C / (((b + b / 100) / 4 : ℕ) : ℝ) ^ 6 + C / ((b / 4 : ℕ) : ℝ) ^ 6 +
        (4 * (b : ℝ) + 4) * Real.exp (-((ndRootCoreWidth b : ℝ) ^ 2 / (576 * (b : ℝ)))) +
        (1 / 2 : ℝ) ^ (cap n + 1)) := by positivity
  calc |coreMarkedSequenceM U cap ndRootCoreWidth (n + 1) -
          coreMarkedSequenceM U cap ndRootCoreWidth n|
      ≤ coreCapacityBudgetM U cap ndRootCoreWidth n * ((2 / 3 : ℝ) *
          (C / (((b + b / 100) / 4 : ℕ) : ℝ) ^ 6 + C / ((b / 4 : ℕ) : ℝ) ^ 6 +
            (4 * (b : ℝ) + 4) * Real.exp (-((ndRootCoreWidth b : ℝ) ^ 2 / (576 * (b : ℝ)))) +
            (1 / 2 : ℝ) ^ (cap n + 1))) := hr
    _ ≤ (excessBound * U.coreCapacityBudget cap ndRootCoreWidth n) * ((2 / 3 : ℝ) *
          (C / (((b + b / 100) / 4 : ℕ) : ℝ) ^ 6 + C / ((b / 4 : ℕ) : ℝ) ^ 6 +
            (4 * (b : ℝ) + 4) * Real.exp (-((ndRootCoreWidth b : ℝ) ^ 2 / (576 * (b : ℝ)))) +
            (1 / 2 : ℝ) ^ (cap n + 1))) :=
        mul_le_mul_of_nonneg_right (coreCapacityBudgetM_le U cap ndRootCoreWidth n) herrnn
    _ = excessBound * (U.coreCapacityBudget cap ndRootCoreWidth n * ((2 / 3 : ℝ) *
          (C / (((b + b / 100) / 4 : ℕ) : ℝ) ^ 6 + C / ((b / 4 : ℕ) : ℝ) ^ 6 +
            (4 * (b : ℝ) + 4) * Real.exp (-((ndRootCoreWidth b : ℝ) ^ 2 / (576 * (b : ℝ)))) +
            (1 / 2 : ℝ) ^ (cap n + 1)))) := by ring
    _ ≤ excessBound * (U.coreCapacityBudget cap ndRootCoreWidth n * ((2 / 3 : ℝ) *
          (((2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (U.floor : ℝ) ^ 6) *
            ((200 / 201 : ℝ) ^ 6) ^ n +
            (1 / 2 : ℝ) ^ K0 * ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n))) := by
        refine mul_le_mul_of_nonneg_left ?_ excessBound_pos.le
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left herr (by norm_num))
          (U.coreCapacityBudget_nonneg cap ndRootCoreWidth n)
    _ ≤ excessBound * ((U.denominator * ((4 * (U.floor : ℝ) ^ (3 / 5 : ℝ) + 1) * (L + 5) *
          ((2 : ℝ) ^ (U.floor + 1) + (16 : ℝ) ^ U.floor)) *
          ((n + 1 : ℕ) : ℝ) ^ 3 * ndRootCoreGrowth ^ n) * ((2 / 3 : ℝ) *
          (((2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (U.floor : ℝ) ^ 6) *
            ((200 / 201 : ℝ) ^ 6) ^ n +
            (1 / 2 : ℝ) ^ K0 * ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n))) := by
        refine mul_le_mul_of_nonneg_left ?_ excessBound_pos.le
        exact mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = _ := by unfold ndRootCoreVariationMajorant; rw [mul_pow, mul_pow]; ring

/-- **The core mass is Cauchy, with an explicit tail.** -/
theorem explicit_coreM_marked_difference {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt 6 C)
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (hb : 32 ^ 5 ≤ U.floor)
    (cap : ℕ → ℕ) (L K0 : ℕ) (hcap : ∀ n, cap n ≤ L * (n + 1))
    (hcaplo : ∀ n, K0 + n / 100 ≤ cap n) {N n : ℕ} (hNn : N ≤ n) :
    |coreMarkedSequenceM U cap ndRootCoreWidth n -
        coreMarkedSequenceM U cap ndRootCoreWidth N| ≤
      excessBound * (U.denominator * ndRootCoreVariationTail U.floor L K0 C N) := by
  set f := coreMarkedSequenceM U cap ndRootCoreWidth with hf
  set B := ndRootCoreVariationMajorant U.floor L K0 C with hB
  have hD : 0 ≤ U.denominator := by
    classical
    letI := U.state.labelFintype
    exact Finset.sum_nonneg fun i _ => U.state.weight_nonneg i
  have hinc := explicit_coreM_increment_le_majorant hC hmix U hb cap L K0 hcap hcaplo
  have hpartial : ∀ J : ℕ, |f (N + J) - f N| ≤
      excessBound * (U.denominator * ∑ j ∈ Finset.range J, B (N + j)) := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
        rw [Finset.sum_range_succ]
        calc |f (N + (J + 1)) - f N|
            ≤ |f (N + (J + 1)) - f (N + J)| + |f (N + J) - f N| := abs_sub_le _ _ _
          _ ≤ excessBound * (U.denominator * B (N + J)) +
              excessBound * (U.denominator * ∑ j ∈ Finset.range J, B (N + j)) :=
              add_le_add (by simpa only [Nat.add_assoc] using hinc (N + J)) ih
          _ = _ := by ring
  have hs : Summable (fun j => B (N + j)) := by
    simpa only [Nat.add_comm N] using
      (summable_nat_add_iff N).mpr (summable_rootCoreVariationMajorant U.floor L K0 C)
  have hsum : (∑ j ∈ Finset.range (n - N), B (N + j)) ≤ ∑' j, B (N + j) :=
    hs.sum_le_tsum _ (fun j _ => rootCoreVariationMajorant_nonneg _ _ _ _ hC)
  have h := (hpartial (n - N)).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hD) excessBound_pos.le)
  simpa only [Nat.add_sub_of_le hNn] using h

end

end ThreeXMinusOne
