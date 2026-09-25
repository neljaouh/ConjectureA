import ThreeXMinusOne.TerminalVariation
import ThreeXMinusOne.Window

/-!
# The terminal error, against a summable majorant

`explicit_quarter_terminalUnitMass_error` and `explicit_terminalUnitMass_le_majorant`, mirrored.

Layer 67 bounded the terminal-versus-core error by (image size) × (capacity budget) × (rate).
Here each factor is replaced by its explicit geometric majorant, so the error becomes summable
in the generation index.

Two constants shift, both already tracked.  The minus span budget grows by `cap + 4` per
generation where `+1` grows by `cap + 3` (Layer 32), so the image-size factor is `e + L + 5`
rather than `e + L + 4` — which is exactly the artifact's majorant read at `e + 1`.  And the
capacity budget carries Layer 64's factor `E`.  So the minus majorant is
`E · ndRootTerminalVariationMajorant U.floor (e+1) L K0 C`, summable for the artifact's reason.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

private theorem terminal_exp_le_inverse_sixthM {b : ℕ} (hb : 0 < b) :
    4 * Real.exp (-(b : ℝ) / 2560000) ≤ ndRootCoreStripConstant / (b : ℝ) ^ 6 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  set x : ℝ := (b : ℝ) / 2560000 with hx_def
  have hx : 0 < x := by rw [hx_def]; positivity
  have ht := Real.pow_div_factorial_le_exp x hx.le 6
  have hexp : Real.exp (-x) ≤ (Nat.factorial 6 : ℝ) / x ^ 6 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_div_iff₀ (Real.exp_pos _) (pow_pos hx _)).mpr
    rw [one_mul, mul_comm]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < Nat.factorial 6)).mp ht
  have hc : 4 * (Nat.factorial 6 : ℝ) * 2560000 ^ 6 ≤ ndRootCoreStripConstant := by
    norm_num [ndRootCoreStripConstant, Nat.factorial]
  calc 4 * Real.exp (-(b : ℝ) / 2560000)
      ≤ 4 * ((Nat.factorial 6 : ℝ) / x ^ 6) := by
        simpa only [hx_def, neg_div] using mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 4)
    _ = (4 * (Nat.factorial 6 : ℝ) * 2560000 ^ 6) / (b : ℝ) ^ 6 := by rw [hx_def]; field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hc (by positivity)

private theorem terminal_quarter_error_le_inverse_sixthM {b : ℕ} (hb : 200 ≤ b)
    {C : ℝ} (hC : 0 ≤ C) :
    2 * C / ((b / 4 : ℕ) : ℝ) ^ 6 + 4 * Real.exp (-(b : ℝ) / 2560000) ≤
      (2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (b : ℝ) ^ 6 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hk0 : (0 : ℝ) < ((b / 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < b / 4)
  have hb8 : (b : ℝ) ≤ 8 * ((b / 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : b ≤ 8 * (b / 4))
  have hrec : 1 / ((b / 4 : ℕ) : ℝ) ≤ 8 / (b : ℝ) :=
    (div_le_div_iff₀ hk0 hb0).mpr (by simpa only [one_mul] using hb8)
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / ((b / 4 : ℕ) : ℝ)) hrec 6)
    (by positivity : 0 ≤ 2 * C)
  have he := terminal_exp_le_inverse_sixthM (b := b) (by omega)
  calc 2 * C / ((b / 4 : ℕ) : ℝ) ^ 6 + 4 * Real.exp (-(b : ℝ) / 2560000)
      ≤ (2 * C) * (8 / (b : ℝ)) ^ 6 + ndRootCoreStripConstant / (b : ℝ) ^ 6 := by
        simp only [div_pow, one_pow, mul_one_div] at hp ⊢
        linarith
    _ = _ := by rw [div_pow]; ring

/-- The quarter-conductor form. -/
theorem explicit_quarter_terminalUnitMassM_error {A : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt A C)
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ)
    (e : ℕ) (he : rootSpanM U e) (n : ℕ) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) :
    |forwardCoreTerminalUnitMassM U cap width n (cap n)
        ((forwardIterateM U cap n).floor / 4) X hX hi -
        coreMarkedSequenceM U cap width n| ≤
      (rootSpanBudgetM e cap n + 1 : ℝ) * coreCapacityBudgetM U cap width n * ((2 / 3 : ℝ) *
        (2 * C / (((forwardIterateM U cap n).floor / 4 : ℕ) : ℝ) ^ A +
          4 * Real.exp (-((forwardIterateM U cap n).floor : ℝ) / 2560000) +
          (1 / 2 : ℝ) ^ (cap n + 1))) := by
  have hs : rootSpanM (forwardIterateM U cap n) (rootSpanBudgetM e cap n) := by
    simpa only [forwardIterateM_eq_iterateM] using iterateM_rootSpan U he cap n
  have hb := (forwardIterateM U cap n).floor_twoHundred
  have hq : ndGeom2ShiftedWideSymmetricHorizon (forwardIterateM U cap n).floor +
      (forwardIterateM U cap n).floor / 4 ≤ 2 * (forwardIterateM U cap n).floor := by
    unfold ndGeom2ShiftedWideSymmetricHorizon ndGeom2ShiftedWideSymmetricWidth
    omega
  exact explicit_terminalUnitMassM_error hC hmix U cap width n (rootSpanBudgetM e cap n)
    (cap n) ((forwardIterateM U cap n).floor / 4) hs (by omega) hq X hX hi

/-- **The terminal error, below `E ·` the `+1` majorant read at `e + 1`.** -/
theorem explicit_terminalUnitMassM_le_majorant {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt 6 C)
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (e L K0 : ℕ)
    (he : rootSpanM U e) (hcap : ∀ n, cap n ≤ L * (n + 1)) (hcaplo : ∀ n, K0 + n / 100 ≤ cap n)
    (n : ℕ) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) :
    |forwardCoreTerminalUnitMassM U cap ndRootCoreWidth n (cap n)
        ((forwardIterateM U cap n).floor / 4) X hX hi -
        coreMarkedSequenceM U cap ndRootCoreWidth n| ≤
      excessBound * (U.denominator *
        ndRootTerminalVariationMajorant U.floor (e + 1) L K0 C n) := by
  have hfloor := forwardIterateM_floor_eq U cap n
  have hr := explicit_quarter_terminalUnitMassM_error hC hmix U cap ndRootCoreWidth e he n X hX hi
  have hbudget := U.coreCapacityBudget_le_geometric cap L hcap n
  have herr := terminal_quarter_error_le_inverse_sixthM
    (forwardIterateM U cap n).floor_twoHundred hC
  have hi6 : 1 / ((forwardIterateM U cap n).floor : ℝ) ^ 6 ≤
      (1 / (U.floor : ℝ) ^ 6) * ((200 / 201 : ℝ) ^ 6) ^ n := by
    rw [hfloor]
    have hh := pow_le_pow_left₀
      (by positivity : (0 : ℝ) ≤ 1 / ((U.forwardIterate cap n).floor : ℝ))
      (U.core_inverse_floor_le_geometric cap n) 6
    simpa only [div_pow, one_pow, mul_pow, ← pow_mul, Nat.mul_comm] using hh
  have hh := mul_le_mul_of_nonneg_left hi6
    (by unfold ndRootCoreStripConstant; positivity : 0 ≤ 2 * C * 8 ^ 6 + ndRootCoreStripConstant)
  simp only [← mul_assoc, mul_one_div] at hh
  have hct := rootCore_cap_failure_le_geometric cap K0 hcaplo n
  have her : 2 * C / (((forwardIterateM U cap n).floor / 4 : ℕ) : ℝ) ^ 6 +
      4 * Real.exp (-((forwardIterateM U cap n).floor : ℝ) / 2560000) +
      (1 / 2 : ℝ) ^ (cap n + 1) ≤
      ((2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (U.floor : ℝ) ^ 6) *
        ((200 / 201 : ℝ) ^ 6) ^ n +
        (1 / 2 : ℝ) ^ K0 * ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n := by linarith
  have hspan : (rootSpanBudgetM e cap n + 1 : ℝ) ≤
      ((e + L + 5 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have hs := rootSpanBudgetM_le_quadratic e L cap hcap n
    have hn : rootSpanBudgetM e cap n + 1 ≤ (e + L + 5) * (n + 1) ^ 2 := by
      calc rootSpanBudgetM e cap n + 1 ≤ (e + L + 4) * (n + 1) ^ 2 + 1 :=
            Nat.add_le_add_right hs 1
        _ ≤ (e + L + 4) * (n + 1) ^ 2 + (n + 1) ^ 2 :=
            Nat.add_le_add_left (by simpa using Nat.pow_le_pow_left (show 1 ≤ n + 1 by omega) 2) _
        _ = _ := by ring
    exact_mod_cast hn
  have hD : 0 ≤ U.denominator := by
    classical
    letI := U.state.labelFintype
    exact Finset.sum_nonneg fun i _ => U.state.weight_nonneg i
  have hGeo : 0 ≤ (4 * (U.floor : ℝ) ^ (3 / 5 : ℝ) + 1) * (L + 5) *
      ((2 : ℝ) ^ (U.floor + 1) + (16 : ℝ) ^ U.floor) := by positivity
  have hbM := (coreCapacityBudgetM_le U cap ndRootCoreWidth n).trans
    (mul_le_mul_of_nonneg_left hbudget excessBound_pos.le)
  have hrnn : (0 : ℝ) ≤ (2 / 3 : ℝ) *
      (2 * C / (((forwardIterateM U cap n).floor / 4 : ℕ) : ℝ) ^ 6 +
        4 * Real.exp (-((forwardIterateM U cap n).floor : ℝ) / 2560000) +
        (1 / 2 : ℝ) ^ (cap n + 1)) := by positivity
  have hRnn : (0 : ℝ) ≤ (2 / 3 : ℝ) *
      (((2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (U.floor : ℝ) ^ 6) *
        ((200 / 201 : ℝ) ^ 6) ^ n +
        (1 / 2 : ℝ) ^ K0 * ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n) := by
    have : (0 : ℝ) ≤ 2 * C * 8 ^ 6 + ndRootCoreStripConstant := by
      unfold ndRootCoreStripConstant; positivity
    positivity
  have hBnn : (0 : ℝ) ≤ excessBound * (U.denominator *
      ((4 * (U.floor : ℝ) ^ (3 / 5 : ℝ) + 1) * (L + 5) *
        ((2 : ℝ) ^ (U.floor + 1) + (16 : ℝ) ^ U.floor)) *
      ((n + 1 : ℕ) : ℝ) ^ 3 * ndRootCoreGrowth ^ n) := by
    have hg : (0 : ℝ) ≤ ndRootCoreGrowth := by norm_num [ndRootCoreGrowth]
    have := excessBound_pos.le
    positivity
  refine hr.trans ?_
  refine le_trans (mul_le_mul (mul_le_mul hspan hbM
      (coreCapacityBudgetM_nonneg U cap ndRootCoreWidth n) (by positivity))
      (mul_le_mul_of_nonneg_left her (by norm_num)) hrnn
      (mul_nonneg (by positivity) hBnn)) (le_of_eq ?_)
  set E := excessBound with hE
  clear_value E
  simp only [ndRootTerminalVariationMajorant, ndRootCoreVariationMajorant,
    show e + 1 + L + 4 = e + L + 5 from by omega]
  ring

end

end ThreeXMinusOne
