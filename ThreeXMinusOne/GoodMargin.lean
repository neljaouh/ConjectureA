import ThreeXMinusOne.CoreVariation
import ThreeXMinusOne.TerminalMajorant
import ThreeXMinusOne.LossMajorant
import ThreeXMinusOne.DepthShiftSplit
import Erdos1135.ND.PositiveDensity.ExplicitLogarithmicVariationBudgets

/-!
# The good-mass margin

`explicit_good_marked_margin_logarithmic_full`, mirrored.

A seed whose core mass starts at `255/256` still has a definite fraction of its mass left after
three losses are paid: the core mass drifts (Layer 66, tail `≤ 1/16`), the terminal reading
differs from the core reading (Layer 68, `≤ 1/8`), and the depth-shift band discards some
(Layer 69, `≤ 1/8`).  Each of the three budgets is the artifact's own, map-free, and each of my
three bounds carries Layer 64's factor `E`.

**How much `E` costs.**  `+1` pays `1/16 + 1/8 + 1/8 = 5/16` and keeps `255/256 − 5/16 = 175/256`.
The minus side pays `E · 5/16`.  A crude `E ≤ 2` — proved here from `(9/16)^200 ≤ (9/16)^9 ≤ 1/100`
and `log 2 > 0.693` — already leaves `95/256`, and `1/4` is a convenient round number below it.
The true value of `E` is `1 + 4.6 × 10^(-50)`, so the honest margin is `175/256` to fifty
places; `1/4` is simply what is cheap to certify, and the constant it costs is absorbed
downstream by the choice of conductor.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

/-- A crude but cheap bound: the generation excess is below `2`. -/
theorem excessBound_le_two : excessBound ≤ 2 := by
  unfold excessBound
  have h1 : (9 / 16 : ℝ) ^ 200 ≤ (9 / 16 : ℝ) ^ 9 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
  have h2 : (9 / 16 : ℝ) ^ 9 ≤ 1 / 100 := by norm_num
  have hlog := Real.log_two_gt_d9
  have ht : 3 * (9 / 16 : ℝ) ^ 200 * (256 / 175 : ℝ) ≤ Real.log 2 := by nlinarith [h1, h2]
  calc Real.exp (3 * (9 / 16 : ℝ) ^ 200 * (256 / 175 : ℝ))
      ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr ht
    _ = 2 := Real.exp_log (by norm_num)

/-- **The margin.**  `+1` keeps `175/256`; `1/4` is what a crude `E ≤ 2` certifies. -/
theorem explicit_good_marked_marginM_logarithmic_full
    (C : ℕ) (hmix : Tao.syracFineScaleMixingAt 6 (C : ℝ))
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (hb : 32 ^ 5 ≤ U.floor)
    (cap : ℕ → ℕ) (e : ℕ) (he : rootSpanM U e)
    (hcap : ∀ n, cap n ≤ 17 * (n + 1)) (hcaplo : ∀ n, 16 + n / 100 ≤ cap n)
    {N n : ℕ} (hN : explicitLogarithmicSeedGeneration U.floor C ≤ N) (hNn : N ≤ n)
    (hn : explicitLogarithmicTerminalStart U.floor C (e + 1) ≤ n)
    (hseed : (255 / 256 : ℝ) * U.denominator ≤ coreMarkedSequenceM U cap ndRootCoreWidth N)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i)) :
    (1 / 4 : ℝ) * U.denominator ≤
      forwardCoreTerminalGoodDepthShiftUnitMassM U cap ndRootCoreWidth n (cap n)
        ((forwardIterateM U cap n).floor / 4) X hX hi := by
  have hb1 : 1 ≤ U.floor := by omega
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hD : 0 ≤ U.denominator := by
    classical
    letI := U.state.labelFintype
    exact Finset.sum_nonneg fun i _ => U.state.weight_nonneg i
  have hE2 := excessBound_le_two
  have hEpos := excessBound_pos
  have hED : excessBound * U.denominator ≤ 2 * U.denominator :=
    mul_le_mul_of_nonneg_right hE2 hD
  have hEDnn : 0 ≤ excessBound * U.denominator := mul_nonneg hEpos.le hD
  -- the three budgets
  have hcore := explicit_coreM_marked_difference hC hmix U hb cap 17 16 hcap hcaplo hNn
  have hcoreB := explicitCoreVariationTail_logarithmic_budget hb1 C 16 hC le_rfl hN
  have hterm := explicit_terminalUnitMassM_le_majorant hC hmix U cap e 17 16 he hcap hcaplo n
    X hX hi
  have htermB := explicitTerminalVariation_logarithmic_budget hb1 C (e + 1) 16 hC le_rfl hn
  have hbad := forward_terminalBadDepthShiftUnitMassM_le_summable_majorant U cap e 17 he hcap n
    (cap n) X hX hi
  have hbadB := explicitTerminalVariation_logarithmic_budget hb1 C (e + 1) 0
    (by norm_num : (0 : ℝ) ≤ 0) hC hn
  -- convert each `E · (D · majorant)` into a plain multiple of `D`
  have hcoreD : excessBound * (U.denominator *
      ndRootCoreVariationTail U.floor 17 16 (C : ℝ) N) ≤ U.denominator / 8 := by
    have h1 : excessBound * (U.denominator *
        ndRootCoreVariationTail U.floor 17 16 (C : ℝ) N) ≤
        excessBound * U.denominator * (1 / 16 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hcoreB hEDnn
      calc excessBound * (U.denominator * ndRootCoreVariationTail U.floor 17 16 (C : ℝ) N)
          = excessBound * U.denominator * ndRootCoreVariationTail U.floor 17 16 (C : ℝ) N := by
            ring
        _ ≤ excessBound * U.denominator * (1 / 16 : ℝ) := this
    linarith [h1, hED]
  have htermD : excessBound * (U.denominator *
      ndRootTerminalVariationMajorant U.floor (e + 1) 17 16 (C : ℝ) n) ≤ U.denominator / 4 := by
    have h1 : excessBound * (U.denominator *
        ndRootTerminalVariationMajorant U.floor (e + 1) 17 16 (C : ℝ) n) ≤
        excessBound * U.denominator * (1 / 8 : ℝ) := by
      have := mul_le_mul_of_nonneg_left htermB hEDnn
      calc excessBound * (U.denominator *
            ndRootTerminalVariationMajorant U.floor (e + 1) 17 16 (C : ℝ) n)
          = excessBound * U.denominator *
              ndRootTerminalVariationMajorant U.floor (e + 1) 17 16 (C : ℝ) n := by ring
        _ ≤ excessBound * U.denominator * (1 / 8 : ℝ) := this
    linarith [h1, hED]
  have hbadD : excessBound * (U.denominator *
      ndRootTerminalVariationMajorant U.floor (e + 1) 17 0 0 n) ≤ U.denominator / 4 := by
    have h1 : excessBound * (U.denominator *
        ndRootTerminalVariationMajorant U.floor (e + 1) 17 0 0 n) ≤
        excessBound * U.denominator * (1 / 8 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hbadB hEDnn
      calc excessBound * (U.denominator *
            ndRootTerminalVariationMajorant U.floor (e + 1) 17 0 0 n)
          = excessBound * U.denominator *
              ndRootTerminalVariationMajorant U.floor (e + 1) 17 0 0 n := by ring
        _ ≤ excessBound * U.denominator * (1 / 8 : ℝ) := this
    linarith [h1, hED]
  have hc := (abs_le.mp (hcore.trans hcoreD)).1
  have ht := (abs_le.mp (hterm.trans htermD)).1
  unfold forwardCoreTerminalGoodDepthShiftUnitMassM
  linarith only [hseed, hc, ht, hbad.trans hbadD, hD]

end

end ThreeXMinusOne
