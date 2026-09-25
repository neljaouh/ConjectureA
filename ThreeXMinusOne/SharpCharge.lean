import ThreeXMinusOne.IncidenceCharge
import ThreeXMinusOne.Generations

/-!
# The sharp `3x−1` charge bound

A correction to Layer 8, forced by reading the census.

Layer 8 proves `source · atom ≤ (3/2) · root`, unconditional and with an absolute constant.
That is the right statement for `Assembly`, which applies it *once*.  It is the wrong statement
for the census, which applies it *once per generation*: the plus side's corresponding step has
constant `1`, so its terminal charge telescopes for free, while `(3/2)` compounds to `(3/2) ^ n`
and the density would decay geometrically in the number of generations.

The `3/2` is not sharp.  Both `+1` and `−1` clear to
`3 ^ d · source = 2 ^ W · root ± offset`; for `+1` the offset is subtracted, so the bound is
immediate with constant `1`, and for `−1` it is added, so the constant is `1 + offset/(2^W·root)`.
Layer 8 bounds that excess by `1/2` using only `2 · 3 ^ d < root`.  But the depth of a selected
crossing satisfies `d ≤ 2b + 1`, and a root satisfies `16 ^ b ≤ root`, so

    offset/(2 ^ W · root) ≤ 3 ^ d / root ≤ 3 · 9 ^ b / 16 ^ b = 3 · (9/16) ^ b,

which at `b ≥ 200` is about `10 ^ (-50)`, not `1/2`.  That is exactly the hypothesis shape of
Layer 9's `generation_product_le`, which was built for this and which turns the per-generation
excesses into a product bounded by `exp(3 · (9/16) ^ 200 · 256/175) = 1 + 4.6 × 10 ^ (-50)`,
uniformly in the number of generations.

So the `3/2` was never the cost of the sign reversal; it was the cost of bounding the offset by
the room bound instead of by the depth band.  Layer 8's statement stays — `Assembly` uses it and
the absolute constant is convenient there — but the census uses this one.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

variable {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}

/-- The per-incidence excess, as Layer 9's `generation_product_le` wants it. -/
def chargeExcessM (b : ℕ) : ℝ := 3 * (9 / 16 : ℝ) ^ b

theorem chargeExcessM_nonneg (b : ℕ) : 0 ≤ chargeExcessM b := by
  unfold chargeExcessM; positivity

/-- `3 ^ depth ≤ 3 · (9/16) ^ base · root`: the depth band against the root lower bound. -/
theorem threePow_depthM_le (hbaseNine : ∀ i, 9 ≤ base i)
    (hrootLower : ∀ i, 16 ^ base i ≤ root i) (z : IncidenceM Label root base shift K) :
    (3 : ℝ) ^ depthM z ≤ chargeExcessM (base (labelM z)) * (root (labelM z) : ℝ) := by
  have hd : depthM z ≤ 2 * base (labelM z) + 1 :=
    ndGeom2ShiftedWideSymmetricSelectedDepth_le_two_mul_add_one (depthM_mem z)
  have hpow : (3 : ℝ) ^ depthM z ≤ (3 : ℝ) ^ (2 * base (labelM z) + 1) :=
    pow_le_pow_right₀ (by norm_num) hd
  have hnine : (3 : ℝ) ^ (2 * base (labelM z) + 1) = 3 * (9 : ℝ) ^ base (labelM z) := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  have hsixteen : ((16 : ℕ) ^ base (labelM z) : ℝ) ≤ (root (labelM z) : ℝ) := by
    exact_mod_cast hrootLower (labelM z)
  have h16 : (0 : ℝ) < (16 : ℝ) ^ base (labelM z) := by positivity
  have hsixteenR : (16 : ℝ) ^ base (labelM z) ≤ (root (labelM z) : ℝ) := by
    push_cast at hsixteen; exact hsixteen
  calc (3 : ℝ) ^ depthM z
      ≤ 3 * (9 : ℝ) ^ base (labelM z) := hnine ▸ hpow
    _ = chargeExcessM (base (labelM z)) * (16 : ℝ) ^ base (labelM z) := by
        unfold chargeExcessM
        rw [div_pow]
        field_simp
    _ ≤ chargeExcessM (base (labelM z)) * (root (labelM z) : ℝ) :=
        mul_le_mul_of_nonneg_left hsixteenR (chargeExcessM_nonneg _)

/-- **The sharp charge bound.**  `+1` has this with excess `0`. -/
theorem sourceM_mul_atomM_le_root_sharp (hrootOdd : ∀ i, Odd (root i))
    (hbaseNine : ∀ i, 9 ≤ base i) (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (z : IncidenceM Label root base shift K) :
    (sourceM z : ℝ) * atomM z ≤
      (1 + chargeExcessM (base (labelM z))) * (root (labelM z) : ℝ) := by
  have hcl := sourceM_cleared hrootOdd z
  have henvN : Tao.taoOffsetNum (chronologicalWordM z) ≤
      2 ^ Tao.taoTupleWeight (rootSideWordM z) * 3 ^ depthM z := by
    have h := Tao.taoOffsetNum_le_two_pow_weight_mul_three_pow_length (chronologicalWordM z)
    rwa [chronologicalWordM_length z, chronologicalWordM_weight z] at h
  have h2W : (0 : ℝ) < (2 : ℝ) ^ Tao.taoTupleWeight (rootSideWordM z) := by positivity
  have hclR : (3 : ℝ) ^ depthM z * (sourceM z : ℝ) =
      (2 : ℝ) ^ Tao.taoTupleWeight (rootSideWordM z) * (root (labelM z) : ℝ) +
        (Tao.taoOffsetNum (chronologicalWordM z) : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hcl
    push_cast at h
    exact h
  have henvR : (Tao.taoOffsetNum (chronologicalWordM z) : ℝ) ≤
      (2 : ℝ) ^ Tao.taoTupleWeight (rootSideWordM z) * (3 : ℝ) ^ depthM z := by
    exact_mod_cast henvN
  have hdepth := threePow_depthM_le (base := base) hbaseNine hrootLower z
  have key : (3 : ℝ) ^ depthM z * (sourceM z : ℝ) ≤
      (2 : ℝ) ^ Tao.taoTupleWeight (rootSideWordM z) *
        ((1 + chargeExcessM (base (labelM z))) * (root (labelM z) : ℝ)) := by
    rw [hclR]
    nlinarith [henvR, hdepth, h2W]
  rw [atomM_eq_div, ← mul_div_assoc, div_le_iff₀ h2W]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ depthM z := by positivity
  nlinarith [key]

/-- The excess shrinks as the floor rises. -/
theorem chargeExcessM_antitone {b₀ b : ℕ} (h : b₀ ≤ b) : chargeExcessM b ≤ chargeExcessM b₀ := by
  unfold chargeExcessM
  have := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 9/16) (by norm_num : (9:ℝ)/16 ≤ 1) h
  linarith

/-- **The sharp charge bound with a uniform floor.** -/
theorem sourceM_mul_atomM_le_root_sharp_uniform {b₀ : ℕ} (hrootOdd : ∀ i, Odd (root i))
    (hbaseNine : ∀ i, 9 ≤ base i) (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (hbase : ∀ i, b₀ ≤ base i) (z : IncidenceM Label root base shift K) :
    (sourceM z : ℝ) * atomM z ≤ (1 + chargeExcessM b₀) * (root (labelM z) : ℝ) := by
  refine (sourceM_mul_atomM_le_root_sharp hrootOdd hbaseNine hrootLower z).trans ?_
  have hroot : (0 : ℝ) ≤ (root (labelM z) : ℝ) := Nat.cast_nonneg _
  have := chargeExcessM_antitone (hbase (labelM z))
  nlinarith

end

end ThreeXMinusOne
