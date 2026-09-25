import ThreeXMinusOne.IncidenceCharge

/-!
# The generation product: why the `3x−1` excess does not compound

`fullTerminal_source_mul_weight_le_frozenOwner` chains one incidence per generation by
`ht.trans he`, an exact composition on the `+1` side.  For `3x−1` each generation contributes a
factor `1 + ε_k`, and a naive reading gives `(3/2)^n` with `n` unbounded — which would sink the
density.

It does not, because the state's floor **grows**: `explicit_forward_floor` unfolds the iterate's
floor as `floor + floor/100`, so with `floor_twoHundred` it increases by at least `2` per
generation.  Combined with the room bound this makes

    ε_k ≤ 3·(9/16)^(floor k) ≤ 3·(9/16)^200 · (81/256)^k,

a geometric series.  The product over *any* number of generations is therefore bounded by
`exp (3·(256/175)·(9/16)^200)`, an absolute constant — uniformly in `n`, hence uniformly in `Y`.
That constant is `1 + O(10⁻⁴⁹)`.
-/

namespace ThreeXMinusOne

open Erdos1135
open scoped BigOperators

noncomputable section

theorem geom_sum_le_inv_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, q ^ k ≤ 1 / (1 - q) := by
  have hpos : (0 : ℝ) < 1 - q := by linarith
  have key : ∀ m : ℕ, (1 - q) * ∑ k ∈ Finset.range m, q ^ k = 1 - q ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
  have hqn : (0 : ℝ) ≤ q ^ n := by positivity
  have h := key n
  rw [le_div_iff₀ hpos]
  nlinarith [h, hqn]

theorem prod_one_add_le_exp_sum (ε : ℕ → ℝ) (hε : ∀ k, 0 ≤ ε k) (n : ℕ) :
    ∏ k ∈ Finset.range n, (1 + ε k) ≤ Real.exp (∑ k ∈ Finset.range n, ε k) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod (fun k _ => by linarith [hε k]) (fun k _ => ?_)
  have := Real.add_one_le_exp (ε k)
  linarith

/-- The per-generation excess, straight from the room bound. -/
theorem generation_excess_le {d b rt : ℕ} (hb : 200 ≤ b) (hd : d ≤ 2 * b + 1)
    (hrt : 16 ^ b ≤ rt) :
    (3 : ℝ) ^ d / (rt : ℝ) ≤ 3 * (9 / 16 : ℝ) ^ b := by
  have hrtpos : (0 : ℝ) < (rt : ℝ) := by
    have : (0 : ℕ) < 16 ^ b := by positivity
    exact_mod_cast lt_of_lt_of_le this hrt
  have h16 : ((16 : ℝ)) ^ b ≤ (rt : ℝ) := by exact_mod_cast hrt
  have h16pos : (0 : ℝ) < (16 : ℝ) ^ b := by positivity
  have hnum : (3 : ℝ) ^ d ≤ 3 * (9 : ℝ) ^ b := by
    have : (3 : ℝ) ^ d ≤ (3 : ℝ) ^ (2 * b + 1) :=
      pow_le_pow_right₀ (by norm_num) hd
    calc (3 : ℝ) ^ d ≤ (3 : ℝ) ^ (2 * b + 1) := this
      _ = 3 * (9 : ℝ) ^ b := by
          have h9 : (9 : ℝ) = (3 : ℝ) ^ 2 := by norm_num
          rw [h9, ← pow_mul, ← pow_succ']
  calc (3 : ℝ) ^ d / (rt : ℝ) ≤ (3 * (9 : ℝ) ^ b) / (rt : ℝ) := by
        gcongr
    _ ≤ (3 * (9 : ℝ) ^ b) / (16 : ℝ) ^ b := by
        gcongr
    _ = 3 * (9 / 16 : ℝ) ^ b := by
        rw [div_pow]; ring

/-- A floor that starts at `200` and gains at least `2` per generation. -/
theorem floor_lower (fl : ℕ → ℕ) (h0 : 200 ≤ fl 0) (hstep : ∀ k, fl k + 2 ≤ fl (k + 1)) (k : ℕ) :
    200 + 2 * k ≤ fl k := by
  induction k with
  | zero => simpa using h0
  | succ k ih =>
      have := hstep k
      omega

/-- **The generation product is bounded by an absolute constant, uniformly in `n`.** -/
theorem generation_product_le (ε : ℕ → ℝ) (hε : ∀ k, 0 ≤ ε k)
    (fl : ℕ → ℕ) (h0 : 200 ≤ fl 0) (hstep : ∀ k, fl k + 2 ≤ fl (k + 1))
    (hbound : ∀ k, ε k ≤ 3 * (9 / 16 : ℝ) ^ fl k) (n : ℕ) :
    ∏ k ∈ Finset.range n, (1 + ε k) ≤
      Real.exp (3 * (9 / 16 : ℝ) ^ 200 * (256 / 175 : ℝ)) := by
  have hq0 : (0 : ℝ) ≤ (81 / 256 : ℝ) := by norm_num
  have hq1 : (81 / 256 : ℝ) < 1 := by norm_num
  have hstepbd : ∀ k, ε k ≤ 3 * (9 / 16 : ℝ) ^ 200 * (81 / 256 : ℝ) ^ k := by
    intro k
    refine (hbound k).trans ?_
    have hk : 200 + 2 * k ≤ fl k := floor_lower fl h0 hstep k
    have hmono : (9 / 16 : ℝ) ^ fl k ≤ (9 / 16 : ℝ) ^ (200 + 2 * k) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
    have hsplit : (9 / 16 : ℝ) ^ (200 + 2 * k) = (9 / 16 : ℝ) ^ 200 * (81 / 256 : ℝ) ^ k := by
      rw [pow_add, pow_mul]
      norm_num
    calc 3 * (9 / 16 : ℝ) ^ fl k ≤ 3 * (9 / 16 : ℝ) ^ (200 + 2 * k) := by linarith
      _ = 3 * (9 / 16 : ℝ) ^ 200 * (81 / 256 : ℝ) ^ k := by rw [hsplit]; ring
  have hsum : ∑ k ∈ Finset.range n, ε k ≤ 3 * (9 / 16 : ℝ) ^ 200 * (256 / 175 : ℝ) := by
    have h1 : ∑ k ∈ Finset.range n, ε k ≤
        ∑ k ∈ Finset.range n, (3 * (9 / 16 : ℝ) ^ 200 * (81 / 256 : ℝ) ^ k) :=
      Finset.sum_le_sum (fun k _ => hstepbd k)
    have h2 : ∑ k ∈ Finset.range n, (3 * (9 / 16 : ℝ) ^ 200 * (81 / 256 : ℝ) ^ k) =
        3 * (9 / 16 : ℝ) ^ 200 * ∑ k ∈ Finset.range n, (81 / 256 : ℝ) ^ k := by
      rw [Finset.mul_sum]
    have h3 : ∑ k ∈ Finset.range n, (81 / 256 : ℝ) ^ k ≤ 1 / (1 - 81 / 256 : ℝ) :=
      geom_sum_le_inv_one_sub hq0 hq1 n
    have h4 : (1 : ℝ) / (1 - 81 / 256) = 256 / 175 := by norm_num
    have hApos : (0 : ℝ) ≤ 3 * (9 / 16 : ℝ) ^ 200 := by positivity
    rw [h2] at h1
    rw [h4] at h3
    nlinarith [h1, h3, hApos]
  exact (prod_one_add_le_exp_sum ε hε n).trans (Real.exp_le_exp.mpr hsum)

end

end ThreeXMinusOne
