import ConjectureAZ
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# The 3x+1 Growth Exponent Conjecture

Kontorovich–Lagarias record the growth exponent conjecture as strictly weaker than
Applegate–Lagarias Conjecture A.  With `ALConjectureAZ.conjectureA_AL` in hand it is a corollary,
and the derivation is the obvious one:

* Conjecture A gives `c_a · x ≤ π_a(x)` for `x ≥ |a|`;
* trivially `π_a(x) ≤ 2x + 1`, since `[-x, x]` contains only `2⌊x⌋ + 1` integers;
* so `(log c_a + log x)/log x ≤ log π_a(x)/log x ≤ (log 3 + log x)/log x` for `x ≥ 2`,
  and both outer terms tend to `1`.

The squeeze gives an honest `Tendsto`, which is stronger than the conjecture asks: the ratio
converges, so the `liminf` and `limsup` are not merely equal to `1` but equal to a limit.

The upper bound is where the count being over `ℤ` matters — the window is `[-x, x]`, not `[0, x]`,
so the trivial bound is `2x + 1` rather than `x + 1`.  Nothing downstream depends on the constant.
-/

namespace ALConjectureAZ

open Filter Topology

/-! ## 1. The trivial upper bound -/

/-- At most `2m + 1` integers lie in `[-m, m]`. -/
theorem piAZ_le (a : ℤ) (m : ℕ) : piAZ a m ≤ 2 * m + 1 := by
  classical
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Int.card_Icc]
  omega

/-- `π_a(x) ≤ 2x + 1`: the window `[-x, x]` has nothing else in it. -/
theorem piAL_le {a : ℤ} (ha : a ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    (piAL a x : ℝ) ≤ 2 * x + 1 := by
  rw [piAL_eq_piAZ ha hx]
  have h1 : piAZ a ⌊x⌋₊ ≤ 2 * ⌊x⌋₊ + 1 := piAZ_le a _
  have h2 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have h3 : ((piAZ a ⌊x⌋₊ : ℕ) : ℝ) ≤ ((2 * ⌊x⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
  refine h3.trans ?_
  push_cast
  linarith

/-! ## 2. The growth exponent -/

/-- `log π_a(x) / log x`, the quantity whose `liminf` and `limsup` the conjecture is about. -/
noncomputable def growthRatio (a : ℤ) (x : ℝ) : ℝ := Real.log (piAL a x) / Real.log x

/-- `η₃⁻(a) = liminf_{x→∞} log π_a(x) / log x`. -/
noncomputable def eta3Inf (a : ℤ) : ℝ := liminf (growthRatio a) atTop

/-- `η₃⁺(a) = limsup_{x→∞} log π_a(x) / log x`. -/
noncomputable def eta3Sup (a : ℤ) : ℝ := limsup (growthRatio a) atTop

/-- **The ratio converges to `1`** — stronger than the conjecture, which only asks that the two
one-sided exponents agree at `1`. -/
theorem tendsto_growthRatio (a : ℤ) (h3 : ¬ (3 ∣ a)) :
    Tendsto (growthRatio a) atTop (𝓝 1) := by
  have ha0 : a ≠ 0 := by rintro rfl; exact h3 (dvd_zero 3)
  obtain ⟨c, hc, hb⟩ := conjectureA_AL a h3
  -- both envelopes tend to 1
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have env : ∀ k : ℝ, Tendsto (fun x : ℝ => 1 + k / Real.log x) atTop (𝓝 1) := by
    intro k
    have h0 : Tendsto (fun x : ℝ => k / Real.log x) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hlog
    simpa using tendsto_const_nhds.add h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (env (Real.log c)) (env (Real.log 3))
    ?_ ?_
  · filter_upwards [eventually_ge_atTop (max |(a : ℝ)| 2)] with x hx
    have hax : |(a : ℝ)| ≤ x := le_trans (le_max_left _ _) hx
    have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
    have hcx : c * x ≤ (piAL a x : ℝ) := hb x hax
    have hcxpos : (0 : ℝ) < c * x := by positivity
    have hstep : Real.log c + Real.log x ≤ Real.log (piAL a x) := by
      rw [← Real.log_mul (ne_of_gt hc) (ne_of_gt hxpos)]
      exact Real.log_le_log hcxpos hcx
    have hne : Real.log x ≠ 0 := ne_of_gt hlogx
    rw [growthRatio, ← sub_nonneg]
    have hid : Real.log (piAL a x) / Real.log x - (1 + Real.log c / Real.log x)
        = (Real.log (piAL a x) - (Real.log c + Real.log x)) / Real.log x := by
      field_simp
      ring
    rw [hid]
    exact div_nonneg (by linarith) hlogx.le
  · filter_upwards [eventually_ge_atTop (max |(a : ℝ)| 2)] with x hx
    have hax : |(a : ℝ)| ≤ x := le_trans (le_max_left _ _) hx
    have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
    have hcx : c * x ≤ (piAL a x : ℝ) := hb x hax
    have hppos : (0 : ℝ) < (piAL a x : ℝ) := lt_of_lt_of_le (by positivity) hcx
    have hub : (piAL a x : ℝ) ≤ 3 * x := by
      have := piAL_le ha0 hxpos.le
      linarith
    have hstep : Real.log (piAL a x) ≤ Real.log 3 + Real.log x := by
      rw [← Real.log_mul (by norm_num) (ne_of_gt hxpos)]
      exact Real.log_le_log hppos hub
    have hne : Real.log x ≠ 0 := ne_of_gt hlogx
    rw [growthRatio, ← sub_nonneg]
    have hid : 1 + Real.log 3 / Real.log x - Real.log (piAL a x) / Real.log x
        = (Real.log 3 + Real.log x - Real.log (piAL a x)) / Real.log x := by
      field_simp
      ring
    rw [hid]
    exact div_nonneg (by linarith) hlogx.le

/-! ## 3. The conjecture -/

/-- The **3x+1 Growth Exponent Conjecture**: `η₃⁻(a) = η₃⁺(a) = 1` for `3 ∤ a`. -/
def GrowthExponentConjecture : Prop :=
  ∀ a : ℤ, ¬ (3 ∣ a) → eta3Inf a = 1 ∧ eta3Sup a = 1

/-- **The Growth Exponent Conjecture, unconditionally**, as a corollary of Conjecture A. -/
theorem growthExponentConjecture : GrowthExponentConjecture := by
  intro a h3
  have h := tendsto_growthRatio a h3
  exact ⟨h.liminf_eq, h.limsup_eq⟩

end ALConjectureAZ
