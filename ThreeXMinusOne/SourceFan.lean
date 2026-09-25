import ThreeXMinusOne.Decode
import ThreeXMinusOne.Map

/-!
# The `3x−1` terminal source fan

The arithmetic core of `Geom2ShiftedWideSymmetricTerminalCapOneCompression`.

The compression sends a cap-`K` terminal incidence to a cap-one one together with a fan index
`j`, by shaving `2j` off the head exponent.  Shaving `2j` multiplies the cleared numerator by
`4 ^ j`, and the map on sources that does this is the fan.  For `+1` it is `y ↦ 4y + 1`, whose
`j`-fold iterate satisfies `3·fan + 1 = 4^j·(3x + 1)`.  For `3x−1` it is `y ↦ 4y − 1`, and the
identity is `3·fan − 1 = 4^j·(3x − 1)`.

Written without any `ℕ` subtraction on the identity — as `3·fan + 4^j = 3·(4^j·x) + 1` — because
`omega` can close the induction step only if the nonlinear products are presented as atoms, and
`4^j·x` has to be one of them.

The head-compression lemma then says: a source whose first exponent is `v` with `2j < v` is the
`j`-fold fan of a source whose first exponent is `v − 2j` and which drives the same word tail to
the same root.
-/

namespace ThreeXMinusOne

open Erdos1135

noncomputable section

/-- The `3x−1` fan: `j`-fold `y ↦ 4y − 1`. -/
def sourceFanM (j x : ℕ) : ℕ := ((fun y : ℕ => 4 * y - 1)^[j]) x

@[simp] theorem sourceFanM_zero (x : ℕ) : sourceFanM 0 x = x := rfl

theorem sourceFanM_succ (j x : ℕ) : sourceFanM (j + 1) x = 4 * sourceFanM j x - 1 := by
  unfold sourceFanM
  rw [Function.iterate_succ_apply']

theorem sourceFanM_pos {x : ℕ} (hx : 1 ≤ x) (j : ℕ) : 1 ≤ sourceFanM j x := by
  induction j with
  | zero => simpa using hx
  | succ j ih => rw [sourceFanM_succ]; omega

/-- **The fan's cleared identity.**  `+1` has `3·fan + 1 = 4^j·(3x + 1)`. -/
theorem sourceFanM_cleared {x : ℕ} (hx : 1 ≤ x) (j : ℕ) :
    3 * sourceFanM j x + 4 ^ j = 3 * (4 ^ j * x) + 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hf := sourceFanM_pos hx j
      have hp : (4 : ℕ) ^ (j + 1) = 4 * 4 ^ j := by ring
      have hA : 4 * 4 ^ j * x = 4 * (4 ^ j * x) := by ring
      rw [sourceFanM_succ, hp, hA]
      omega

/-- **Head compression.**  Shaving `2j` off the leading exponent un-fans the source. -/
theorem exists_head_compressed_sourceM {tail : List ℕ+} {v : ℕ+} {x r j : ℕ}
    (hr : Odd r) (hj : 2 * j < (v : ℕ))
    (haff : taoAffListM (v :: tail) (x : ℚ) = (r : ℚ)) :
    ∃ x0 : ℕ, Odd x0 ∧ x = sourceFanM j x0 ∧
      taoAffListM (⟨(v : ℕ) - 2 * j, by omega⟩ :: tail) (x0 : ℚ) = (r : ℚ) := by
  obtain ⟨hx, hvalues, _⟩ := taoAffListM_oddNat_decode (v :: tail) x r hr haff
  have hv : syrMExponent x = (v : ℕ) := by
    have hhead := List.cons.inj hvalues
    exact congrArg (fun a : ℕ+ => (a : ℕ)) hhead.1
  have hfactor : 2 ^ (v : ℕ) * syrM x + 1 = 3 * x := by
    rw [← hv]; exact two_pow_syrMExponent_mul_syrM_add_one hx.pos
  have hxpos : 1 ≤ x := hx.pos
  set B := 2 ^ ((v : ℕ) - 2 * j) * syrM x with hBdef
  have hB : 4 ^ j * B + 1 = 3 * x := by
    rw [← hfactor, hBdef]
    have hvsplit : (v : ℕ) = 2 * j + ((v : ℕ) - 2 * j) := by omega
    conv_rhs => rw [hvsplit, pow_add]
    rw [pow_mul]
    norm_num
    ring
  have hmod : B % 3 = 2 := by
    have h4 : 4 ^ j % 3 = 1 := by
      rw [Nat.pow_mod]; norm_num
    have hm : (4 ^ j * B + 1) % 3 = 0 := by rw [hB]; omega
    rw [Nat.add_mod, Nat.mul_mod, h4, one_mul] at hm
    omega
  have hB0 : 3 * ((B + 1) / 3) = B + 1 := by omega
  set x0 := (B + 1) / 3 with hx0def
  have hx0pos : 1 ≤ x0 := by omega
  have hhead0 : taoSingleAffM ⟨(v : ℕ) - 2 * j, by omega⟩ (x0 : ℚ) = (syrM x : ℚ) := by
    have hnat : 3 * x0 = syrM x * 2 ^ ((v : ℕ) - 2 * j) + 1 := by
      rw [hB0, hBdef]; ring
    have h3 : ((3 : ℚ) * (x0 : ℚ)) = ((syrM x : ℚ) * (2 : ℚ) ^ ((v : ℕ) - 2 * j) + 1) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) hnat
    unfold taoSingleAffM
    rw [div_eq_iff (by positivity)]
    show (3 : ℚ) * (x0 : ℚ) - 1 = (syrM x : ℚ) * (2 : ℚ) ^ ((v : ℕ) - 2 * j)
    linarith [h3]
  have hhead : taoSingleAffM v (x : ℚ) = (syrM x : ℚ) := by
    unfold taoSingleAffM
    apply (div_eq_iff (by positivity)).2
    have hnat : 3 * x = syrM x * 2 ^ (v : ℕ) + 1 := by rw [← hfactor]; ring
    have h3 : ((3 : ℚ) * (x : ℚ)) = ((syrM x : ℚ) * (2 : ℚ) ^ (v : ℕ) + 1) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) hnat
    linarith [h3]
  have haff0 : taoAffListM (⟨(v : ℕ) - 2 * j, by omega⟩ :: tail) (x0 : ℚ) = (r : ℚ) := by
    change taoAffListM tail (taoSingleAffM _ _) = _
    rw [hhead0, ← hhead]
    exact haff
  refine ⟨x0, (taoAffListM_oddNat_decode _ x0 r hr haff0).choose, ?_, haff0⟩
  have hfan := sourceFanM_cleared hx0pos j
  have hBx : 4 ^ j * B + 4 ^ j = 3 * (4 ^ j * x0) := by
    calc 4 ^ j * B + 4 ^ j = 4 ^ j * (B + 1) := by ring
      _ = 4 ^ j * (3 * x0) := by rw [← hB0]
      _ = 3 * (4 ^ j * x0) := by ring
  omega

end

end ThreeXMinusOne
