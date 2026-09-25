import ThreeXMinusOne.Map
import Erdos1135.ND.PositiveDensity.GeneralTargetResidueCoverage

/-!
# General-target root coverage for `3x−1`

Layer 1 of the port.  This is `Erdos1135.ND.PositiveDensity.GeneralTargetResidueCoverage`
with the sign reversed.  The purely arithmetic helpers it rests on
(`ndA5PreviousPhysicalCollapseSource` and its residue theory, and the map-generic
`exists_bound_predecessor_no_return`) are reused verbatim from the artifact: they carry no
dependence on which of `3x±1` is in play.

The output is the same as on the `+1` side: for every target `a > 0` with `3 ∤ a`, every
modulus `3^q`, every residue `y` and every bound `X`, there is an odd `R > X` in residue class
`y` that reaches `a` under `3x−1` and never returns to itself under the accelerated map.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

/-- The `3x−1` general-target root.  Mirrors `ndGeneralTargetRoot` with `3r+1` replaced by
`3r−1`. -/
def rootM (r k : ℕ) : ℕ :=
  (3 * r - 1) * ndA5PreviousPhysicalCollapseSource k + r

theorem rootM_pos {r : ℕ} (hr : 0 < r) (k : ℕ) : 0 < rootM r k := by
  have h : rootM r k = (3 * r - 1) * ndA5PreviousPhysicalCollapseSource k + r := rfl
  omega

/-- The cleared form: `3·root − 1 = 4^k·(3r−1)`, written without truncated subtraction. -/
theorem rootM_cleared {r : ℕ} (hr : 0 < r) (k : ℕ) :
    3 * rootM r k = 4 ^ k * (3 * r - 1) + 1 := by
  have hc := three_mul_ndA5PreviousPhysicalCollapseSource_add_one k
  set c := ndA5PreviousPhysicalCollapseSource k with hcdef
  obtain ⟨t, ht⟩ : ∃ t, 3 * r = t + 1 := ⟨3 * r - 1, by omega⟩
  have h1 : 3 * r - 1 = t := by omega
  have hrw : rootM r k = t * c + r := by rw [rootM, h1]
  rw [hrw, h1, ← hc]
  have hexp : 3 * (t * c + r) = 3 * (t * c) + 3 * r := by ring
  rw [hexp, ht]
  ring

theorem rootM_cleared_sub {r : ℕ} (hr : 0 < r) (k : ℕ) :
    3 * rootM r k - 1 = 4 ^ k * (3 * r - 1) := by
  rw [rootM_cleared hr k]; simp

theorem rootM_succ {r : ℕ} (hr : 0 < r) (k : ℕ) :
    rootM r (k + 1) + 1 = 4 * rootM r k := by
  have h1 := rootM_cleared hr k
  have h2 := rootM_cleared hr (k + 1)
  have hp : (4 : ℕ) ^ (k + 1) * (3 * r - 1) = 4 * (4 ^ k * (3 * r - 1)) := by
    rw [pow_succ]; ring
  rw [hp] at h2
  omega

theorem rootM_odd {r : ℕ} (hr : 0 < r) {k : ℕ} (hk : 0 < k) : Odd (rootM r k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hs := rootM_succ hr j
  have hj := rootM_pos hr j
  show Odd (rootM r (j + 1))
  rw [Nat.odd_iff]
  omega

theorem rootM_ge_index {r : ℕ} (hr : 0 < r) (k : ℕ) : k ≤ rootM r k := by
  have h := self_le_ndA5PreviousPhysicalCollapseSource k
  have h2 : 1 ≤ 3 * r - 1 := by omega
  have hform : rootM r k = (3 * r - 1) * ndA5PreviousPhysicalCollapseSource k + r := rfl
  nlinarith [h, h2]

/-- Solvability of the head equation `3r = 2^e·a + 1`.  On the `+1` side the admissible
exponents are `e ≡ 0 (mod 2)` for `a ≡ 1` and `e ≡ 1` for `a ≡ 2`; here the two parities are
swapped, which is the only change. -/
theorem exists_rootM_start {a : ℕ} (ha : 0 < a) (hthree : ¬ 3 ∣ a) :
    ∃ r e : ℕ, 0 < e ∧ 0 < r ∧ 3 * r = 2 ^ e * a + 1 := by
  have hmod : a % 3 = 1 ∨ a % 3 = 2 := by
    have hn : a % 3 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hthree
    omega
  rcases hmod with h | h
  · refine ⟨(2 * a + 1) / 3, 1, by norm_num, ?_, ?_⟩
    · have hm : (2 * a + 1) % 3 = 0 := by omega
      omega
    · have hm : (2 * a + 1) % 3 = 0 := by omega
      have : (2 : ℕ) ^ 1 * a = 2 * a := by norm_num
      omega
  · refine ⟨(4 * a + 1) / 3, 2, by norm_num, ?_, ?_⟩
    · have hm : (4 * a + 1) % 3 = 0 := by omega
      omega
    · have hm : (4 * a + 1) % 3 = 0 := by omega
      have : (2 : ℕ) ^ 2 * a = 4 * a := by norm_num
      omega

theorem rootM_reaches {a r e k : ℕ} (hr : 0 < r)
    (hstart : 3 * r = 2 ^ e * a + 1) (hk : 0 < k) :
    ReachesM (rootM r k) a := by
  have ho := rootM_odd hr hk
  have h3r : 3 * r - 1 = 2 ^ e * a := by omega
  have hpow : (4 : ℕ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  have hstep : (4 : ℕ) ^ k * (3 * r - 1) = 2 ^ (2 * k + e) * a := by
    rw [h3r, hpow, pow_add, mul_assoc]
  have hc : 3 * rootM r k - 1 = 2 ^ (2 * k + e) * a := by
    rw [rootM_cleared_sub hr k, hstep]
  refine ⟨2 * k + e + 1, ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_one, colM_odd (Nat.odd_iff.mp ho), hc]
  exact colM_iterate_powTwo_mul (2 * k + e) a

/-- Every general-target root has the same accelerated successor as its seed, so the no-return
bound for the seed transfers to the whole family. -/
theorem rootM_syrM {r : ℕ} (hr : 0 < r) (k : ℕ) : syrM (rootM r k) = syrM r := by
  have hpow : (4 : ℕ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  have h : 3 * rootM r k - 1 = 2 ^ (2 * k) * (3 * r - 1) := by
    rw [rootM_cleared_sub hr k, hpow]
  show ordCompl[2] (3 * rootM r k - 1) = ordCompl[2] (3 * r - 1)
  rw [h]
  exact Nat.ordCompl_self_pow_mul (3 * r - 1) (2 * k) Nat.prime_two

/-! ## Residue coverage -/

theorem coprime_three_pow_sub {r : ℕ} (hr : 0 < r) (q : ℕ) :
    Nat.Coprime (3 ^ q) (3 * r - 1) := by
  apply Nat.Coprime.pow_left
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro hdvd
  obtain ⟨c, hc⟩ := hdvd
  omega

theorem rootM_residue_injective {r : ℕ} (hr : 0 < r) (q : ℕ) :
    Function.Injective (fun m : Fin (3 ^ q) =>
      (⟨rootM r m % 3 ^ q, Nat.mod_lt _ (by positivity)⟩ : Fin (3 ^ q))) := by
  intro m n he
  have hmod : Nat.ModEq (3 ^ q) (rootM r m) (rootM r n) := congrArg Fin.val he
  have hm : Nat.ModEq (3 ^ q) (ndA5PreviousPhysicalCollapseSource m)
      (ndA5PreviousPhysicalCollapseSource n) :=
    Nat.ModEq.cancel_left_of_coprime (coprime_three_pow_sub hr q)
      (Nat.ModEq.add_right_cancel' r hmod)
  exact ndCollapseSource_residue_injective q (Fin.ext hm)

theorem rootM_residue_surjective {r : ℕ} (hr : 0 < r) (q : ℕ) :
    Function.Surjective (fun m : Fin (3 ^ q) =>
      (⟨rootM r m % 3 ^ q, Nat.mod_lt _ (by positivity)⟩ : Fin (3 ^ q))) :=
  Finite.surjective_of_injective (rootM_residue_injective hr q)

theorem rootM_modEq_of_period (r q m t : ℕ) :
    Nat.ModEq (3 ^ q) (rootM r m) (rootM r (m + t * 3 ^ q)) := by
  have h := (ndCollapseSource_modEq_of_add_iff q m (t * 3 ^ q)).2 (Nat.dvd_mul_left _ _)
  exact (h.mul_left (3 * r - 1)).add_right r

/-- **The Layer-1 output.**  Arbitrarily large odd `3x−1`-predecessors of any admissible target,
in every ternary residue class, that never return to themselves under the accelerated map. -/
theorem exists_large_nonreturning_predecessorM_in_residue
    {a : ℕ} (ha : 0 < a) (hthree : ¬ 3 ∣ a) (q X : ℕ) (y : Fin (3 ^ q)) :
    ∃ R : ℕ, X < R ∧ Odd R ∧ ReachesM R a ∧ R % 3 ^ q = y ∧
      ∀ k : ℕ, 0 < k → (syrM^[k]) R ≠ R := by
  obtain ⟨r, e, he, hr, hstart⟩ := exists_rootM_start ha hthree
  obtain ⟨B, hB⟩ := exists_bound_predecessor_no_return syrM (syrM r)
  obtain ⟨m, hm⟩ := rootM_residue_surjective hr q y
  let k := (m : ℕ) + (max B X + 1) * 3 ^ q
  have hk : max B X < k := by
    have hq : 1 ≤ 3 ^ q := Nat.one_le_pow _ _ (by norm_num)
    have h := Nat.mul_le_mul_left (max B X + 1) hq
    dsimp only [k]
    omega
  have hR := hk.trans_le (rootM_ge_index hr k)
  have hmod := rootM_modEq_of_period r q m (max B X + 1)
  change rootM r m % 3 ^ q = rootM r k % 3 ^ q at hmod
  have hy : rootM r k % 3 ^ q = y := hmod.symm.trans (congrArg Fin.val hm)
  refine ⟨rootM r k, (le_max_right B X).trans_lt hR, rootM_odd hr (by omega),
    rootM_reaches hr hstart (by omega), hy, ?_⟩
  exact hB _ ((le_max_left B X).trans_lt hR) ⟨1, by simpa using rootM_syrM hr k⟩

end ThreeXMinusOne
