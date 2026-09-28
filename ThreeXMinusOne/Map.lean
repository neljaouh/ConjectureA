import Erdos1135.Terras.Core.Defs
import Erdos1135.Tao.Syracuse.Basic
import Mathlib.Tactic

/-!
# The `3x−1` map and its accelerated (Syracuse) form

Layer 0 of the port of M2 to `3x−1`.  Every declaration here mirrors, one for one, a
declaration of the artifact's `Erdos1135.Tao.Syracuse.Basic` / `CollatzBridge` / `ParityBridge`
for `3x+1`.  Truncated subtraction is avoided throughout by carrying the cleared form
`2^e * syrM N + 1 = 3 * N` instead of `2^e * syrM N = 3 * N - 1`.
-/

namespace ThreeXMinusOne

open Erdos1135

/-- The ordinary `3x−1` map: `n/2` on evens, `3n−1` on odds. -/
def colM (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n - 1

theorem colM_even {n : ℕ} (h : n % 2 = 0) : colM n = n / 2 := by
  simp [colM, h]

theorem colM_odd {n : ℕ} (h : n % 2 = 1) : colM n = 3 * n - 1 := by
  simp [colM, h]

/-- `n` reaches `a` under the `3x−1` map. -/
def ReachesM (a b : ℕ) : Prop := ∃ m, colM^[m] a = b

theorem reachesM_refl (n : ℕ) : ReachesM n n := ⟨0, rfl⟩

theorem ReachesM.trans {a b c : ℕ} (hab : ReachesM a b) (hbc : ReachesM b c) :
    ReachesM a c := by
  obtain ⟨m, hm⟩ := hab
  obtain ⟨n, hn⟩ := hbc
  exact ⟨n + m, by rw [Function.iterate_add_apply, hm, hn]⟩

/-! ## The accelerated map -/

/-- The 2-adic exponent stripped by one backward `3x−1` step. -/
def syrMExponent (N : ℕ) : ℕ := Terras.twoAdicExponent (3 * N - 1)

/-- The `3x−1` Syracuse map: the odd part of `3N−1`. -/
def syrM (N : ℕ) : ℕ := ordCompl[2] (3 * N - 1)

theorem num_ne_zero {N : ℕ} (hN : 0 < N) : 3 * N - 1 ≠ 0 := by omega

theorem two_pow_syrMExponent_mul_syrM (N : ℕ) :
    (2 : ℕ) ^ syrMExponent N * syrM N = 3 * N - 1 := by
  simpa [syrM, syrMExponent, Terras.twoAdicExponent]
    using Nat.ordProj_mul_ordCompl_eq_self (3 * N - 1) 2

/-- The cleared form, free of truncated subtraction. -/
theorem two_pow_syrMExponent_mul_syrM_add_one {N : ℕ} (hN : 0 < N) :
    (2 : ℕ) ^ syrMExponent N * syrM N + 1 = 3 * N := by
  have h := two_pow_syrMExponent_mul_syrM N
  omega

theorem syrM_odd {N : ℕ} (hN : 0 < N) : Odd (syrM N) := by
  refine Nat.not_even_iff_odd.mp ?_
  intro heven
  have hdiv : (2 : ℕ) ∣ ordCompl[2] (3 * N - 1) := even_iff_two_dvd.mp heven
  exact Nat.not_dvd_ordCompl Nat.prime_two (num_ne_zero hN) hdiv

theorem syrM_pos {N : ℕ} (hN : 0 < N) : 0 < syrM N :=
  Nat.ordCompl_pos 2 (num_ne_zero hN)

theorem syrMExponent_pos_of_odd {N : ℕ} (hN : Odd N) : 0 < syrMExponent N := by
  obtain ⟨k, hk⟩ := hN
  have hNpos : 0 < N := by omega
  have hdiv : (2 : ℕ) ∣ 3 * N - 1 := ⟨3 * k + 1, by omega⟩
  exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two (num_ne_zero hNpos) hdiv

/-- Odd starts have odd `3x−1` Syracuse orbits. -/
theorem syrM_iterate_odd (n N : ℕ) (hN : Odd N) : Odd ((syrM^[n]) N) := by
  induction n generalizing N with
  | zero => simpa using hN
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (syrM N) (syrM_odd hN.pos)

theorem syrM_iterate_pos (n N : ℕ) (hN : Odd N) : 0 < (syrM^[n]) N :=
  (syrM_iterate_odd n N hN).pos

/-! ## The bridge back to the ordinary map -/

theorem colM_iterate_powTwo_mul (a M : ℕ) : (colM^[a]) ((2 : ℕ) ^ a * M) = M := by
  induction a with
  | zero => simp
  | succ a ih =>
      have hEven : ((2 : ℕ) ^ (a + 1) * M) % 2 = 0 := by
        have : (2 : ℕ) ^ (a + 1) * M = 2 * (2 ^ a * M) := by rw [pow_succ]; ring
        omega
      rw [Function.iterate_succ_apply, colM_even hEven]
      have hdiv : ((2 : ℕ) ^ (a + 1) * M) / 2 = (2 : ℕ) ^ a * M := by
        have : (2 : ℕ) ^ (a + 1) * M = 2 ^ a * M * 2 := by rw [pow_succ]; ring
        rw [this, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
      rw [hdiv]
      exact ih

theorem colM_iterate_syrM_block {M : ℕ} (hM : Odd M) :
    (colM^[syrMExponent M + 1]) M = syrM M := by
  have hMpos : 0 < M := hM.pos
  have hodd : M % 2 = 1 := Nat.odd_iff.mp hM
  rw [Function.iterate_add_apply, Function.iterate_one, colM_odd hodd]
  have hcl : 3 * M - 1 = (2 : ℕ) ^ syrMExponent M * syrM M :=
    (two_pow_syrMExponent_mul_syrM M).symm
  rw [hcl]
  exact colM_iterate_powTwo_mul (syrMExponent M) (syrM M)

theorem reachesM_syrM {M : ℕ} (hM : Odd M) : ReachesM M (syrM M) :=
  ⟨syrMExponent M + 1, colM_iterate_syrM_block hM⟩

theorem reachesM_powTwo_mul (a M : ℕ) : ReachesM ((2 : ℕ) ^ a * M) M :=
  ⟨a, colM_iterate_powTwo_mul a M⟩

theorem reachesM_syrM_iterate {M : ℕ} (hM : Odd M) (k : ℕ) :
    ReachesM M ((syrM^[k]) M) := by
  induction k generalizing M with
  | zero => simpa using reachesM_refl M
  | succ k ih =>
      have hhead : ReachesM M (syrM M) := reachesM_syrM hM
      have htail : ReachesM (syrM M) ((syrM^[k]) (syrM M)) := ih (syrM_odd hM.pos)
      simpa only [Function.iterate_succ_apply] using hhead.trans htail

end ThreeXMinusOne
