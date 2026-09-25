import ThreeXMinusOne.Telescope
import Erdos1135.Tao.Syracuse.OffsetInjectivity

/-!
# The affine decode lemma for `3x−1`

Layer 4 of the port: `Tao/Syracuse/Affine.lean` and `Tao/Syracuse/AffineOdd.lean`.

`taoAffList_oddNat_decode` is the **single** point through which the whole "physical incidence"
machinery touches the arithmetic: a reverse word plus the cleared affine identity is decoded
back into a genuine Syracuse orbit.  In the 517-line
`Geom2ShiftedWideSymmetricRootSideBoundedOvershootPhysicalIncidence` the map is named on exactly
one line, and that line is an application of this lemma.

The port is cheap because the *offset* objects are sign-agnostic: with
`taoSingleAffM a x = (3x−1)/2^a` one gets

    taoAffListM as x = 3^len/2^weight · x − taoOffsetList as

with **the artifact's own `taoOffsetList`**, merely subtracted instead of added.  Consequently
`taoOffsetNum`, its injectivity theory and `two_pow_mul_odd_cancel` are reused verbatim, and the
cleared form `3^len·N = 2^weight·M + taoOffsetNum as` is free of truncated subtraction.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.Tao

noncomputable section

def taoSingleAffM (a : ℕ+) (x : ℚ) : ℚ := ((3 : ℚ) * x - 1) / (2 : ℚ) ^ (a : ℕ)

def taoAffListM : List ℕ+ → ℚ → ℚ
  | [], x => x
  | a :: as, x => taoAffListM as (taoSingleAffM a x)

/-- The closed form.  Note the reused `taoOffsetList`: only the sign in front of it changes. -/
theorem taoAffListM_closed (as : List ℕ+) (x : ℚ) :
    taoAffListM as x =
      (3 : ℚ) ^ as.length / (2 : ℚ) ^ taoTupleWeight as * x - taoOffsetList as := by
  induction as generalizing x with
  | nil => simp [taoAffListM, taoTupleWeight, taoOffsetList]
  | cons a as ih =>
      simp [taoAffListM, taoSingleAffM, taoTupleWeight, taoOffsetList, ih]
      ring_nf

theorem syrM_one_step_eq_taoSingleAffM {N : ℕ} (hN : Odd N) :
    (syrM N : ℚ) = taoSingleAffM ⟨syrMExponent N, syrMExponent_pos_of_odd hN⟩ (N : ℚ) := by
  have hNpos : 0 < N := hN.pos
  have hcast : ((3 * N - 1 : ℕ) : ℚ) = 3 * (N : ℚ) - 1 := by
    have h : (3 : ℕ) * N - 1 + 1 = 3 * N := by omega
    have := congrArg (fun n : ℕ => (n : ℚ)) h
    push_cast at this
    linarith
  unfold syrM syrMExponent Terras.twoAdicExponent taoSingleAffM
  rw [Nat.cast_div_charZero (Nat.ordProj_dvd (3 * N - 1) 2)]
  rw [hcast]
  norm_num

theorem syrM_iterate_eq_taoAffListM (n N : ℕ) (hN : Odd N) :
    (((syrM^[n]) N : ℕ) : ℚ) = taoAffListM (syrMValuationPNatList n N hN) (N : ℚ) := by
  induction n generalizing N with
  | zero => simp [syrMValuationPNatList, taoAffListM]
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      simp only [syrMValuationPNatList, taoAffListM]
      rw [← syrM_one_step_eq_taoSingleAffM hN]
      exact ih (syrM N) (syrM_odd hN.pos)

/-- The cleared form, free of truncated subtraction. -/
theorem taoAffListM_eq_nat_iff_cleared (as : List ℕ+) (N M : ℕ) :
    taoAffListM as (N : ℚ) = (M : ℚ) ↔
      3 ^ as.length * N = 2 ^ taoTupleWeight as * M + taoOffsetNum as := by
  rw [taoAffListM_closed, taoOffsetList_eq_num_div]
  have hden : ((2 : ℚ) ^ taoTupleWeight as) ≠ 0 := by positivity
  constructor
  · intro h
    have hq : (3 : ℚ) ^ as.length * (N : ℚ) =
        (2 : ℚ) ^ taoTupleWeight as * (M : ℚ) + (taoOffsetNum as : ℚ) := by
      field_simp at h
      linarith
    exact_mod_cast hq
  · intro h
    have hq : ((3 ^ as.length * N : ℕ) : ℚ) =
        ((2 ^ taoTupleWeight as * M + taoOffsetNum as : ℕ) : ℚ) := by exact_mod_cast h
    push_cast at hq
    field_simp
    linarith

/-- **The decode lemma.**  Mirrors `Tao.taoAffList_oddNat_decode`. -/
theorem taoAffListM_oddNat_decode (as : List ℕ+) (N M : ℕ) (hM : Odd M)
    (hAff : taoAffListM as (N : ℚ) = (M : ℚ)) :
    ∃ hN : Odd N,
      syrMValuationPNatList as.length N hN = as ∧ (syrM^[as.length]) N = M := by
  induction as generalizing N with
  | nil =>
      have hNM : N = M := by
        have := hAff
        simp only [taoAffListM] at this
        exact_mod_cast this
      subst hNM
      exact ⟨hM, by simp [syrMValuationPNatList], by simp⟩
  | cons a tail ih =>
      have hcleared := (taoAffListM_eq_nat_iff_cleared (a :: tail) N M).mp hAff
      have hoff : taoOffsetNum (a :: tail) =
          3 ^ tail.length + 2 ^ (a : ℕ) * taoOffsetNum tail := rfl
      have hlen : (a :: tail).length = tail.length + 1 := rfl
      have hwt : taoTupleWeight (a :: tail) = (a : ℕ) + taoTupleWeight tail := by
        simp [taoTupleWeight]
      rw [hlen, hwt, hoff] at hcleared
      -- hcleared : 3^(L+1)*N = 2^(a+W)*M + (3^L + 2^a * OffNum tail)
      have h3L : 0 < 3 ^ tail.length := by positivity
      have hNpos : 0 < N := by
        rcases Nat.eq_zero_or_pos N with h | h
        · subst h; simp at hcleared; omega
        · exact h
      obtain ⟨t, ht⟩ : ∃ t, 3 * N = t + 1 := ⟨3 * N - 1, by omega⟩
      have hexp : 3 ^ tail.length * t =
          2 ^ (a : ℕ) * (2 ^ taoTupleWeight tail * M + taoOffsetNum tail) := by
        have hL : (3 : ℕ) ^ (tail.length + 1) * N = 3 ^ tail.length * (3 * N) := by
          rw [pow_succ]; ring
        rw [hL, ht] at hcleared
        have hR : (2 : ℕ) ^ ((a : ℕ) + taoTupleWeight tail) * M =
            2 ^ (a : ℕ) * (2 ^ taoTupleWeight tail * M) := by rw [pow_add]; ring
        rw [hR] at hcleared
        have hLL : (3 : ℕ) ^ tail.length * (t + 1) = 3 ^ tail.length * t + 3 ^ tail.length := by
          ring
        rw [hLL] at hcleared
        have hRR : (2 : ℕ) ^ (a : ℕ) * (2 ^ taoTupleWeight tail * M + taoOffsetNum tail) =
            2 ^ (a : ℕ) * (2 ^ taoTupleWeight tail * M) + 2 ^ (a : ℕ) * taoOffsetNum tail := by
          ring
        rw [hRR]
        omega
      have hcoprime : Nat.Coprime (2 ^ (a : ℕ)) (3 ^ tail.length) :=
        Nat.Coprime.pow (a : ℕ) tail.length (by decide : Nat.Coprime 2 3)
      have hdvd_prod : 2 ^ (a : ℕ) ∣ 3 ^ tail.length * t := ⟨_, hexp⟩
      have hdvd : 2 ^ (a : ℕ) ∣ t := hcoprime.dvd_of_dvd_mul_left hdvd_prod
      obtain ⟨N₁, hN₁⟩ := hdvd
      have htailCleared :
          3 ^ tail.length * N₁ = 2 ^ taoTupleWeight tail * M + taoOffsetNum tail := by
        have hmul : 2 ^ (a : ℕ) * (3 ^ tail.length * N₁) =
            2 ^ (a : ℕ) * (2 ^ taoTupleWeight tail * M + taoOffsetNum tail) := by
          rw [← hexp, hN₁]; ring
        exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) (a : ℕ)) hmul
      have htailAff : taoAffListM tail (N₁ : ℚ) = (M : ℚ) :=
        (taoAffListM_eq_nat_iff_cleared tail N₁ M).2 htailCleared
      obtain ⟨hN₁odd, htailValues, htailIterate⟩ := ih N₁ htailAff
      have hNodd : Odd N := by
        obtain ⟨r, hr⟩ : ∃ r, (a : ℕ) = r + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt a.2)
        have hteven : t = 2 * (2 ^ r * N₁) := by rw [hN₁, hr, pow_succ]; ring
        rw [Nat.odd_iff]
        omega
      have hfactorization : 2 ^ (a : ℕ) * N₁ = 2 ^ syrMExponent N * syrM N := by
        have h := two_pow_syrMExponent_mul_syrM_add_one hNpos
        omega
      obtain ⟨ha, hnext⟩ :=
        two_pow_mul_odd_cancel hN₁odd (syrM_odd hNpos) hfactorization
      have hhead : (⟨syrMExponent N, syrMExponent_pos_of_odd hNodd⟩ : ℕ+) = a :=
        Subtype.ext ha.symm
      have htailValues' :
          syrMValuationPNatList tail.length (syrM N) (syrM_odd hNpos) = tail := by
        simpa [hnext] using htailValues
      refine ⟨hNodd, ?_, ?_⟩
      · simp [hlen, syrMValuationPNatList, hhead, htailValues']
      · simpa [hlen, Function.iterate_succ_apply, hnext] using htailIterate

end

end ThreeXMinusOne
