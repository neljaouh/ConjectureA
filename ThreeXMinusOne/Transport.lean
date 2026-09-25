import ThreeXMinusOne.SelectedWord
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricReferenceMarkedPhysicalIncidence

/-!
# Transport evaluation for `3x−1`

Rung five: `referencePrefixTransportAt_apply_physical_source` and
`referencePrefixTransportAt_apply_unitIncidence`.

Both are proved by the substitution of rung one, at a larger modulus.  The artifact's lemma is
universally quantified over naturals `(N, M)` satisfying the `+1` affine relation; given the
minus relation, the pair

    N' = 2^W·3V − N,   M' = 3^L·3V − M      with  V = 3^(q+k)·(N+M+1)

satisfies it, and `3^(q+k+1)` divides both `2^W·3V` and `3^L·3V`, so `N' ≡ −N (mod 3^k)` and
`M' ≡ −M (mod 3^q)` simultaneously.  Feeding `(N', M')` to the artifact's lemma therefore
evaluates the transport at `−(root)` and returns `g` at `−(source)` — the same "everything
negated" pattern the digit obeys.

That `g` is applied at `−(source)` rather than `source` costs nothing downstream: the only
hypothesis the kernel places on `g` is that it vanishes off the units of `ZMod 3`, and `−y` is a
unit exactly when `y` is.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

theorem transportAtM_apply_physical_source
    {N M : ℕ} (q k : ℕ) (word : List ℕ+)
    (hlen : word.length ≤ q) (hk : k ≤ q - word.length)
    (hAff : taoAffListM word.reverse (N : ℚ) = (M : ℚ))
    (g : ZMod (3 ^ k) → ℝ) :
    ndReferencePrefixTransportAt q word hlen
        (fun z => g (Tao.taoZModThreeProjection hk z)) (-((M : ℕ) : ZMod (3 ^ q))) =
      (3 : ℝ) ^ word.length * (Tao.geom2PNatListPMF word.length word).toReal *
        g (-((N : ℕ) : ZMod (3 ^ k))) := by
  classical
  set L := word.reverse.length with hL
  set W := Tao.taoTupleWeight word.reverse with hW
  set C := Tao.taoOffsetNum word.reverse with hC
  have hcl := (taoAffListM_eq_nat_iff_cleared word.reverse N M).mp hAff
  rw [← hL, ← hW, ← hC] at hcl
  set V : ℕ := 3 ^ (q + k) * (N + M + 1) with hV
  have h2W : 1 ≤ 2 ^ W := Nat.one_le_pow _ _ (by norm_num)
  have h3L : 1 ≤ 3 ^ L := Nat.one_le_pow _ _ (by norm_num)
  have hVbig : N + M + 1 ≤ V := by
    have : 1 ≤ 3 ^ (q + k) := Nat.one_le_pow _ _ (by norm_num)
    calc N + M + 1 = 1 * (N + M + 1) := by ring
      _ ≤ 3 ^ (q + k) * (N + M + 1) := Nat.mul_le_mul_right _ this
  have hNle : N ≤ 2 ^ W * (3 * V) := by
    have h1 : 3 * V ≤ 2 ^ W * (3 * V) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hMle : M ≤ 3 ^ L * (3 * V) := by
    have h1 : 3 * V ≤ 3 ^ L * (3 * V) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  set N' : ℕ := 2 ^ W * (3 * V) - N with hN'def
  set M' : ℕ := 3 ^ L * (3 * V) - M with hM'def
  have hN : N + N' = 2 ^ W * (3 * V) := by omega
  have hM : M + M' = 3 ^ L * (3 * V) := by omega
  have e1 : 3 ^ L * N + 3 ^ L * N' = 3 ^ L * (2 ^ W * (3 * V)) := by rw [← Nat.mul_add, hN]
  have e2 : 2 ^ W * M + 2 ^ W * M' = 2 ^ W * (3 ^ L * (3 * V)) := by rw [← Nat.mul_add, hM]
  have e3 : 3 ^ L * (2 ^ W * (3 * V)) = 2 ^ W * (3 ^ L * (3 * V)) := by ring
  have hcl' : 3 ^ L * N' + C = 2 ^ W * M' := by omega
  have hAff' : Tao.taoAffList word.reverse (N' : ℚ) = (M' : ℚ) :=
    (Tao.taoAffList_eq_nat_iff_cleared word.reverse N' M').2 hcl'
  -- the two congruences, at their own moduli
  have hdvdN : (3 ^ k : ℕ) ∣ N + N' := by
    rw [hN, hV]
    exact ⟨2 ^ W * (3 * 3 ^ q * (N + M + 1)), by rw [pow_add]; ring⟩
  have hdvdM : (3 ^ q : ℕ) ∣ M + M' := by
    rw [hM, hV]
    exact ⟨3 ^ L * (3 * 3 ^ k * (N + M + 1)), by rw [pow_add]; ring⟩
  have hNzm : ((N' : ℕ) : ZMod (3 ^ k)) = -((N : ℕ) : ZMod (3 ^ k)) := by
    have hz : ((N + N' : ℕ) : ZMod (3 ^ k)) = 0 := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr
        ((Nat.modEq_zero_iff_dvd).mpr hdvdN)
    push_cast at hz
    linear_combination hz
  have hMzm : ((M' : ℕ) : ZMod (3 ^ q)) = -((M : ℕ) : ZMod (3 ^ q)) := by
    have hz : ((M + M' : ℕ) : ZMod (3 ^ q)) = 0 := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr
        ((Nat.modEq_zero_iff_dvd).mpr hdvdM)
    push_cast at hz
    linear_combination hz
  have hplus := referencePrefixTransportAt_apply_physical_source
    (N := N') (M := M') q k word hlen hk hAff' g
  rw [hMzm, hNzm] at hplus
  exact hplus

end ThreeXMinusOne
