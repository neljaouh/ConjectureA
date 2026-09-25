import ThreeXMinusOne.Decode
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideUnitChildRate

/-!
# The ambient child of a `3x−1` affine relation

Rung one of the mass-identity tower: the minus twin of
`ndNatCast_eq_reversedPrefixAmbientChild_sourceDigit_of_affine`.

The statement carries the sign trap recorded in `UnitChild.lean`.  Writing
`ndReversedPrefixAmbientChild s w z = A·z + B` with `A = 3^s·(2^W)⁻¹` and `B` the head prefix —
the embed is *linear* in `z` — the `+1` cleared identity `3^s·N + C = 2^W·M` gives `M = A·N + B`,
whereas the `3x−1` identity `3^s·N = 2^W·M + C` gives `M = A·N − B`, hence

    −M = A·(−N) + B = ambientChild s w (−N).

So both the value and the digit are negated.

Rather than redo the `ZMod` algebra that identifies `A` and `B` with the artifact's
`taoSection6AmbientTailEmbed` and `taoSection7OffsetPrefix` — sixty lines, and the place where a
sign slip would be easiest to make and hardest to see — this **reuses the artifact's lemma by
substitution**.  Given the minus relation, set

    N' = 2^W·3V − N,     M' = 3^s·3V − M     (V large enough that both are natural)

Then `3^s·N' + C = 2^W·M'` is the `+1` relation, additively and with no truncated subtraction in
the derivation; and `3 ∣ 2^W·3V` while `3^(1+s) ∣ 3^s·3V`, so `N' ≡ −N (mod 3)` and
`M' ≡ −M (mod 3^(1+s))`.  Applying the artifact's lemma to `(N', M')` yields exactly the minus
statement.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

theorem natCastM_eq_ambientChild_negDigit_of_affineM
    {s N M : ℕ} {rootSide : List ℕ+}
    (hlen : rootSide.length = s)
    (hAff : taoAffListM rootSide.reverse (N : ℚ) = (M : ℚ)) :
    -(M : ZMod (3 ^ (1 + s))) =
      ndReversedPrefixAmbientChild s rootSide (-(N : ZMod (3 ^ 1))) := by
  classical
  have hrevlen : rootSide.reverse.length = s := by rw [List.length_reverse, hlen]
  set W := Tao.taoTupleWeight rootSide.reverse with hW
  set C := Tao.taoOffsetNum rootSide.reverse with hC
  have hcl := (taoAffListM_eq_nat_iff_cleared rootSide.reverse N M).mp hAff
  rw [hrevlen, ← hW, ← hC] at hcl
  -- the substitution
  set V : ℕ := N + M + 1 with hV
  have h2W : 1 ≤ 2 ^ W := Nat.one_le_pow _ _ (by norm_num)
  have h3s : 1 ≤ 3 ^ s := Nat.one_le_pow _ _ (by norm_num)
  have hNle : N ≤ 2 ^ W * (3 * V) := by
    have : 3 * V ≤ 2 ^ W * (3 * V) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hMle : M ≤ 3 ^ s * (3 * V) := by
    have : 3 * V ≤ 3 ^ s * (3 * V) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  set N' : ℕ := 2 ^ W * (3 * V) - N with hN'def
  set M' : ℕ := 3 ^ s * (3 * V) - M with hM'def
  have hN : N + N' = 2 ^ W * (3 * V) := by omega
  have hM : M + M' = 3 ^ s * (3 * V) := by omega
  -- the `+1` cleared identity for the substituted pair, derived additively
  have e1 : 3 ^ s * N + 3 ^ s * N' = 3 ^ s * (2 ^ W * (3 * V)) := by
    rw [← Nat.mul_add, hN]
  have e2 : 2 ^ W * M + 2 ^ W * M' = 2 ^ W * (3 ^ s * (3 * V)) := by
    rw [← Nat.mul_add, hM]
  have e3 : 3 ^ s * (2 ^ W * (3 * V)) = 2 ^ W * (3 ^ s * (3 * V)) := by ring
  have hcl' : 3 ^ s * N' + C = 2 ^ W * M' := by omega
  have hAff' : Tao.taoAffList rootSide.reverse (N' : ℚ) = (M' : ℚ) := by
    refine (Tao.taoAffList_eq_nat_iff_cleared rootSide.reverse N' M').2 ?_
    rw [hrevlen]
    exact hcl'
  have hplus := ndNatCast_eq_reversedPrefixAmbientChild_sourceDigit_of_affine hlen hAff'
  -- transport the two congruences
  have hdigit : ((N' : ℕ) : ZMod (3 ^ 1)) = -((N : ℕ) : ZMod (3 ^ 1)) := by
    have hsum : ((N : ℕ) : ZMod (3 ^ 1)) + ((N' : ℕ) : ZMod (3 ^ 1)) = 0 := by
      have hdvd : (3 ^ 1 : ℕ) ∣ 2 ^ W * (3 * V) := ⟨2 ^ W * V, by ring⟩
      have hmod : Nat.ModEq (3 ^ 1) (2 ^ W * (3 * V)) 0 := (Nat.modEq_zero_iff_dvd).mpr hdvd
      have hz : ((2 ^ W * (3 * V) : ℕ) : ZMod (3 ^ 1)) = 0 := by
        simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
      calc ((N : ℕ) : ZMod (3 ^ 1)) + ((N' : ℕ) : ZMod (3 ^ 1))
          = ((N + N' : ℕ) : ZMod (3 ^ 1)) := by push_cast; ring
        _ = ((2 ^ W * (3 * V) : ℕ) : ZMod (3 ^ 1)) := by rw [hN]
        _ = 0 := hz
    linear_combination hsum
  have hval : ((M' : ℕ) : ZMod (3 ^ (1 + s))) = -((M : ℕ) : ZMod (3 ^ (1 + s))) := by
    have hsum : ((M : ℕ) : ZMod (3 ^ (1 + s))) + ((M' : ℕ) : ZMod (3 ^ (1 + s))) = 0 := by
      have hdvd : (3 ^ (1 + s) : ℕ) ∣ 3 ^ s * (3 * V) := ⟨V, by rw [pow_add]; ring⟩
      have hmod : Nat.ModEq (3 ^ (1 + s)) (3 ^ s * (3 * V)) 0 := (Nat.modEq_zero_iff_dvd).mpr hdvd
      have hz : ((3 ^ s * (3 * V) : ℕ) : ZMod (3 ^ (1 + s))) = 0 := by
        simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
      calc ((M : ℕ) : ZMod (3 ^ (1 + s))) + ((M' : ℕ) : ZMod (3 ^ (1 + s)))
          = ((M + M' : ℕ) : ZMod (3 ^ (1 + s))) := by push_cast; ring
        _ = ((3 ^ s * (3 * V) : ℕ) : ZMod (3 ^ (1 + s))) := by rw [hM]
        _ = 0 := hz
    linear_combination hsum
  rw [hval, hdigit] at hplus
  exact hplus

end ThreeXMinusOne
