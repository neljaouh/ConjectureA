import ThreeXMinusOne.Decode
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricFirstCrossingPhysicalShell

/-!
# The physical shell bounds for `3x−1`

The minus twin of `shiftedWideSymmetric_affineSource_crossBounds_of_boundedOvershoot`, which is
what puts an incidence's source into a bounded window around its root — the input
`Assembly.count_ge_of_incidence_family` still needs.

The `+1` proof turns on exactly two arithmetic consequences of the cleared identity
`3^s·N + C = 2^W·M`:

    2^W·M ≤ 2·(3^s·N)    and    3^s·N ≤ 2^W·M.

For `3x−1` the identity is `3^s·N = 2^W·M + C`, and with the offset envelope `C ≤ 2^W·3^s`
against the room bound `2·3^s < M` these become

    2^W·M ≤ 3^s·N        (strictly *better* than the `+1` fact)
    3^s·N ≤ 2·(2^W·M)    (weaker by one factor of two).

Everything else — the first-crossing and bounded-overshoot hypotheses, `ndBalancedTotal` and its
two envelopes, the `four_pow` identities — is word-only and is reused from the artifact verbatim.
The upshot is the `+1` conclusion with the upper constant `2·2^K` relaxed to `4·2^K`: the source
window widens from `32X` to `64X`, and nothing else moves.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

/-- The artifact's helper of the same name is `private`, so it is reproved here. -/
private theorem four_pow_eq_two_pow_two_mul (b : ℕ) : (4 : ℕ) ^ b = 2 ^ (2 * b) := by
  rw [pow_mul]; norm_num

/-- **The `3x−1` shell bounds.** -/
theorem crossBoundsM_of_boundedOvershoot
    {b a s K N M : ℕ} {word : List ℕ+}
    (hlen : word.length = s)
    (hhit : ndGeom2ShiftedWideSymmetricHit b a s word)
    (hover : ndGeom2ShiftedWideSymmetricBoundedOvershoot b a s K word)
    (hroom : 2 * 3 ^ s < M)
    (hAff : taoAffListM word (N : ℚ) = (M : ℚ)) :
    2 ^ a * 4 ^ b * M ≤ 4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b * N ∧
      2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b * N ≤
        4 * 2 ^ K * 2 ^ a * 4 ^ b * M := by
  set W := Tao.taoTupleWeight word with hW
  set R := ndGeom2ShiftedWideSymmetricShiftRadius b with hR
  set C := Tao.taoOffsetNum word with hC
  have htake : word.take s = word := by rw [← hlen]; exact List.take_length
  have hhitNat :
      2 * b + ndBalancedTotal (s - b) + a ≤ W + ndBalancedTotal (b - s) + R := by
    unfold ndGeom2ShiftedWideSymmetricHit at hhit
    rw [htake] at hhit
    simpa only [W, R] using hhit
  have hoverNat :
      W + ndBalancedTotal (b - s) + R ≤ 2 * b + ndBalancedTotal (s - b) + a + K := by
    simpa only [ndGeom2ShiftedWideSymmetricBoundedOvershoot, W, R] using hover
  have hclearNat := (taoAffListM_eq_nat_iff_cleared word N M).mp hAff
  have hclear : 3 ^ s * N = 2 ^ W * M + C := by
    simpa only [hlen, W, C] using hclearNat
  have hoffset : C ≤ 2 ^ W * 3 ^ s := by
    simpa only [hlen, W, C] using
      Tao.taoOffsetNum_le_two_pow_weight_mul_three_pow_length word
  have hpowTwoPos : 0 < 2 ^ W := by positivity
  have hscaledRoom : 2 * (2 ^ W * 3 ^ s) < 2 ^ W * M := by
    calc 2 * (2 ^ W * 3 ^ s) = 2 ^ W * (2 * 3 ^ s) := by ring
      _ < 2 ^ W * M := (Nat.mul_lt_mul_left hpowTwoPos).2 hroom
  -- the two arithmetic facts, with `A`, `B`, `D` opaque to `omega`
  have hterminalLeDoubleSource : 2 ^ W * M ≤ 2 * (3 ^ s * N) := by omega
  have hsourceLeTerminal : 3 ^ s * N ≤ 2 * (2 ^ W * M) := by omega
  by_cases hbs : b ≤ s
  · let j := s - b
    have hsSplit : s = b + j := by dsimp only [j]; omega
    have hhitRight : 2 * b + ndBalancedTotal j + a ≤ W + R := by
      simpa only [j, Nat.sub_eq_zero_of_le hbs, ndBalancedTotal_zero, Nat.add_zero] using hhitNat
    have hoverRight : W + R ≤ 2 * b + ndBalancedTotal j + a + K := by
      simpa only [j, Nat.sub_eq_zero_of_le hbs, ndBalancedTotal_zero, Nat.add_zero] using hoverNat
    have hexpLower : 2 ^ (2 * b + ndBalancedTotal j + a) ≤ 2 ^ (W + R) :=
      Nat.pow_le_pow_right (by norm_num) hhitRight
    have hexpUpper : 2 ^ (W + R) ≤ 2 ^ (2 * b + ndBalancedTotal j + a + K) :=
      Nat.pow_le_pow_right (by norm_num) hoverRight
    have hbalancedLower : 3 ^ j ≤ 2 ^ ndBalancedTotal j := three_pow_le_two_pow_ndBalancedTotal j
    have hbalancedUpper : 2 ^ ndBalancedTotal j ≤ 2 * 3 ^ j :=
      two_pow_ndBalancedTotal_le_two_mul_three_pow j
    have hlowerTimes : (2 ^ a * 4 ^ b * M) * 3 ^ j ≤ (2 * 2 ^ R * 3 ^ b * N) * 3 ^ j := by
      calc (2 ^ a * 4 ^ b * M) * 3 ^ j = (2 ^ a * 4 ^ b * 3 ^ j) * M := by ring
        _ ≤ (2 ^ a * 4 ^ b * 2 ^ ndBalancedTotal j) * M :=
            Nat.mul_le_mul_right M (Nat.mul_le_mul_left (2 ^ a * 4 ^ b) hbalancedLower)
        _ = 2 ^ (2 * b + ndBalancedTotal j + a) * M := by
            rw [four_pow_eq_two_pow_two_mul, pow_add, pow_add]; ring
        _ ≤ 2 ^ (W + R) * M := Nat.mul_le_mul_right M hexpLower
        _ = 2 ^ R * (2 ^ W * M) := by rw [pow_add]; ring
        _ ≤ 2 ^ R * (2 * (3 ^ s * N)) := Nat.mul_le_mul_left (2 ^ R) hterminalLeDoubleSource
        _ = (2 * 2 ^ R * 3 ^ b * N) * 3 ^ j := by rw [hsSplit, pow_add]; ring
    have hlowerSharp : 2 ^ a * 4 ^ b * M ≤ 2 * 2 ^ R * 3 ^ b * N :=
      Nat.le_of_mul_le_mul_right hlowerTimes (by positivity)
    have hlower : 2 ^ a * 4 ^ b * M ≤ 4 * 2 ^ R * 3 ^ b * N := by
      calc 2 ^ a * 4 ^ b * M ≤ 2 * 2 ^ R * 3 ^ b * N := hlowerSharp
        _ ≤ 4 * 2 ^ R * 3 ^ b * N := by
            have h : 2 * (2 ^ R * 3 ^ b * N) ≤ 4 * (2 ^ R * 3 ^ b * N) :=
              Nat.mul_le_mul_right (2 ^ R * 3 ^ b * N) (by norm_num)
            simpa only [mul_assoc] using h
    have hupperTimes :
        (2 ^ R * 3 ^ b * N) * 3 ^ j ≤ (4 * 2 ^ K * 2 ^ a * 4 ^ b * M) * 3 ^ j := by
      calc (2 ^ R * 3 ^ b * N) * 3 ^ j = 2 ^ R * (3 ^ s * N) := by rw [hsSplit, pow_add]; ring
        _ ≤ 2 ^ R * (2 * (2 ^ W * M)) := Nat.mul_le_mul_left (2 ^ R) hsourceLeTerminal
        _ = 2 * (2 ^ (W + R) * M) := by rw [pow_add]; ring
        _ ≤ 2 * (2 ^ (2 * b + ndBalancedTotal j + a + K) * M) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right M hexpUpper)
        _ = (2 * 2 ^ K * 2 ^ a * 4 ^ b * 2 ^ ndBalancedTotal j) * M := by
            rw [four_pow_eq_two_pow_two_mul, pow_add, pow_add, pow_add]; ring
        _ ≤ (2 * 2 ^ K * 2 ^ a * 4 ^ b * (2 * 3 ^ j)) * M :=
            Nat.mul_le_mul_right M
              (Nat.mul_le_mul_left (2 * 2 ^ K * 2 ^ a * 4 ^ b) hbalancedUpper)
        _ = (4 * 2 ^ K * 2 ^ a * 4 ^ b * M) * 3 ^ j := by ring
    exact ⟨hlower, Nat.le_of_mul_le_mul_right hupperTimes (by positivity)⟩
  · have hsb : s ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hbs)
    let j := b - s
    have hsSplit : b = s + j := by dsimp only [j]; omega
    have hhitLeft : 2 * b + a ≤ W + ndBalancedTotal j + R := by
      simpa only [j, Nat.sub_eq_zero_of_le hsb, ndBalancedTotal_zero, Nat.zero_add] using hhitNat
    have hoverLeft : W + ndBalancedTotal j + R ≤ 2 * b + a + K := by
      simpa only [j, Nat.sub_eq_zero_of_le hsb, ndBalancedTotal_zero, Nat.zero_add] using hoverNat
    have hexpLower : 2 ^ (2 * b + a) ≤ 2 ^ (W + ndBalancedTotal j + R) :=
      Nat.pow_le_pow_right (by norm_num) hhitLeft
    have hexpUpper : 2 ^ (W + ndBalancedTotal j + R) ≤ 2 ^ (2 * b + a + K) :=
      Nat.pow_le_pow_right (by norm_num) hoverLeft
    have hbalancedLower : 3 ^ j ≤ 2 ^ ndBalancedTotal j := three_pow_le_two_pow_ndBalancedTotal j
    have hbalancedUpper : 2 ^ ndBalancedTotal j ≤ 2 * 3 ^ j :=
      two_pow_ndBalancedTotal_le_two_mul_three_pow j
    have hlower : 2 ^ a * 4 ^ b * M ≤ 4 * 2 ^ R * 3 ^ b * N := by
      calc 2 ^ a * 4 ^ b * M = 2 ^ (2 * b + a) * M := by
            rw [four_pow_eq_two_pow_two_mul, pow_add]; ring
        _ ≤ 2 ^ (W + ndBalancedTotal j + R) * M := Nat.mul_le_mul_right M hexpLower
        _ = 2 ^ R * 2 ^ W * 2 ^ ndBalancedTotal j * M := by rw [pow_add, pow_add]; ring
        _ ≤ 2 ^ R * 2 ^ W * (2 * 3 ^ j) * M :=
            Nat.mul_le_mul_right M (Nat.mul_le_mul_left (2 ^ R * 2 ^ W) hbalancedUpper)
        _ = 2 * 2 ^ R * 3 ^ j * (2 ^ W * M) := by ring
        _ ≤ 2 * 2 ^ R * 3 ^ j * (2 * (3 ^ s * N)) :=
            Nat.mul_le_mul_left (2 * 2 ^ R * 3 ^ j) hterminalLeDoubleSource
        _ = 4 * 2 ^ R * 3 ^ b * N := by rw [hsSplit, pow_add]; ring
    have hupperSharp : 2 ^ R * 3 ^ b * N ≤ 2 * (2 ^ K * 2 ^ a * 4 ^ b * M) := by
      calc 2 ^ R * 3 ^ b * N = 2 ^ R * 3 ^ j * (3 ^ s * N) := by rw [hsSplit, pow_add]; ring
        _ ≤ 2 ^ R * 3 ^ j * (2 * (2 ^ W * M)) :=
            Nat.mul_le_mul_left (2 ^ R * 3 ^ j) hsourceLeTerminal
        _ ≤ 2 ^ R * 2 ^ ndBalancedTotal j * (2 * (2 ^ W * M)) :=
            Nat.mul_le_mul_right (2 * (2 ^ W * M))
              (Nat.mul_le_mul_left (2 ^ R) hbalancedLower)
        _ = 2 * (2 ^ (W + ndBalancedTotal j + R) * M) := by rw [pow_add, pow_add]; ring
        _ ≤ 2 * (2 ^ (2 * b + a + K) * M) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right M hexpUpper)
        _ = 2 * (2 ^ K * 2 ^ a * 4 ^ b * M) := by
            rw [four_pow_eq_two_pow_two_mul, pow_add, pow_add]; ring
    have hupper : 2 ^ R * 3 ^ b * N ≤ 4 * 2 ^ K * 2 ^ a * 4 ^ b * M := by
      calc 2 ^ R * 3 ^ b * N ≤ 2 * (2 ^ K * 2 ^ a * 4 ^ b * M) := hupperSharp
        _ ≤ 4 * 2 ^ K * 2 ^ a * 4 ^ b * M := by
            have h : 2 * (2 ^ K * 2 ^ a * 4 ^ b * M) ≤ 4 * (2 ^ K * 2 ^ a * 4 ^ b * M) :=
              Nat.mul_le_mul_right (2 ^ K * 2 ^ a * 4 ^ b * M) (by norm_num)
            simpa only [mul_assoc] using h
    exact ⟨hlower, hupper⟩

end ThreeXMinusOne
