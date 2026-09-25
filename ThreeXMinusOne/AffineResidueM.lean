import ThreeXMinusOne.Decode
import Erdos1135.Tao.Syracuse.AffineResidue

/-!
# The ternary residue condition for `3x−1`

Layer 6 of the port: `Tao/Syracuse/AffineResidue.lean`.

This is the layer that decides *which* reverse words are admissible above a given root, and it is
the parameter through which the artifact's word finsets are indexed.  The finset

    ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset b a s K x

already takes the residue `x` as an argument; the `3x+1` development instantiates it at
`x := (root : ZMod (3^s))`.  The content of this file is that the `3x−1` condition is the *same*
finset at the *negated* residue:

    taoAffineOffsetZModM q as = - taoAffineOffsetZMod q as.

So the word-counting machinery — which is stated for general `x` — transfers without change, and
only the instantiation moves.

A second, smaller gain: on the `+1` side `taoAffineSourceCandidate` is
`(2^W·M − OffNum)/3^q`, a truncated subtraction, and the `hroom : 2·3^q < M` hypothesis exists to
keep it honest.  Here the candidate is `(2^W·M + OffNum)/3^q` and that hypothesis is **not
needed**; `taoAffineOffsetZModM_eq_iff_existsUnique_oddNat` below drops it.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.Tao
open scoped ZMod

noncomputable section

/-- The `3x−1` admissible residue: the negative of the `3x+1` one. -/
def taoAffineOffsetZModM (q : ℕ) (as : List ℕ+) : ZMod (3 ^ q) :=
  -(taoAffineOffsetZMod q as)

/-- The `3x−1` source candidate.  Free of truncated subtraction. -/
def taoAffineSourceCandidateM (q : ℕ) (as : List ℕ+) (M : ℕ) : ℕ :=
  (2 ^ taoTupleWeight as * M + taoOffsetNum as) / 3 ^ q

private theorem two_pow_isUnit (q S : ℕ) : IsUnit ((2 : ZMod (3 ^ q)) ^ S) := by
  refine IsUnit.pow S ?_
  simpa using
    (ZMod.unitOfCoprime 2 (Nat.Coprime.pow_right q (by decide : Nat.Coprime 2 3))).isUnit

theorem taoAffineOffsetZModM_eq_iff_cleared (q : ℕ) (as : List ℕ+) (M : ℕ) :
    (M : ZMod (3 ^ q)) = taoAffineOffsetZModM q as ↔
      (((2 ^ taoTupleWeight as * M : ℕ) : ZMod (3 ^ q))) =
        -(taoOffsetNum as : ZMod (3 ^ q)) := by
  let a : ZMod (3 ^ q) := (2 : ZMod (3 ^ q)) ^ taoTupleWeight as
  have ha : IsUnit a := two_pow_isUnit q (taoTupleWeight as)
  have hainv : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a ha
  have hainv' : a⁻¹ * a = 1 := ZMod.inv_mul_of_unit a ha
  rw [taoAffineOffsetZModM, taoAffineOffsetZMod]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  change (M : ZMod (3 ^ q)) = -((taoOffsetNum as : ZMod (3 ^ q)) * a⁻¹) ↔
    a * (M : ZMod (3 ^ q)) = -(taoOffsetNum as : ZMod (3 ^ q))
  constructor
  · intro h
    rw [h]
    calc a * -((taoOffsetNum as : ZMod (3 ^ q)) * a⁻¹)
        = -((taoOffsetNum as : ZMod (3 ^ q)) * (a * a⁻¹)) := by ring
      _ = -(taoOffsetNum as : ZMod (3 ^ q)) := by rw [hainv, mul_one]
  · intro h
    calc (M : ZMod (3 ^ q)) = 1 * (M : ZMod (3 ^ q)) := by rw [one_mul]
      _ = (a⁻¹ * a) * (M : ZMod (3 ^ q)) := by rw [hainv']
      _ = a⁻¹ * (a * (M : ZMod (3 ^ q))) := by ring
      _ = a⁻¹ * -(taoOffsetNum as : ZMod (3 ^ q)) := by rw [h]
      _ = -((taoOffsetNum as : ZMod (3 ^ q)) * a⁻¹) := by ring

theorem taoAffineSourceCandidateM_eq_of_taoAffListM_eq
    {q : ℕ} {as : List ℕ+} (hlen : as.length = q) {N M : ℕ}
    (hAff : taoAffListM as (N : ℚ) = (M : ℚ)) :
    taoAffineSourceCandidateM q as M = N := by
  have hclear := (taoAffListM_eq_nat_iff_cleared as N M).mp hAff
  simp only [taoAffineSourceCandidateM]
  rw [← hclear]
  simp [hlen]

theorem taoAffListM_oddNat_injective (as : List ℕ+) (M : ℕ) {N N' : TaoOddNat}
    (hN : taoAffListM as (N.1 : ℚ) = (M : ℚ))
    (hN' : taoAffListM as (N'.1 : ℚ) = (M : ℚ)) :
    N = N' := by
  have hclear := (taoAffListM_eq_nat_iff_cleared as N.1 M).mp hN
  have hclear' := (taoAffListM_eq_nat_iff_cleared as N'.1 M).mp hN'
  have hmul : 3 ^ as.length * N.1 = 3 ^ as.length * N'.1 := by omega
  exact Subtype.ext (Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) as.length) hmul)

theorem taoAffineOffsetZModM_eq_of_taoAffListM_eq
    {q : ℕ} {as : List ℕ+} (hlen : as.length = q) {N : TaoOddNat} {M : ℕ}
    (hAff : taoAffListM as (N.1 : ℚ) = (M : ℚ)) :
    (M : ZMod (3 ^ q)) = taoAffineOffsetZModM q as := by
  have hclear := (taoAffListM_eq_nat_iff_cleared as N.1 M).mp hAff
  apply (taoAffineOffsetZModM_eq_iff_cleared q as M).2
  have hcast : ((3 ^ as.length * N.1 : ℕ) : ZMod (3 ^ q)) =
      ((2 ^ taoTupleWeight as * M + taoOffsetNum as : ℕ) : ZMod (3 ^ q)) :=
    congrArg (fun x : ℕ => (x : ZMod (3 ^ q))) hclear
  rw [hlen, Nat.cast_mul, ZMod.natCast_self, zero_mul, Nat.cast_add] at hcast
  linear_combination -hcast

/-- **The existence-uniqueness step, without the `+1` side's room hypothesis.** -/
theorem taoAffineOffsetZModM_eq_iff_existsUnique_oddNat
    {q : ℕ} {as : List ℕ+} (hlen : as.length = q) {M : ℕ} (hM : Odd M) :
    (M : ZMod (3 ^ q)) = taoAffineOffsetZModM q as ↔
      ∃! N : TaoOddNat, taoAffListM as (N.1 : ℚ) = (M : ℚ) := by
  constructor
  · intro hcompat
    have hclearedZ := (taoAffineOffsetZModM_eq_iff_cleared q as M).mp hcompat
    have hzero :
        ((2 ^ taoTupleWeight as * M + taoOffsetNum as : ℕ) : ZMod (3 ^ q)) =
          ((0 : ℕ) : ZMod (3 ^ q)) := by
      rw [Nat.cast_add, Nat.cast_zero, hclearedZ]
      ring
    have hmod : Nat.ModEq (3 ^ q) (2 ^ taoTupleWeight as * M + taoOffsetNum as) 0 :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hzero
    have hdvd : 3 ^ q ∣ 2 ^ taoTupleWeight as * M + taoOffsetNum as :=
      (Nat.modEq_zero_iff_dvd).mp hmod
    set N := (2 ^ taoTupleWeight as * M + taoOffsetNum as) / 3 ^ q with hNdef
    have hclearAff :
        3 ^ as.length * N = 2 ^ taoTupleWeight as * M + taoOffsetNum as := by
      rw [hlen, hNdef]
      exact Nat.mul_div_cancel' hdvd
    have hAff : taoAffListM as (N : ℚ) = (M : ℚ) :=
      (taoAffListM_eq_nat_iff_cleared as N M).2 hclearAff
    obtain ⟨hNodd, _hvalues, _hiterate⟩ := taoAffListM_oddNat_decode as N M hM hAff
    refine ⟨⟨N, hNodd⟩, hAff, ?_⟩
    intro N' hN'
    exact taoAffListM_oddNat_injective as M hN' hAff
  · rintro ⟨N, hAff, _hunique⟩
    exact taoAffineOffsetZModM_eq_of_taoAffListM_eq hlen hAff

theorem existsUnique_taoAffListM_eq_of_affineOffsetZModM
    {q : ℕ} {as : List ℕ+} (hlen : as.length = q) {M : ℕ} (hM : Odd M)
    (hcompat : (M : ZMod (3 ^ q)) = taoAffineOffsetZModM q as) :
    ∃! N : TaoOddNat, taoAffListM as (N.1 : ℚ) = (M : ℚ) :=
  (taoAffineOffsetZModM_eq_iff_existsUnique_oddNat hlen hM).mp hcompat

end

end ThreeXMinusOne
