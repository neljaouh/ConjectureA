import ThreeXMinusOne.ShellIncidence
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideUniformFloorPhysical

/-!
# Floor growth for `3x−1`

The three lemmas of `Geom2ShiftedWideSymmetricRootSideUniformFloorPhysical` that make a child
state's floor exceed its parent's, mirrored for `3x−1`.

They matter twice over.  They are what `nextM` will need for its `base_twoHundred` field, and
they are the hypothesis of `Generations.generation_product_le`: the floor gaining at least
`b/100 ≥ 2` per generation is exactly what makes the `3x−1` excess a geometric series and so
bounds the generation product uniformly in `n`.

The mirror is exact, with **no constant changes**, because these lemmas use only the *lower*
shell bound — and that is the half the sign reversal improves rather than degrades
(`2^W·M ≤ 3^s·N` for `3x−1` against `2^W·M ≤ 2·(3^s·N)` for `3x+1`), so
`ShellIncidence.sourceM_shell` states it with the same constant `4` as the `+1` version.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

/-- The minus incidence with a uniform floor. -/
abbrev UniformFloorIncidenceM (Label : Type*) (root : Label → ℕ) (b K : ℕ) :=
  IncidenceM Label root (fun _ => b)
    (fun _ => ndGeom2ShiftedWideSymmetricShiftRadius b) K

variable {Label : Type*} {root rootBase : Label → ℕ} {b K : ℕ}

theorem sixteenPow_actualBase_add_oneHundredth_le_sourceM
    (hrootOdd : ∀ i, Odd (root i)) (hb : 200 ≤ b)
    (hfloor : ∀ i, b ≤ rootBase i) (hrootLower : ∀ i, 16 ^ rootBase i ≤ root i)
    (z : UniformFloorIncidenceM Label root b K) :
    16 ^ (rootBase (labelM z) + b / 100) ≤ sourceM z := by
  let i := labelM z
  let q := rootBase i
  let r := ndGeom2ShiftedWideSymmetricShiftRadius b
  let M := root i
  have hpacketRootLower : ∀ j, 16 ^ b ≤ root j := fun j =>
    (Nat.pow_le_pow_right (by norm_num) (hfloor j)).trans (hrootLower j)
  have hshell := sourceM_shell hrootOdd (fun _ => by omega) hpacketRootLower z
  have hscale : 4 * 2 ^ r * 3 ^ b * 16 ^ (q + b / 100) ≤ 2 ^ r * 4 ^ b * 16 ^ q := by
    calc 4 * 2 ^ r * 3 ^ b * 16 ^ (q + b / 100)
        = 2 ^ r * 16 ^ q * (4 * 3 ^ b * 16 ^ (b / 100)) := by rw [pow_add]; ring
      _ ≤ 2 ^ r * 16 ^ q * 4 ^ b := by
          gcongr
          exact four_mul_threePow_mul_sixteenPow_oneHundredth_le_fourPow hb
      _ = 2 ^ r * 4 ^ b * 16 ^ q := by ring
  have hnumLower : 2 ^ r * 4 ^ b * 16 ^ q ≤ 2 ^ r * 4 ^ b * M := by
    gcongr
    exact hrootLower i
  have hcross : 4 * 2 ^ r * 3 ^ b * 16 ^ (q + b / 100) ≤ 4 * 2 ^ r * 3 ^ b * sourceM z :=
    hscale.trans (hnumLower.trans (by simpa only [i, q, r, M] using hshell.1))
  have hdenPos : 0 < 4 * 2 ^ r * 3 ^ b := by positivity
  have hcancel := Nat.le_of_mul_le_mul_left hcross hdenPos
  simpa only [i, q] using hcancel

theorem actualBase_add_oneHundredth_le_sourceMBase
    (hrootOdd : ∀ i, Odd (root i)) (hb : 200 ≤ b)
    (hfloor : ∀ i, b ≤ rootBase i) (hrootLower : ∀ i, 16 ^ rootBase i ≤ root i)
    (z : UniformFloorIncidenceM Label root b K) :
    rootBase (labelM z) + b / 100 ≤ ndA5QOneRootDyadicBase (sourceM z) := by
  let q := rootBase (labelM z)
  have hsource :=
    sixteenPow_actualBase_add_oneHundredth_le_sourceM hrootOdd hb hfloor hrootLower z
  have hpow : 2 ^ (4 * (q + b / 100)) ≤ sourceM z := by
    calc 2 ^ (4 * (q + b / 100)) = 16 ^ (q + b / 100) := by
          rw [show (16 : ℕ) = 2 ^ 4 by norm_num, pow_mul]
      _ ≤ sourceM z := by simpa only [q] using hsource
  have hlog : 4 * (q + b / 100) ≤ Nat.log 2 (sourceM z) :=
    Nat.le_log_of_pow_le (by norm_num) hpow
  unfold ndA5QOneRootDyadicBase
  dsimp only [q] at hlog ⊢
  omega

/-- **The floor gains at least `b/100` per generation.**  This is the hypothesis
`Generations.generation_product_le` consumes. -/
theorem floor_add_oneHundredth_le_sourceMBase
    (hrootOdd : ∀ i, Odd (root i)) (hb : 200 ≤ b)
    (hfloor : ∀ i, b ≤ rootBase i) (hrootLower : ∀ i, 16 ^ rootBase i ≤ root i)
    (z : UniformFloorIncidenceM Label root b K) :
    b + b / 100 ≤ ndA5QOneRootDyadicBase (sourceM z) :=
  (Nat.add_le_add_right (hfloor (labelM z)) (b / 100)).trans
    (actualBase_add_oneHundredth_le_sourceMBase hrootOdd hb hfloor hrootLower z)

end ThreeXMinusOne
