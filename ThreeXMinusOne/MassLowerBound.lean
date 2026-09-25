import ThreeXMinusOne.TwoConductor
import ThreeXMinusOne.TerminalWindow
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricExplicitConductor

/-!
# The good mass is bounded below

`terminal_conductor_room_of_pos_mark` and
`fullGoodCoreTerminalMass_ge_of_square_budget_and_height_of_nonreturningSeed`, mirrored.

This closes the analytic half.  Layer 61 bounds the good mass *above* by
`(8/9)·p·(terminal mass) + (mixing error)`; a lower bound `a` on the good mass, together with a
budget that keeps the mixing error below `a/2`, then forces the terminal mass above
`9a/(16p)` — the same conclusion as `+1`, with the same constants.

Two supporting facts.  The conductor has room (`3^k < X`) whenever the mass is positive, because
a terminal source is at least `16^floor` and at most `64X`.  And the budget condition is the
`+1` one with `88` doubled to `176`, matching the doubled additive constant in Layer 61.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

private theorem power_roomM {b : ℕ} (hb : 200 ≤ b) :
    4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b * 16 ^ (b / 100) ≤ 4 ^ b := by
  have h :=
    four_mul_twoPowShiftRadius_mul_threePow_mul_sixteenPow_base_add_oneHundredth_le_sixtyFourPow hb
  have h' : 16 ^ b * (4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b *
      16 ^ (b / 100)) ≤ 16 ^ b * 4 ^ b := by
    calc 16 ^ b * (4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b * 16 ^ (b / 100))
        = 4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b * 16 ^ (b + b / 100) := by
          rw [pow_add]; ring
      _ ≤ 64 ^ b := h
      _ = 16 ^ b * 4 ^ b := by rw [← mul_pow]; norm_num
  exact Nat.le_of_mul_le_mul_left h' (by positivity)

/-- The minus analogue of `ndGeom2RootSideCommonFloorShifted_sourceLower`. -/
theorem sourceM_lower {Label : Type*} {root rootBase shift : Label → ℕ} {b K : ℕ}
    (hodd : ∀ i, Odd (root i)) (hb : 200 ≤ b) (hfloor : ∀ i, b ≤ rootBase i)
    (hlower : ∀ i, 16 ^ rootBase i ≤ root i)
    (z : IncidenceM Label root (fun _ => b) shift K) :
    16 ^ (rootBase (labelM z) + b / 100) ≤ sourceM z := by
  have hpacket : ∀ j, 16 ^ b ≤ root j := fun j =>
    (Nat.pow_le_pow_right (by norm_num) (hfloor j)).trans (hlower j)
  have hshell := sourceM_shell hodd (fun _ => by omega) hpacket z
  have hscale : 4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b *
      16 ^ (rootBase (labelM z) + b / 100) ≤ 4 ^ b * 16 ^ (rootBase (labelM z)) := by
    calc 4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b *
          16 ^ (rootBase (labelM z) + b / 100)
        = 16 ^ (rootBase (labelM z)) *
            (4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b * 16 ^ (b / 100)) := by
          rw [pow_add]; ring
      _ ≤ 16 ^ (rootBase (labelM z)) * 4 ^ b := Nat.mul_le_mul_left _ (power_roomM hb)
      _ = _ := by ring
  have hnum : 4 ^ b * 16 ^ (rootBase (labelM z)) ≤
      2 ^ shift (labelM z) * 4 ^ b * root (labelM z) := by
    calc 4 ^ b * 16 ^ (rootBase (labelM z)) ≤ 4 ^ b * root (labelM z) :=
          Nat.mul_le_mul_left _ (hlower _)
      _ ≤ 2 ^ shift (labelM z) * (4 ^ b * root (labelM z)) := by
          simpa using Nat.mul_le_mul_right (4 ^ b * root (labelM z))
            (Nat.one_le_two_pow (n := shift (labelM z)))
      _ = _ := by ring
  have hcross : 4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b *
      16 ^ (rootBase (labelM z) + b / 100) ≤
      4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b * sourceM z :=
    hscale.trans (hnum.trans hshell.1)
  exact Nat.le_of_mul_le_mul_left hcross (by positivity)

/-- **The conductor has room** whenever the terminal mass is positive. -/
theorem terminal_conductor_roomM_of_pos_mark
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ)
    (n K k : ℕ) (hk : k ≤ (forwardIterateM U cap n).floor) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i))
    (hT : 0 < forwardCoreTerminalUnitMassM U cap width n K k X hX hi) :
    ((3 ^ k : ℕ) : ℝ) < X := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  have hfan := forwardCoreTerminalUnitMassM_le_cap_one_fan U cap width n K k X hX hi
  obtain ⟨z⟩ : Nonempty (FullTerminalIncidenceM (forwardIterateM U cap n) X hX hi) := by
    by_contra h
    haveI : IsEmpty (FullTerminalIncidenceM (forwardIterateM U cap n) X hX hi) :=
      not_nonempty_iff.mp h
    have hz : forwardCoreTerminalUnitMassM U cap width n K k X hX hi ≤ 0 := by
      refine hfan.trans (le_of_eq ?_)
      unfold coreTerminalFanBoundM
      simp
    linarith
  have hb := (forwardIterateM U cap n).floor_twoHundred
  have hwin := fullTerminalM_source_window (forwardIterateM U cap n) X hX hi z
  have hlower : 16 ^ (forwardIterateM U cap n).floor ≤ sourceM z :=
    (Nat.pow_le_pow_right (by norm_num) (show (forwardIterateM U cap n).floor ≤
      (forwardIterateM U cap n).state.base (labelM z) + (forwardIterateM U cap n).floor / 100 by
        have := (forwardIterateM U cap n).floor_le_base (labelM z); omega)).trans
      (sourceM_lower (forwardIterateM U cap n).state.root_odd hb
        (forwardIterateM U cap n).floor_le_base (forwardIterateM U cap n).state.rootLower z)
  have h64 : 64 ≤ 2 ^ (forwardIterateM U cap n).floor := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
      (show 6 ≤ (forwardIterateM U cap n).floor by omega)
    simpa using h
  have hpower : 64 * 3 ^ k ≤ 16 ^ (forwardIterateM U cap n).floor := by
    calc 64 * 3 ^ k ≤ 2 ^ (forwardIterateM U cap n).floor *
          3 ^ (forwardIterateM U cap n).floor :=
          Nat.mul_le_mul h64 (Nat.pow_le_pow_right (by norm_num) hk)
      _ = 6 ^ (forwardIterateM U cap n).floor := by rw [← mul_pow]; norm_num
      _ ≤ _ := Nat.pow_le_pow_left (by norm_num) _
  have hnat := hpower.trans hlower
  have hreal : (64 : ℝ) * ((3 ^ k : ℕ) : ℝ) ≤ (sourceM z : ℝ) := by exact_mod_cast hnat
  linarith [hwin.2]

/-- The budget condition, with `+1`'s `88` doubled. -/
theorem conductorM_error_le_half {P Cmix a : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hsquare : 176 * P * Cmix ≤ a * (m : ℝ) ^ 2) :
    88 * P * (Cmix / (m : ℝ) ^ 2) ≤ a / 2 := by
  have hmPos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ 2)).2
  linarith only [hsquare]

/-- **The terminal mass is bounded below.**  Same conclusion and constants as `+1`. -/
theorem fullGoodCoreTerminalMassM_ge_of_square_budget_and_height
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ)
    (n K m k : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k) (hk : k ≤ (forwardIterateM U cap n).floor)
    (hseed : ∀ i k, 0 < k → (syrM^[k]) (U.state.root i) ≠ U.state.root i)
    {Cmix a : ℝ} (hCmix : 0 ≤ Cmix)
    (hmix : ndTernaryUniformMean k (fun y => |ndSyracuseUnitReferenceDensity k y -
      ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|) ≤
      Cmix / (m : ℝ) ^ 2)
    (ha : 0 < a)
    (hsquare : 176 * (generationExcessProductM U cap (n + 1) * U.parentSourcePotential) * Cmix ≤
      a * (m : ℝ) ^ 2)
    (p : ℕ) (hp : 0 < p)
    (hheight : ∀ y, ndSyracuseUnitReferenceDensity m y ≤ (2 / 3 : ℝ) * (p : ℝ))
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (forwardIterateM U cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (forwardIterateM U cap n).floor
        ((forwardIterateM U cap n).state.root i))
    (hmark : a ≤ forwardCoreTerminalGoodDepthShiftUnitMassM U cap width n K k X hX hi) :
    9 * a / (16 * (p : ℝ)) ≤ fullGoodCoreTerminalMassM U cap width n
      ((forwardIterateM U cap n).fullTerminalShift X hX hi) 1 := by
  have hOrig := (ha.trans_le hmark).trans_le
    (forwardCoreTerminalGoodDepthShiftUnitMassM_le_original U cap width n K k X hX hi)
  have hQ := terminal_conductor_roomM_of_pos_mark U cap width n K k hk X hX hi hOrig
  have hbound := forwardGoodDepthShiftUnitMassM_le_two_conductor_of_height U cap width n K m k hmk
    hseed X hX hQ.le hi (Cmix / (m : ℝ) ^ 2) (div_nonneg hCmix (by positivity)) hmix p hp hheight
  have herror := conductorM_error_le_half hm hsquare
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (p : ℝ))).2
  nlinarith only [hmark, hbound, herror]

end

end ThreeXMinusOne
