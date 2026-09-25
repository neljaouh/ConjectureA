import ThreeXMinusOne.RootPath

/-!
# The descent word's offset is bounded

`next_wordAtom_mul_sixteenPow_le_one`, `forwardWordOffset_le_rootUniform` and
`forwardWord_weighted_source_band`, mirrored.

**This is the one place where the sign genuinely weakens an estimate**, and it is worth being
precise about where the slack comes from.

For `+1` the affine identity is `atom·N + offset = M`, so `atom·N ≤ M` outright, and since
`N ≥ 16^(b/100)·M` one gets `atom·16^(b/100) ≤ 1` exactly.  For `3x−1` it is
`atom·N − offset = M`, so `atom·N = M + offset` and the same step gives only
`atom·16^(b/100) ≤ 1 + offset/M`.  With `offset ≤ 2^b` and `M ≥ 16^b` that excess is at most
`2^(-3b)`, so `≤ 2` is true with enormous room — but it is not `≤ 1`, and the `+1` proof of the
offset bound consumes its constant exactly.

The recursion survives anyway, because the `+1` proof is lossy elsewhere: it bounds
`2^(b'+1) ≤ 2^b·16^(b/100)`, discarding a factor `2^(3·b/100 - 1)`.  Keeping that factor, the
step reads `offset ≤ 2^b + κ·2^(b+1)/2^(3·b/100)` and closes for any `κ ≤ 32`, where `+1` needs
`κ ≤ 1`.  So the same constant `2^(b+1)` holds for both maps; what the sign costs is slack that
was there all along.

The band does flip: `+1` has `root(anc) − 2^(b+1) ≤ atom·root ≤ root(anc)`, and `3x−1` has
`root(anc) ≤ atom·root ≤ root(anc) + 2^(b+1)`.  Same width, other side.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

/-- `+1` gets `≤ 1`; the minus offset adds rather than subtracts, so this is `≤ 2`. -/
theorem nextFloorM_wordAtom_mul_sixteenPow_le_two
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (K : ℕ)
    (z : (nextFloorM U K).state.Label) :
    ndRootUniformWordAtom (ucWordM z) * (16 : ℝ) ^ (U.floor / 100) ≤ 2 := by
  have ha := forwardWordM_affine U (fun _ => K) 1 z
  have ha' : ndRootUniformWordAtom (ucWordM z) * (((nextFloorM U K).state.root z : ℕ) : ℝ) -
      ndRootUniformWordOffset (ucWordM z) =
      ((U.state.root (ucLabelM z) : ℕ) : ℝ) := by
    simpa [forwardWordM, forwardAncestorM, forwardFirstIncidenceM] using ha
  have hg : (16 : ℝ) ^ (U.floor / 100) * ((U.state.root (ucLabelM z) : ℕ) : ℝ) ≤
      (((nextFloorM U K).state.root z : ℕ) : ℝ) := by
    exact_mod_cast nextFloorM_root_ge_sixteenPow_mul_parent U K z
  have hlen : (ucWordM z).length ≤ ndGeom2ShiftedWideSymmetricHorizon U.floor := by
    rw [ucWordM_length]
    exact (Finset.mem_Icc.mp z.2.1.2).2
  have hF := rootUniformWordOffset_le_twoPow_of_length_le_horizon hlen
  have hW : (0 : ℝ) ≤ ndRootUniformWordAtom (ucWordM z) := (rootUniformWordAtom_pos _).le
  have hMnat : 16 ^ U.floor ≤ U.state.root (ucLabelM z) :=
    (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base _)).trans (U.state.rootLower _)
  have hM : (16 : ℝ) ^ U.floor ≤ ((U.state.root (ucLabelM z) : ℕ) : ℝ) := by
    exact_mod_cast hMnat
  have htwo : (2 : ℝ) ^ U.floor ≤ (16 : ℝ) ^ U.floor :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hMpos : (0 : ℝ) < ((U.state.root (ucLabelM z) : ℕ) : ℝ) := by
    have := (U.state.root_odd (ucLabelM z)).pos
    exact_mod_cast this
  have hmul := mul_le_mul_of_nonneg_left hg hW
  apply (mul_le_mul_iff_left₀ hMpos).mp
  nlinarith only [hmul, ha', hF, hM, htwo, hMpos]

/-- **The accumulated offset stays below `2 ^ (floor + 1)`** — the same constant as `+1`. -/
theorem forwardWordOffsetM_le_rootUniform
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    (z : (forwardIterateM U cap n).state.Label) :
    ndRootUniformWordOffset (forwardWordM U cap n z) ≤ (2 : ℝ) ^ (U.floor + 1) := by
  induction n generalizing U cap with
  | zero => simp [forwardWordM, ndRootUniformWordOffset, Tao.taoOffsetList]
  | succ n ih =>
      set iz := forwardFirstIncidenceM U cap n z with hiz
      set w := ucWordM iz with hw
      have hd : 1 ≤ U.floor / 100 := by have := U.floor_twoHundred; omega
      have hd2 : 2 ≤ U.floor / 100 := by have := U.floor_twoHundred; omega
      have hlen : w.length ≤ ndGeom2ShiftedWideSymmetricHorizon U.floor := by
        rw [hw, ucWordM_length]
        exact (Finset.mem_Icc.mp iz.2.1.2).2
      have hF := rootUniformWordOffset_le_twoPow_of_length_le_horizon hlen
      have hW := nextFloorM_wordAtom_mul_sixteenPow_le_two U (cap 0) iz
      have htail := ih (U := nextFloorM U (cap 0)) (cap := ndGeom2RootSideCapTail cap) z
      have hA : (0 : ℝ) ≤ ndRootUniformWordAtom w := (rootUniformWordAtom_pos _).le
      set T := ndRootUniformWordOffset
        (forwardWordM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n z) with hT
      have hT0 : (0 : ℝ) ≤ T := rootUniformWordOffset_nonneg _
      have h16 : (0 : ℝ) < (16 : ℝ) ^ (U.floor / 100) := by positivity
      -- `atom w · T · 16 ^ d ≤ 2 · 2 ^ (b + d + 1)`
      have hkey : ndRootUniformWordAtom w * T * (16 : ℝ) ^ (U.floor / 100) ≤
          2 * (2 : ℝ) ^ ((nextFloorM U (cap 0)).floor + 1) := by
        have hprod : ndRootUniformWordAtom w * (16 : ℝ) ^ (U.floor / 100) * T ≤ 2 * T :=
          mul_le_mul_of_nonneg_right hW hT0
        have h2T : 2 * T ≤ 2 * (2 : ℝ) ^ ((nextFloorM U (cap 0)).floor + 1) := by
          linarith [htail]
        calc ndRootUniformWordAtom w * T * (16 : ℝ) ^ (U.floor / 100)
            = ndRootUniformWordAtom w * (16 : ℝ) ^ (U.floor / 100) * T := by ring
          _ ≤ 2 * T := hprod
          _ ≤ _ := h2T
      -- `2 · 2 ^ (b + d + 1) ≤ 2 ^ b · 16 ^ d`, because `2 ≤ 3d`
      have hcmp : 2 * (2 : ℝ) ^ ((nextFloorM U (cap 0)).floor + 1) ≤
          (2 : ℝ) ^ U.floor * (16 : ℝ) ^ (U.floor / 100) := by
        have hl : 2 * (2 : ℝ) ^ ((nextFloorM U (cap 0)).floor + 1) =
            (2 : ℝ) ^ (U.floor + U.floor / 100 + 2) := by
          change 2 * (2 : ℝ) ^ (U.floor + U.floor / 100 + 1) = _
          rw [← pow_succ']
        have hr : (2 : ℝ) ^ U.floor * (16 : ℝ) ^ (U.floor / 100) =
            (2 : ℝ) ^ (U.floor + 4 * (U.floor / 100)) := by
          rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add]
        rw [hl, hr]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have htame : ndRootUniformWordAtom w * T ≤ (2 : ℝ) ^ U.floor := by
        have h := hkey.trans hcmp
        exact le_of_mul_le_mul_right (by linarith [h]) h16
      rw [forwardWordM, rootUniformWordOffset_append]
      change ndRootUniformWordOffset w + ndRootUniformWordAtom w * T ≤ _
      have hpow : (2 : ℝ) ^ (U.floor + 1) = 2 * (2 : ℝ) ^ U.floor := by rw [pow_succ]; ring
      linarith [hF, htame, hpow]

/-- **The band, flipped.**  `+1` has `root(anc) − 2^(b+1) ≤ atom·root ≤ root(anc)`. -/
theorem forwardWordM_weighted_source_band
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    (z : (forwardIterateM U cap n).state.Label) :
    (U.state.root (forwardAncestorM U cap n z) : ℝ) ≤
        ndRootUniformWordAtom (forwardWordM U cap n z) *
          ((forwardIterateM U cap n).state.root z : ℝ) ∧
      ndRootUniformWordAtom (forwardWordM U cap n z) *
          ((forwardIterateM U cap n).state.root z : ℝ) ≤
        (U.state.root (forwardAncestorM U cap n z) : ℝ) + (2 : ℝ) ^ (U.floor + 1) := by
  have ha := forwardWordM_affine U cap n z
  have hF := forwardWordOffsetM_le_rootUniform U cap n z
  have hF0 := rootUniformWordOffset_nonneg (forwardWordM U cap n z)
  constructor <;> linarith only [ha, hF, hF0]

end

end ThreeXMinusOne
