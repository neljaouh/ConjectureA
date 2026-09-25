import ThreeXMinusOne.WordOffsetBound
import ThreeXMinusOne.TerminalCharge

/-!
# The descent atom against the floor

`forwardWordAtom_mul_sixteenPow_floor_le` and
`threePow_mul_forwardWordAtom_le_rootUniform_edge`, mirrored.

Layer 51's `≤ 2` was enough for the offset bound, which had slack to spare.  It is *not* enough
here: this bound is an induction whose per-generation factor multiplies, so a constant `2` would
give `2^n` and the capacity estimate would collapse.

The sharp form is the one to use, and it lands exactly on the constant Layer 35 already
introduced.  From `atom·N = M + offset`, `offset ≤ 2^b` and `M ≥ 16^b`,

    atom · 16^(b/100) ≤ 1 + 2^b/16^b = 1 + (1/8)^b ≤ 1 + 3·(9/16)^b = 1 + chargeExcessM b,

since `2^b ≤ 9^b`.  So the per-generation excess here is the *same* `chargeExcessM` as the charge
inequality, and the accumulated product is the *same* `generationExcessProductM`, bounded by
`1 + 4.6×10^(-50)` uniformly in `n` by Layer 37.  `+1` has this with the product replaced by `1`.

That is the third distinct place the same excess has appeared — the charge (Layer 37), the
terminal telescope, and now the capacity atom — and each time it is the same series, so the whole
`3x−1` argument pays for the sign once, not once per use.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

/-- The sharp per-generation atom bound.  `+1` has `≤ 1`. -/
theorem nextFloorM_wordAtom_mul_sixteenPow_le_sharp
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (K : ℕ)
    (z : (nextFloorM U K).state.Label) :
    ndRootUniformWordAtom (ucWordM z) * (16 : ℝ) ^ (U.floor / 100) ≤
      1 + chargeExcessM U.floor := by
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
  have hMpos : (0 : ℝ) < ((U.state.root (ucLabelM z) : ℕ) : ℝ) := by
    have := (U.state.root_odd (ucLabelM z)).pos
    exact_mod_cast this
  -- `2 ^ b ≤ chargeExcessM b * 16 ^ b`, because `2 ^ b ≤ 9 ^ b` and `chargeExcessM b = 3(9/16)^b`
  have hexc : (2 : ℝ) ^ U.floor ≤ chargeExcessM U.floor * (16 : ℝ) ^ U.floor := by
    unfold chargeExcessM
    have h29 : (2 : ℝ) ^ U.floor ≤ (9 : ℝ) ^ U.floor :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have hnine : (3 : ℝ) * (9 / 16 : ℝ) ^ U.floor * (16 : ℝ) ^ U.floor =
        3 * (9 : ℝ) ^ U.floor := by
      rw [div_pow]
      field_simp
    rw [hnine]
    linarith [h29, pow_pos (by norm_num : (0:ℝ) < 9) U.floor]
  have hmul := mul_le_mul_of_nonneg_left hg hW
  apply (mul_le_mul_iff_left₀ hMpos).mp
  nlinarith only [hmul, ha', hF, hM, hexc, hMpos, chargeExcessM_nonneg U.floor]

/-- **The atom against the floor**, with the accumulated excess.  `+1` has the product as `1`. -/
theorem forwardWordAtomM_mul_sixteenPow_floor_le
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    (z : (forwardIterateM U cap n).state.Label) :
    ndRootUniformWordAtom (forwardWordM U cap n z) *
        (16 : ℝ) ^ (forwardIterateM U cap n).floor ≤
      generationExcessProductM U cap n * (16 : ℝ) ^ U.floor := by
  induction n generalizing U cap with
  | zero => simp [forwardWordM, forwardIterateM, ndRootUniformWordAtom,
      generationExcessProductM]
  | succ n ih =>
      set w := ucWordM (forwardFirstIncidenceM U cap n z) with hw
      have ht := ih (U := nextFloorM U (cap 0)) (cap := ndGeom2RootSideCapTail cap) z
      have hA : (0 : ℝ) ≤ ndRootUniformWordAtom w := (rootUniformWordAtom_pos _).le
      have he := nextFloorM_wordAtom_mul_sixteenPow_le_sharp U (cap 0)
        (forwardFirstIncidenceM U cap n z)
      have hP := generationExcessProductM_nonneg (nextFloorM U (cap 0))
        (ndGeom2RootSideCapTail cap) n
      have hsixteen : (0 : ℝ) < (16 : ℝ) ^ U.floor := by positivity
      rw [forwardWordM, rootUniformWordAtom_append]
      have hp : (16 : ℝ) ^ (nextFloorM U (cap 0)).floor =
          (16 : ℝ) ^ U.floor * (16 : ℝ) ^ (U.floor / 100) := pow_add _ _ _
      rw [hp] at ht
      have hPb : (0 : ℝ) ≤ generationExcessProductM (nextFloorM U (cap 0))
          (ndGeom2RootSideCapTail cap) n * (16 : ℝ) ^ U.floor := mul_nonneg hP hsixteen.le
      show ndRootUniformWordAtom w *
        ndRootUniformWordAtom
          (forwardWordM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n z) *
        (16 : ℝ) ^ (forwardIterateM (nextFloorM U (cap 0))
          (ndGeom2RootSideCapTail cap) n).floor ≤
        generationExcessProductM U cap (n + 1) * (16 : ℝ) ^ U.floor
      calc ndRootUniformWordAtom w *
            ndRootUniformWordAtom
              (forwardWordM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n z) *
            (16 : ℝ) ^ (forwardIterateM (nextFloorM U (cap 0))
              (ndGeom2RootSideCapTail cap) n).floor
          = ndRootUniformWordAtom w *
              (ndRootUniformWordAtom
                (forwardWordM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n z) *
                (16 : ℝ) ^ (forwardIterateM (nextFloorM U (cap 0))
                  (ndGeom2RootSideCapTail cap) n).floor) := by ring
        _ ≤ ndRootUniformWordAtom w *
              (generationExcessProductM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n *
                ((16 : ℝ) ^ U.floor * (16 : ℝ) ^ (U.floor / 100))) :=
              mul_le_mul_of_nonneg_left ht hA
        _ = generationExcessProductM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n *
              (16 : ℝ) ^ U.floor *
              (ndRootUniformWordAtom w * (16 : ℝ) ^ (U.floor / 100)) := by ring
        _ ≤ generationExcessProductM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n *
              (16 : ℝ) ^ U.floor * (1 + chargeExcessM U.floor) :=
              mul_le_mul_of_nonneg_left he hPb
        _ = generationExcessProductM U cap (n + 1) * (16 : ℝ) ^ U.floor := by
              simp only [generationExcessProductM]; ring

/-- The edge form the capacity estimate consumes. -/
theorem threePow_mul_forwardWordAtomM_le_rootUniform_edge
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n q : ℕ)
    (hq : q ≤ 2 * (forwardIterateM U cap n).floor)
    (z : (forwardIterateM U cap n).state.Label) :
    (3 : ℝ) ^ q * ndRootUniformWordAtom (forwardWordM U cap n z) ≤
      generationExcessProductM U cap n * (16 : ℝ) ^ U.floor *
        (9 / 16 : ℝ) ^ (forwardIterateM U cap n).floor := by
  have hqR : (3 : ℝ) ^ q ≤ (9 : ℝ) ^ (forwardIterateM U cap n).floor := by
    calc (3 : ℝ) ^ q ≤ (3 : ℝ) ^ (2 * (forwardIterateM U cap n).floor) :=
          pow_le_pow_right₀ (by norm_num) hq
      _ = (9 : ℝ) ^ (forwardIterateM U cap n).floor := by rw [pow_mul]; norm_num
  have ht := forwardWordAtomM_mul_sixteenPow_floor_le U cap n z
  calc (3 : ℝ) ^ q * ndRootUniformWordAtom (forwardWordM U cap n z)
      ≤ (9 : ℝ) ^ (forwardIterateM U cap n).floor *
          ndRootUniformWordAtom (forwardWordM U cap n z) :=
        mul_le_mul_of_nonneg_right hqR (rootUniformWordAtom_pos _).le
    _ ≤ generationExcessProductM U cap n * (16 : ℝ) ^ U.floor *
          ((9 : ℝ) ^ (forwardIterateM U cap n).floor /
            (16 : ℝ) ^ (forwardIterateM U cap n).floor) := by
        rw [← mul_div_assoc]
        refine (le_div_iff₀ (by positivity :
          (0 : ℝ) < (16 : ℝ) ^ (forwardIterateM U cap n).floor)).2 ?_
        have h := mul_le_mul_of_nonneg_left ht
          (by positivity : (0 : ℝ) ≤ (9 : ℝ) ^ (forwardIterateM U cap n).floor)
        nlinarith only [h]
    _ = _ := by rw [div_pow]

end

end ThreeXMinusOne
