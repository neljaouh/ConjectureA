import ThreeXMinusOne.TerminalInjectivity
import ThreeXMinusOne.TerminalPath
import ThreeXMinusOne.SourceTariff
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootUniformGroupedCapacity

/-!
# The descent path, and the word-affine identity

`forwardRootPath`, `forwardWord_affine`, `forwardWeight_eq_ownerWeight_mul_wordAtom` and
`next_root_ge_sixteenPow_mul_parent`, mirrored.

The capacity argument needs to see a whole `n`-generation descent as a single affine step: the
generation-`n` root is carried to the generation-zero root by the concatenated word, and the
generation-`n` outer weight is the ancestor's weight times that word's atom.  Those two facts are
what let a weighted sum over labels be regrouped by root value.

`ndRootUniformWordAtom` and `ndRootUniformWordOffset` are word-only — `3^len / 2^weight` and the
offset of the reversed word — so both are the artifact's own, used verbatim.  **The atom is
literally the same function for both maps**; only the identity relating it to the roots changes
sign, from `atom·N + offset = M` to `atom·N − offset = M`, because `3x−1` subtracts where `3x+1`
adds.  That single sign is the whole difference in this file, and it is confined to
`rootUniformWordM_affine_of_path`.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

/-- **The affine identity along a `3x−1` path.**  `+1` has `+ offset`. -/
theorem rootUniformWordM_affine_of_path {N M : ℕ} (p : SyrMPath N M) :
    ndRootUniformWordAtom p.word.reverse * (N : ℝ) -
      ndRootUniformWordOffset p.word.reverse = (M : ℝ) := by
  have ha := syrM_iterate_eq_taoAffListM p.depth N p.sourceOdd
  rw [p.valuation_eq, p.terminal_eq, taoAffListM_closed] at ha
  have hr := congrArg (fun x : ℚ => (x : ℝ)) ha.symm
  simpa only [ndRootUniformWordAtom, ndRootUniformWordOffset, List.reverse_reverse,
    List.length_reverse, Tao.taoTupleWeight_reverse, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast] using hr

theorem ucAtomM_eq_rootUniformWordAtom {Label : Type*} {Labels : Finset Label}
    {root : Label → ℕ} {b a K : ℕ} (z : UnitChildIncidenceM Labels root b a K) :
    ucAtomM z = ndRootUniformWordAtom (ucWordM z) := by
  unfold ucAtomM ndRootUniformWordAtom
  rw [← ucWordM_length z, Tao.geom2PNatListPMF_apply_length_toReal_eq_weight,
    Tao.one_div_two_pow_eq_inv_pow]
  simp only [div_eq_mul_inv, one_mul]

private theorem packetLowerM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) :
    ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
  (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans (U.state.rootLower i)

/-- The `3x−1` orbit path from a generation-`n` root up to its generation-zero ancestor. -/
noncomputable def forwardRootPathM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) : (n : ℕ) → (z : (forwardIterateM U cap n).state.Label) →
    SyrMPath ((forwardIterateM U cap n).state.root z)
      (U.state.root (forwardAncestorM U cap n z))
  | 0, z => SyrMPath.nil _ (U.state.root_odd z)
  | n + 1, z =>
      (forwardRootPathM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n z).appendIncidenceM
        U.state.root_odd (toPhysicalM (forwardFirstIncidenceM U cap n z))

theorem forwardRootPathM_word_eq_reverse
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    (z : (forwardIterateM U cap n).state.Label) :
    (forwardRootPathM U cap n z).word = (forwardWordM U cap n z).reverse := by
  induction n generalizing U cap with
  | zero => rfl
  | succ n ih =>
      change (forwardRootPathM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n z).word ++
          chronologicalWordM (toPhysicalM (forwardFirstIncidenceM U cap n z)) = _
      rw [ih]
      simp only [forwardWordM, chronologicalWordM, toPhysicalM_word, List.reverse_append]

/-- **The descent is one affine step.** -/
theorem forwardWordM_affine (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (z : (forwardIterateM U cap n).state.Label) :
    ndRootUniformWordAtom (forwardWordM U cap n z) *
        ((forwardIterateM U cap n).state.root z : ℝ) -
      ndRootUniformWordOffset (forwardWordM U cap n z) =
        (U.state.root (forwardAncestorM U cap n z) : ℝ) := by
  have h := rootUniformWordM_affine_of_path (forwardRootPathM U cap n z)
  simpa only [forwardRootPathM_word_eq_reverse, List.reverse_reverse] using h

/-- **The weight factorises along the descent.**  No sign: atoms multiply. -/
theorem forwardWeightM_eq_ownerWeight_mul_wordAtom
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    (z : (forwardIterateM U cap n).state.Label) :
    (forwardIterateM U cap n).state.outerWeight z =
      U.state.outerWeight (forwardAncestorM U cap n z) *
        ndRootUniformWordAtom (forwardWordM U cap n z) := by
  induction n generalizing U cap with
  | zero => simp [forwardIterateM, forwardAncestorM, forwardWordM, ndRootUniformWordAtom]
  | succ n ih =>
      rw [forwardWordM, rootUniformWordAtom_append]
      have h := ih (U := nextFloorM U (cap 0)) (cap := ndGeom2RootSideCapTail cap) z
      change _ = (U.state.outerWeight (forwardAncestorM U cap (n + 1) z) *
        ucAtomM (forwardFirstIncidenceM U cap n z)) * _ at h
      rw [ucAtomM_eq_rootUniformWordAtom] at h
      exact h.trans (by ring)

/-- **A child root is at least `16^(b/100)` times its parent.** -/
theorem nextFloorM_root_ge_sixteenPow_mul_parent
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (K : ℕ)
    (z : (nextFloorM U K).state.Label) :
    16 ^ (U.floor / 100) * U.state.root (ucLabelM z) ≤ (nextFloorM U K).state.root z := by
  have hs := sourceM_shell U.state.root_odd
    (fun _ => by have := U.floor_twoHundred; omega) (packetLowerM U) (toPhysicalM z)
  have hl : 4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius U.floor * 3 ^ U.floor *
      (16 ^ (U.floor / 100) * U.state.root (ucLabelM z)) ≤
      2 ^ ndGeom2ShiftedWideSymmetricShiftRadius U.floor * 4 ^ U.floor *
        U.state.root (ucLabelM z) := by
    calc 4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius U.floor * 3 ^ U.floor *
          (16 ^ (U.floor / 100) * U.state.root (ucLabelM z))
        = 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius U.floor *
            U.state.root (ucLabelM z) * (4 * 3 ^ U.floor * 16 ^ (U.floor / 100)) := by ring
      _ ≤ 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius U.floor *
            U.state.root (ucLabelM z) * 4 ^ U.floor := by
          gcongr
          exact four_mul_threePow_mul_sixteenPow_oneHundredth_le_fourPow U.floor_twoHundred
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left (hl.trans hs.1) (by positivity)

/-- Labels are determined by ancestor, root and descent length. -/
theorem forwardLabelM_eq_of_ancestor_root_depth_eq
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    {z w : (forwardIterateM U cap n).state.Label}
    (ha : forwardAncestorM U cap n z = forwardAncestorM U cap n w)
    (hr : (forwardIterateM U cap n).state.root z = (forwardIterateM U cap n).state.root w)
    (hd : (forwardWordM U cap n z).length = (forwardWordM U cap n w).length) : z = w := by
  set p := forwardRootPathM U cap n z with hpdef
  set q := forwardRootPathM U cap n w with hqdef
  have hdepth : p.depth = q.depth := by
    rw [← p.word_length, ← q.word_length]
    simpa only [hpdef, hqdef, forwardRootPathM_word_eq_reverse, List.length_reverse] using hd
  have hw := SyrMPath.word_eq_of_source_depth_eq p q hr hdepth
  have hword : forwardWordM U cap n z = forwardWordM U cap n w := by
    apply List.reverse_injective
    exact (forwardRootPathM_word_eq_reverse U cap n z).symm.trans
      (hw.trans (forwardRootPathM_word_eq_reverse U cap n w))
  exact (forwardLabelM_tail_eq_of_append U cap n z w [] [] ha (by simpa using hword)).1

end

end ThreeXMinusOne
