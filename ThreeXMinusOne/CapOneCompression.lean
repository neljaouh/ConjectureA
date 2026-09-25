import ThreeXMinusOne.SourceFan
import ThreeXMinusOne.IncidenceCharge
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalCapOneCompression

/-!
# Compressing a `3x−1` terminal incidence to cap one

`exists_physical_terminal_cap_one_compression`, mirrored.

A cap-`K` incidence is a cap-one incidence with `2j` added back onto its head exponent.  The
word side of that is `ndTerminalEvenRaise`; the source side is the fan of Layer 40; and the atom
is scaled by `(1/4)^j`, since raising the head exponent by `2j` divides the geometric weight by
`4^j`.

**Most of the work is already done, in the artifact.**  `exists_first_crossing_cap_one_compression`
— the combinatorial heart, which finds the `j` and splits the word — mentions no root, no source
and no residue: it is a statement about `ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAt`,
which is word-only.  So is `ndTerminalEvenRaise` and its atom law.  Both are used here verbatim.

What is `3x−1`-specific is a single line: the rebuilt cap-one word has to sit in the minus
finset, which asks for `taoSection7OffsetZMod s word = −(root)` where `+1` asks for `+root`.
Layer 6's `taoAffineOffsetZModM` supplies exactly that, so the sign lives in one `linear_combination`
and nowhere else in this file.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

variable {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}

/-- **Cap-one compression for `3x−1`.** -/
theorem exists_physical_terminal_cap_one_compressionM
    (hrootOdd : ∀ i, Odd (root i)) (hbase : ∀ i, 9 ≤ base i)
    (hroot : ∀ i, 16 ^ base i ≤ root i)
    (z : IncidenceM Label root base shift K) :
    ∃ (z0 : IncidenceM Label root base shift 1) (j : Fin (K / 2 + 1)),
      labelM z = labelM z0 ∧ depthM z = depthM z0 ∧
      rootSideWordM z = ndTerminalEvenRaise j.val (rootSideWordM z0) ∧
      sourceM z = sourceFanM j.val (sourceM z0) ∧
      atomM z = (1 / 4 : ℝ) ^ j.val * atomM z0 := by
  classical
  rcases z with ⟨i, ⟨s, hs⟩, word, hword⟩
  set z : IncidenceM Label root base shift K := ⟨i, ⟨s, hs⟩, word, hword⟩ with hz
  obtain ⟨hlen, hevent, _⟩ :=
    mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff.mp hword
  obtain ⟨pre, v0, j, hj, hpre, hw, hevent0⟩ :=
    exists_first_crossing_cap_one_compression hlen hevent
  have haff := (sourceM_odd_and_affine hrootOdd z).2
  change taoAffListM word.reverse (sourceM z : ℚ) = (root i : ℚ) at haff
  rw [hw, List.reverse_append, List.reverse_singleton, List.singleton_append] at haff
  have hv : 2 * j < (ndPNatAddNat (2 * j) v0 : ℕ) := by
    change 2 * j < 2 * j + (v0 : ℕ)
    exact Nat.lt_add_of_pos_right v0.2
  obtain ⟨x0, hx0, hsource, haff0⟩ :=
    exists_head_compressed_sourceM (hrootOdd i) hv haff
  have hv0 : (⟨(ndPNatAddNat (2 * j) v0 : ℕ) - 2 * j, by omega⟩ : ℕ+) = v0 := by
    apply Subtype.ext
    simp [ndPNatAddNat_coe]
    rfl
  rw [hv0] at haff0
  have haff0' : taoAffListM (pre ++ [v0]).reverse (x0 : ℚ) = (root i : ℚ) := by
    simpa using haff0
  have hlen0 : (pre ++ [v0]).length = s := by simpa using hpre
  -- The one `3x−1`-specific line: the minus finset wants `−(root)`.
  have hoffset : Tao.taoSection7OffsetZMod s (pre ++ [v0]) = -(root i : ZMod (3 ^ s)) := by
    have h := taoAffineOffsetZModM_eq_of_taoAffListM_eq
      (N := ⟨x0, hx0⟩) (show (pre ++ [v0]).reverse.length = s by simpa using hlen0) haff0'
    unfold taoAffineOffsetZModM at h
    rw [Tao.taoAffineOffsetZMod_reverse_eq_taoSection7OffsetZMod hlen0] at h
    linear_combination h
  set z0 : IncidenceM Label root base shift 1 :=
    ⟨i, ⟨s, hs⟩, pre ++ [v0],
      mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff.mpr
        ⟨hlen0, hevent0, hoffset⟩⟩ with hz0
  have hsource0 : sourceM z0 = x0 :=
    taoAffineSourceCandidateM_eq_of_taoAffListM_eq
      (show (pre ++ [v0]).reverse.length = s by simpa using hlen0) haff0'
  refine ⟨z0, ⟨j, by omega⟩, rfl, rfl, ?_, ?_, ?_⟩
  · change word = ndTerminalEvenRaise j (pre ++ [v0])
    rw [terminalEvenRaise_append]
    exact hw
  · change sourceM z = _
    rw [hsource0]
    exact hsource
  · change (3 : ℝ) ^ s * (Tao.geom2PNatListPMF s word).toReal =
      (1 / 4 : ℝ) ^ j * ((3 : ℝ) ^ s * (Tao.geom2PNatListPMF s (pre ++ [v0])).toReal)
    rw [hw, ← terminalEvenRaise_append, ← hlen0, terminalEvenRaise_atom]
    ring

end

end ThreeXMinusOne
