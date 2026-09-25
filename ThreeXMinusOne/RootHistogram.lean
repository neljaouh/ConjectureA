import ThreeXMinusOne.WordAtomBound

/-!
# The root histogram and its capacity bound

`forwardRootGroup`, `forwardRootGroupHistogram` and
`threePow_mul_forwardRootGroupHistogram_le_rootUniform`, mirrored.

Group the generation-`n` labels by (ancestor, descent length, descent weight).  Within one group
the word atom is a single number `W = 3^D / 2^A`, so Layer 50's weight factorisation makes every
label's outer weight the same, and Layer 51's band confines `W · root` to an interval of width
`2^(floor+1)`.  A set of naturals in one residue class mod `3^q` confined to such an interval has
at most `(width + 3^q) / 3^q` elements — that is
`rootUniform_sameResidue_weighted_card_le`, which is a statement about naturals and needs no
porting.

**The flipped band costs nothing here.**  `+1` has `root(anc) − 2^(b+1) ≤ W·root ≤ root(anc)` and
`3x−1` has `root(anc) ≤ W·root ≤ root(anc) + 2^(b+1)`; the diameter bound uses the upper end of
one and the lower end of the other, so it reads off identically either way.  What does change is
the edge form, which now carries Layer 52's accumulated excess in place of `+1`'s `1`.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

variable (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)

/-- Labels grouped by ancestor, descent length and descent weight. -/
def forwardRootGroupM (i : U.state.Label) (D A : ℕ) :
    Finset (forwardIterateM U cap n).state.Label := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  exact Finset.univ.filter fun z => forwardAncestorM U cap n z = i ∧
    (forwardWordM U cap n z).length = D ∧ Tao.taoTupleWeight (forwardWordM U cap n z) = A

/-- The weight of one group sitting in one residue class. -/
def forwardRootGroupHistogramM (i : U.state.Label) (D A q : ℕ) (y : ZMod (3 ^ q)) : ℝ := by
  classical
  exact ∑ z ∈ (forwardRootGroupM U cap n i D A).filter
    (fun z => (((forwardIterateM U cap n).state.root z : ℕ) : ZMod (3 ^ q)) = y),
      (forwardIterateM U cap n).state.outerWeight z

theorem threePow_mul_forwardRootGroupHistogramM_le_rootUniform
    (i : U.state.Label) (D A q : ℕ) (y : ZMod (3 ^ q)) :
    (3 : ℝ) ^ q * forwardRootGroupHistogramM U cap n i D A q y ≤
      U.state.outerWeight i * ((2 : ℝ) ^ (U.floor + 1) +
        (3 : ℝ) ^ q * ((3 : ℝ) ^ D / (2 : ℝ) ^ A)) := by
  classical
  set Z := (forwardRootGroupM U cap n i D A).filter
    (fun z => (((forwardIterateM U cap n).state.root z : ℕ) : ZMod (3 ^ q)) = y) with hZ
  set S := Z.image (forwardIterateM U cap n).state.root with hS
  set W : ℝ := (3 : ℝ) ^ D / (2 : ℝ) ^ A with hW
  have hmem : ∀ z ∈ Z, forwardAncestorM U cap n z = i ∧
      (forwardWordM U cap n z).length = D ∧
      Tao.taoTupleWeight (forwardWordM U cap n z) = A := by
    intro z hz
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
  have hword : ∀ z ∈ Z, ndRootUniformWordAtom (forwardWordM U cap n z) = W := by
    intro z hz
    simp only [ndRootUniformWordAtom, (hmem z hz).2.1, (hmem z hz).2.2, W]
  have hinj : (Z : Set (forwardIterateM U cap n).state.Label).InjOn
      (forwardIterateM U cap n).state.root := by
    intro z hz w hw hr
    exact forwardLabelM_eq_of_ancestor_root_depth_eq U cap n
      ((hmem z hz).1.trans (hmem w hw).1.symm) hr
      ((hmem z hz).2.1.trans (hmem w hw).2.1.symm)
  have hcard : S.card = Z.card := Finset.card_image_of_injOn hinj
  have hdiam : ∀ N ∈ S, ∀ M ∈ S, W * (N : ℝ) ≤ W * (M : ℝ) + (2 : ℝ) ^ (U.floor + 1) := by
    intro N hN M hM
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hN
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hM
    have hzB := forwardWordM_weighted_source_band U cap n z
    have hwB := forwardWordM_weighted_source_band U cap n w
    rw [(hmem z hz).1, hword z hz] at hzB
    rw [(hmem w hw).1, hword w hw] at hwB
    linarith only [hzB.2, hwB.1]
  have hres : ∀ N ∈ S, ((N : ℕ) : ZMod (3 ^ q)) = y := by
    intro N hN
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hN
    exact (Finset.mem_filter.mp hz).2
  have hc := rootUniform_sameResidue_weighted_card_le S (by positivity : 0 < 3 ^ q) y
    (by positivity : 0 ≤ W) (by positivity : 0 ≤ (2 : ℝ) ^ (U.floor + 1)) hres hdiam
  rw [hcard] at hc
  have hsum : forwardRootGroupHistogramM U cap n i D A q y =
      U.state.outerWeight i * W * Z.card := by
    change (∑ z ∈ Z, (forwardIterateM U cap n).state.outerWeight z) = _
    calc (∑ z ∈ Z, (forwardIterateM U cap n).state.outerWeight z)
        = ∑ _z ∈ Z, U.state.outerWeight i * W := by
          refine Finset.sum_congr rfl fun z hz => ?_
          rw [forwardWeightM_eq_ownerWeight_mul_wordAtom U cap n z, (hmem z hz).1, hword z hz]
      _ = U.state.outerWeight i * W * Z.card := by
          simp only [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hsum]
  have h := mul_le_mul_of_nonneg_left hc (U.state.weight_nonneg i)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, W, mul_assoc, mul_left_comm] using h

/-- The edge form.  `+1` has the excess product as `1`. -/
theorem threePow_mul_forwardRootGroupHistogramM_le_rootUniform_edge
    (i : U.state.Label) (D A q : ℕ) (hq : q ≤ 2 * (forwardIterateM U cap n).floor)
    (y : ZMod (3 ^ q)) :
    (3 : ℝ) ^ q * forwardRootGroupHistogramM U cap n i D A q y ≤
      U.state.outerWeight i * ((2 : ℝ) ^ (U.floor + 1) +
        generationExcessProductM U cap n * (16 : ℝ) ^ U.floor *
          (9 / 16 : ℝ) ^ (forwardIterateM U cap n).floor) := by
  classical
  by_cases hne : (forwardRootGroupM U cap n i D A).Nonempty
  · obtain ⟨z, hz⟩ := hne
    have hd := (Finset.mem_filter.mp hz).2
    have he := threePow_mul_forwardWordAtomM_le_rootUniform_edge U cap n q hq z
    simp only [ndRootUniformWordAtom, hd.2.1, hd.2.2] at he
    exact (threePow_mul_forwardRootGroupHistogramM_le_rootUniform U cap n i D A q y).trans
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) he) (U.state.weight_nonneg i))
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [forwardRootGroupHistogramM, hempty, Finset.filter_empty, Finset.sum_empty,
      mul_zero]
    refine mul_nonneg (U.state.weight_nonneg i) ?_
    have := generationExcessProductM_nonneg U cap n
    positivity

end

end ThreeXMinusOne
