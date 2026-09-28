import ThreeXMinusOne.Incidence
import ThreeXMinusOne.Charge

/-!
# The incidence-level charge inequality for `3x−1`

Layer 8: the analogue of
`ndGeom2PredictableRootSideBoundedOvershootIncidence_source_mul_atom_le_root`, which is what the
terminal-aggregation layer of M2 actually consumes.

The atom is `3^depth · P(word)`, a function of the word alone, so its definition carries over
unchanged.  Identifying it with the `3x−1` prefix likelihood is Layer 7's `sourceM_valuation`;
bounding the product is Layer 3.  The result is the `+1` inequality with the single factor
`1 + δ` that Layers 2–3 showed to be the whole price of the sign reversal.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.Tao Erdos1135.ND.PositiveDensity

noncomputable section

variable {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}

/-- The incidence atom.  Word-only, so identical in form to the `3x+1` one. -/
def atomM (z : IncidenceM Label root base shift K) : ℝ :=
  (3 : ℝ) ^ depthM z * ((Tao.geom2PNatListPMF (depthM z)) (rootSideWordM z)).toReal

theorem atomM_nonneg (z : IncidenceM Label root base shift K) : 0 ≤ atomM z := by
  unfold atomM
  exact mul_nonneg (by positivity) ENNReal.toReal_nonneg

theorem atomM_eq_prefixLikelihoodM (hrootOdd : ∀ i, Odd (root i))
    (z : IncidenceM Label root base shift K) :
    atomM z = prefixLikelihoodM (sourceM z) (sourceM_odd hrootOdd z) (depthM z) := by
  have hpmf := Tao.geom2PNatListPMF_apply_length_toReal (chronologicalWordM z)
  rw [chronologicalWordM_length z] at hpmf
  unfold atomM prefixLikelihoodM prefixGeomMassM
  rw [sourceM_valuation hrootOdd z, ← hpmf]
  unfold chronologicalWordM
  rw [Tao.geom2PNatListPMF_apply_reverse]
  ring

/-- **The `3x−1` incidence charge inequality.**  Compare
`…IncidenceSource_mul_atom_le_root`: same statement, one factor `1 + δ`. -/
theorem sourceM_mul_atomM_le_root (hrootOdd : ∀ i, Odd (root i))
    (z : IncidenceM Label root base shift K) {R δ : ℝ}
    (hR : 1 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hfloor : ∀ j, j < depthM z → R ≤ (((syrM^[j]) (sourceM z) : ℕ) : ℝ))
    (hsmall : 2 * (depthM z : ℝ) ≤ δ * (3 * R - 1)) :
    (sourceM z : ℝ) * atomM z ≤ (1 + δ) * (root (labelM z) : ℝ) := by
  have hsourceOdd : Odd (sourceM z) := sourceM_odd hrootOdd z
  have hsourcePos : (0 : ℝ) < (sourceM z : ℝ) := by exact_mod_cast hsourceOdd.pos
  have hiter : (syrM^[depthM z]) (sourceM z) = root (labelM z) := sourceM_iterate hrootOdd z
  have hlike := prefixLikelihoodM_le_terminal_div_source
    (sourceM z) hsourceOdd (depthM z) hR hδ hδ1 hfloor hsmall
  rw [hiter] at hlike
  rw [atomM_eq_prefixLikelihoodM hrootOdd z]
  calc (sourceM z : ℝ) * prefixLikelihoodM (sourceM z) hsourceOdd (depthM z)
      = prefixLikelihoodM (sourceM z) hsourceOdd (depthM z) * (sourceM z : ℝ) := by ring
    _ ≤ ((1 + δ) * ((root (labelM z) : ℝ) / (sourceM z : ℝ))) * (sourceM z : ℝ) :=
        mul_le_mul_of_nonneg_right hlike hsourcePos.le
    _ = (1 + δ) * (root (labelM z) : ℝ) := by field_simp

/-- **The incidence charge inequality with a depth-independent exponent.**

This, not `sourceM_mul_atomM_le_root`, is the form `PredecessorDensity` needs.  The worst-case version
forces `δ ≥ 2·depth/(3R−1)`, and `…CommonFloorShifted_depth_le_logGap` makes `depth` grow like
`log Y` while the seed root is fixed before `Y` is quantified — so `δ` could not be held
constant and the density constant would decay like `1/log Y`.

Everything here is proved.  What is *not* proved is `PathHarmonicBounded (sourceM z) (depthM z) δ`
for a single `δ` valid along every physical incidence: that is the one remaining analytic input,
and it should follow from the artifact's own per-generation geometric descent
(`…IncidenceSource_shell`), which makes `∑_j 1/(3·s_j − 1)` a geometric series of size
`O(1/root)` rather than a sum of `depth` equal worst-case terms. -/
theorem sourceM_mul_atomM_le_root_pathSum (hrootOdd : ∀ i, Odd (root i))
    (z : IncidenceM Label root base shift K) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsum : PathHarmonicBounded (sourceM z) (depthM z) δ) :
    (sourceM z : ℝ) * atomM z ≤ (1 + δ) * (root (labelM z) : ℝ) := by
  have hsourceOdd : Odd (sourceM z) := sourceM_odd hrootOdd z
  have hsourcePos : (0 : ℝ) < (sourceM z : ℝ) := by exact_mod_cast hsourceOdd.pos
  have hiter : (syrM^[depthM z]) (sourceM z) = root (labelM z) := sourceM_iterate hrootOdd z
  have hlike := prefixLikelihoodM_le_terminal_div_source_pathSum
    (sourceM z) hsourceOdd (depthM z) hδ hδ1 hsum
  rw [hiter] at hlike
  rw [atomM_eq_prefixLikelihoodM hrootOdd z]
  calc (sourceM z : ℝ) * prefixLikelihoodM (sourceM z) hsourceOdd (depthM z)
      = prefixLikelihoodM (sourceM z) hsourceOdd (depthM z) * (sourceM z : ℝ) := by ring
    _ ≤ ((1 + δ) * ((root (labelM z) : ℝ) / (sourceM z : ℝ))) * (sourceM z : ℝ) :=
        mul_le_mul_of_nonneg_right hlike hsourcePos.le
    _ = (1 + δ) * (root (labelM z) : ℝ) := by field_simp

/-! ## The unconditional charge bound

Both of the conditional bounds above go through the prefix-mass telescoping, and both pay for it:
the worst-case form needs an interior-orbit floor the artifact never proves, and the path-sum form
needs a bound on `∑ 1/(3 s_j − 1)`.

**Neither is necessary.**  The cleared affine identity gives the charge directly.  For `3x+1`,
`3^d · source + C = 2^W · root` with `C = taoOffsetNum ≥ 0`, so `source · atom ≤ root` exactly.
For `3x−1` the offset moves to the other side,

    3^d · source = 2^W · root + C,      so   source · atom = root + C/2^W,

and the excess `C/2^W = taoOffsetList(word)` is bounded by the artifact's own envelope
`taoOffsetNum_le_two_pow_weight_mul_three_pow_length` at `3^d`, while the artifact's own room
lemma gives `2·3^d < root`.  Hence `source · atom < (3/2)·root` with **no hypotheses beyond the
ones the `+1` proof already carries**, and with an absolute constant. -/

theorem atomM_eq_div (z : IncidenceM Label root base shift K) :
    atomM z = (3 : ℝ) ^ depthM z / (2 : ℝ) ^ Tao.taoTupleWeight (rootSideWordM z) := by
  have hlen := wordM_length z
  unfold atomM
  rw [← hlen, Tao.geom2PNatListPMF_apply_length_toReal_eq_weight,
    Tao.one_div_two_pow_eq_inv_pow]
  ring

theorem chronologicalWordM_weight (z : IncidenceM Label root base shift K) :
    Tao.taoTupleWeight (chronologicalWordM z) = Tao.taoTupleWeight (rootSideWordM z) := by
  unfold chronologicalWordM
  exact Tao.taoTupleWeight_reverse _

/-- The incidence's cleared affine identity, over `ℕ`. -/
theorem sourceM_cleared (hrootOdd : ∀ i, Odd (root i))
    (z : IncidenceM Label root base shift K) :
    3 ^ depthM z * sourceM z =
      2 ^ Tao.taoTupleWeight (rootSideWordM z) * root (labelM z) +
        Tao.taoOffsetNum (chronologicalWordM z) := by
  have haff := (sourceM_odd_and_affine hrootOdd z).2
  have h := (taoAffListM_eq_nat_iff_cleared (chronologicalWordM z) (sourceM z)
    (root (labelM z))).mp haff
  rw [chronologicalWordM_length z, chronologicalWordM_weight z] at h
  exact h

/-- **The charge inequality for `3x−1`, unconditional, with an absolute constant.**

Compare `ndGeom2PredictableRootSideBoundedOvershootIncidence_source_mul_atom_le_root`, which
gives `source · atom ≤ root` under exactly these hypotheses.  The sign reversal costs a factor
`3/2` and nothing else — in particular no `δ(Y)`, no interior-orbit floor, and no dependence on
the depth. -/
theorem sourceM_mul_atomM_le_root_unconditional
    (hrootOdd : ∀ i, Odd (root i)) (hbaseNine : ∀ i, 9 ≤ base i)
    (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (z : IncidenceM Label root base shift K) :
    (sourceM z : ℝ) * atomM z ≤ (3 / 2 : ℝ) * (root (labelM z) : ℝ) := by
  have hcl := sourceM_cleared hrootOdd z
  have henvN : Tao.taoOffsetNum (chronologicalWordM z) ≤
      2 ^ Tao.taoTupleWeight (rootSideWordM z) * 3 ^ depthM z := by
    have h := Tao.taoOffsetNum_le_two_pow_weight_mul_three_pow_length (chronologicalWordM z)
    rwa [chronologicalWordM_length z, chronologicalWordM_weight z] at h
  have hroomN := roomM hbaseNine hrootLower z
  have h2W : (0 : ℝ) < (2 : ℝ) ^ Tao.taoTupleWeight (rootSideWordM z) := by positivity
  have hclR : (3 : ℝ) ^ depthM z * (sourceM z : ℝ) =
      (2 : ℝ) ^ Tao.taoTupleWeight (rootSideWordM z) * (root (labelM z) : ℝ) +
        (Tao.taoOffsetNum (chronologicalWordM z) : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hcl
    push_cast at h
    exact h
  have henvR : (Tao.taoOffsetNum (chronologicalWordM z) : ℝ) ≤
      (2 : ℝ) ^ Tao.taoTupleWeight (rootSideWordM z) * (3 : ℝ) ^ depthM z := by
    exact_mod_cast henvN
  have hroomR : 2 * (3 : ℝ) ^ depthM z < (root (labelM z) : ℝ) := by exact_mod_cast hroomN
  have key : (3 : ℝ) ^ depthM z * (sourceM z : ℝ) ≤
      (2 : ℝ) ^ Tao.taoTupleWeight (rootSideWordM z) *
        ((3 / 2 : ℝ) * (root (labelM z) : ℝ)) := by
    rw [hclR]
    nlinarith [henvR, hroomR, h2W]
  rw [atomM_eq_div, ← mul_div_assoc, div_le_iff₀ h2W]
  nlinarith [key]

end

end ThreeXMinusOne
