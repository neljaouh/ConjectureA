import ThreeXMinusOne.Telescope

/-!
# The repaired charge inequality for `3x−1`

Layer 3 of the port: `CommonZEndpointPrefixFactorization` together with
`rootTerminal_prefixLikelihood_le_terminal_div_source`, the single private lemma of
`Geom2ShiftedWideSymmetricRootSideIntervalFirstReachingRootTerminal` through which the whole
telescoping reaches the counting argument.

On the `+1` side that lemma reads

    prefixLikelihood source depth ≤ terminal / source

and is the *only* consumer of `ndCommonZOrbitPrefixMass_le_zero`.  Since that antitonicity fails
for `3x−1` (Layer 2), the inequality acquires the inflation factor computed there.  The final
statement of this file, `prefixLikelihoodM_le_terminal_div_source`, recovers the original form
verbatim under an explicit, checkable smallness hypothesis relating the path's floor `R` to its
depth — `2·depth ≤ δ·(3R−1)`, which in M2's own application is
`2·J ≤ δ·(3·16^(2^80) − 1)` with `δ = 13/512` the slack the proof already carries.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.Tao

noncomputable section

theorem geom2PNatListMass_append (as bs : List ℕ+) :
    geom2PNatListMass (as ++ bs) = geom2PNatListMass as * geom2PNatListMass bs := by
  unfold geom2PNatListMass
  simp

theorem prefixGeomMassM_add (N : ℕ) (hN : Odd N) (d m : ℕ) :
    prefixGeomMassM N hN (d + m) =
      prefixGeomMassM N hN d *
        prefixGeomMassM ((syrM^[d]) N) (syrM_iterate_odd d N hN) m := by
  unfold prefixGeomMassM
  rw [syrMValuationPNatList_add]
  exact geom2PNatListMass_append _ _

def prefixLikelihoodM (N : ℕ) (hN : Odd N) (d : ℕ) : ℝ :=
  prefixGeomMassM N hN d * (3 : ℝ) ^ d

theorem prefixMassM_add (N : ℕ) (hN : Odd N) (d m : ℕ) :
    prefixMassM N hN (d + m) =
      prefixLikelihoodM N hN d *
        prefixMassM ((syrM^[d]) N) (syrM_iterate_odd d N hN) m := by
  unfold prefixMassM prefixLikelihoodM EdgeM.sourceWeight
  simp only [orbitEdgeM_source]
  rw [prefixGeomMassM_add, pow_add]
  rw [Function.iterate_add_apply]
  have hiter : (syrM^[d]) ((syrM^[m]) N) = (syrM^[m]) ((syrM^[d]) N) := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]
  rw [hiter]
  ring

theorem prefixLikelihoodM_pos (N : ℕ) (hN : Odd N) (d : ℕ) : 0 < prefixLikelihoodM N hN d := by
  unfold prefixLikelihoodM
  have := prefixGeomMassM_pos N hN d
  positivity

/-- The factorisation of the prefix mass at the terminal, exactly as on the `+1` side. -/
theorem prefixMassM_eq_likelihood_div_terminal (source : ℕ) (hsource : Odd source) (depth : ℕ) :
    prefixMassM source hsource depth =
      prefixLikelihoodM source hsource depth * (1 / (((syrM^[depth]) source : ℕ) : ℝ)) := by
  have hadd := prefixMassM_add source hsource depth 0
  simpa only [Nat.add_zero, prefixMassM_zero] using hadd

/-- **The repaired charge inequality.**  Compare
`rootTerminal_prefixLikelihood_le_terminal_div_source`: the conclusion is the same except for
the inflation factor `exp (depth/(3R−1))` forced by the sign reversal. -/
theorem prefixLikelihoodM_le_terminal_div_source_mul_exp
    (source : ℕ) (hsource : Odd source) (depth : ℕ) {R : ℝ} (hR : 1 < R)
    (hfloor : ∀ j, j < depth → R ≤ (((syrM^[j]) source : ℕ) : ℝ)) :
    prefixLikelihoodM source hsource depth ≤
      (((syrM^[depth]) source : ℕ) : ℝ) / (source : ℝ) *
        Real.exp ((depth : ℝ) * (1 / (3 * R - 1))) := by
  have hsourcePos : (0 : ℝ) < source := by exact_mod_cast hsource.pos
  have hterminalPos : (0 : ℝ) < (((syrM^[depth]) source : ℕ) : ℝ) := by
    exact_mod_cast (syrM_iterate_odd depth source hsource).pos
  have hfactor := prefixMassM_eq_likelihood_div_terminal source hsource depth
  have hmass := prefixMassM_le_exp source hsource hR depth hfloor
  rw [hfactor] at hmass
  -- `L * (1/T) ≤ (1/s) * E`  ⟹  `L ≤ (T/s) * E`
  have hscaled := mul_le_mul_of_nonneg_right hmass hterminalPos.le
  have hL : prefixLikelihoodM source hsource depth
      = prefixLikelihoodM source hsource depth * (1 / (((syrM^[depth]) source : ℕ) : ℝ))
          * (((syrM^[depth]) source : ℕ) : ℝ) := by
    field_simp
  rw [hL]
  refine hscaled.trans_eq ?_
  field_simp

/-! ## Absorbing the inflation -/

/-- `exp x ≤ 1/(1−x)` for `0 ≤ x < 1`. -/
theorem exp_le_one_div_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.exp x ≤ 1 / (1 - x) := by
  have hsub : (0 : ℝ) < 1 - x := by linarith
  have hneg : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have hexp : Real.exp (-x) = 1 / Real.exp x := by
    rw [Real.exp_neg]; ring
  rw [hexp] at hneg
  have hEpos : (0 : ℝ) < Real.exp x := Real.exp_pos x
  rw [le_div_iff₀ hEpos] at hneg
  rw [le_div_iff₀ hsub]
  nlinarith [hneg]

/-- If `x ≤ δ/2` with `0 < δ ≤ 1`, then `exp x ≤ 1 + δ`. -/
theorem exp_le_one_add_of_le_half {x δ : ℝ} (hx : 0 ≤ x) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : x ≤ δ / 2) : Real.exp x ≤ 1 + δ := by
  have hx1 : x < 1 := by linarith
  have h1 := exp_le_one_div_one_sub hx hx1
  have hsub : (0 : ℝ) < 1 - x := by linarith
  have h2 : 1 / (1 - x) ≤ 1 + δ := by
    rw [div_le_iff₀ hsub]
    nlinarith
  linarith

/-- **The charge inequality, recovered verbatim.**  Under the explicit smallness hypothesis
`2·depth ≤ δ·(3R−1)` the inflation is absorbed into a factor `1 + δ`, and the `3x−1` bound has
exactly the shape the counting argument consumes on the `+1` side. -/
theorem prefixLikelihoodM_le_terminal_div_source
    (source : ℕ) (hsource : Odd source) (depth : ℕ) {R δ : ℝ} (hR : 1 < R)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hfloor : ∀ j, j < depth → R ≤ (((syrM^[j]) source : ℕ) : ℝ))
    (hsmall : 2 * (depth : ℝ) ≤ δ * (3 * R - 1)) :
    prefixLikelihoodM source hsource depth ≤
      (1 + δ) * ((((syrM^[depth]) source : ℕ) : ℝ) / (source : ℝ)) := by
  have hRpos : (0 : ℝ) < 3 * R - 1 := by linarith
  have hx : (0 : ℝ) ≤ (depth : ℝ) * (1 / (3 * R - 1)) := by positivity
  have hhalf : (depth : ℝ) * (1 / (3 * R - 1)) ≤ δ / 2 := by
    rw [mul_one_div, div_le_iff₀ hRpos]
    linarith
  have hexp : Real.exp ((depth : ℝ) * (1 / (3 * R - 1))) ≤ 1 + δ :=
    exp_le_one_add_of_le_half hx hδ hδ1 hhalf
  have hmain := prefixLikelihoodM_le_terminal_div_source_mul_exp source hsource depth hR hfloor
  have hsourcePos : (0 : ℝ) < source := by exact_mod_cast hsource.pos
  have hterminalPos : (0 : ℝ) < (((syrM^[depth]) source : ℕ) : ℝ) := by
    exact_mod_cast (syrM_iterate_odd depth source hsource).pos
  have hratio : (0 : ℝ) ≤ (((syrM^[depth]) source : ℕ) : ℝ) / (source : ℝ) := by positivity
  calc prefixLikelihoodM source hsource depth
      ≤ (((syrM^[depth]) source : ℕ) : ℝ) / (source : ℝ) *
          Real.exp ((depth : ℝ) * (1 / (3 * R - 1))) := hmain
    _ ≤ (((syrM^[depth]) source : ℕ) : ℝ) / (source : ℝ) * (1 + δ) :=
        mul_le_mul_of_nonneg_left hexp hratio
    _ = (1 + δ) * ((((syrM^[depth]) source : ℕ) : ℝ) / (source : ℝ)) := by ring

/-! ## The sharp charge bound

The worst-case form above is too lossy to survive `Y → ∞`: its `δ` must exceed
`2·depth/(3R−1)`, and in M2's application `depth` grows like `log Y` while the seed root is a
constant fixed before `Y` is quantified.  The version below replaces the worst-case exponent by
the path-harmonic sum, which for a geometrically descending orbit is bounded independently of
the depth.

Both are **superseded** by the unconditional bound in `IncidenceCharge`; see the note there. -/

/-- The path-harmonic hypothesis.

**Superseded.**  `IncidenceCharge.sourceM_mul_atomM_le_root_unconditional` obtains the charge
bound with no hypothesis of this kind at all, by going through the cleared affine identity
instead of the telescoping.  This definition and the two lemmas below are kept because the
telescoping identity `prefixMassM_succ_eq_mul` is sharp and of independent interest, but nothing
downstream needs them. -/
def PathHarmonicBounded (source depth : ℕ) (δ : ℝ) : Prop :=
  ∑ j ∈ Finset.range depth, 1 / (3 * (((syrM^[j]) source : ℕ) : ℝ) - 1) ≤ δ / 2

/-- **The charge inequality, with the depth-independent exponent.** -/
theorem prefixLikelihoodM_le_terminal_div_source_pathSum
    (source : ℕ) (hsource : Odd source) (depth : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsum : PathHarmonicBounded source depth δ) :
    prefixLikelihoodM source hsource depth ≤
      (1 + δ) * ((((syrM^[depth]) source : ℕ) : ℝ) / (source : ℝ)) := by
  have hsourcePos : (0 : ℝ) < source := by exact_mod_cast hsource.pos
  have hterminalPos : (0 : ℝ) < (((syrM^[depth]) source : ℕ) : ℝ) := by
    exact_mod_cast (syrM_iterate_odd depth source hsource).pos
  have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range depth, 1 / (3 * (((syrM^[j]) source : ℕ) : ℝ) - 1) := by
    refine Finset.sum_nonneg (fun j _ => ?_)
    have hs : (1 : ℝ) ≤ (((syrM^[j]) source : ℕ) : ℝ) := by
      exact_mod_cast (syrM_iterate_odd j source hsource).pos
    have : (0 : ℝ) < 3 * (((syrM^[j]) source : ℕ) : ℝ) - 1 := by linarith
    positivity
  have hexp : Real.exp (∑ j ∈ Finset.range depth,
      1 / (3 * (((syrM^[j]) source : ℕ) : ℝ) - 1)) ≤ 1 + δ :=
    exp_le_one_add_of_le_half hnn hδ hδ1 hsum
  have hmass := prefixMassM_le_exp_pathSum source hsource depth
  rw [prefixMassM_eq_likelihood_div_terminal source hsource depth, prefixMassM_zero] at hmass
  -- L * (1/T) ≤ (1/s) * E  ⟹  L ≤ (T/s) * E ≤ (1+δ) * (T/s)
  have hscaled := mul_le_mul_of_nonneg_right hmass hterminalPos.le
  have hL : prefixLikelihoodM source hsource depth
      = prefixLikelihoodM source hsource depth * (1 / (((syrM^[depth]) source : ℕ) : ℝ))
          * (((syrM^[depth]) source : ℕ) : ℝ) := by
    field_simp
  have hmid : prefixLikelihoodM source hsource depth ≤
      (((syrM^[depth]) source : ℕ) : ℝ) / (source : ℝ) *
        Real.exp (∑ j ∈ Finset.range depth, 1 / (3 * (((syrM^[j]) source : ℕ) : ℝ) - 1)) := by
    rw [hL]
    refine hscaled.trans_eq ?_
    field_simp
  have hratio : (0 : ℝ) ≤ (((syrM^[depth]) source : ℕ) : ℝ) / (source : ℝ) := by positivity
  calc prefixLikelihoodM source hsource depth
      ≤ (((syrM^[depth]) source : ℕ) : ℝ) / (source : ℝ) *
          Real.exp (∑ j ∈ Finset.range depth,
            1 / (3 * (((syrM^[j]) source : ℕ) : ℝ) - 1)) := hmid
    _ ≤ (((syrM^[depth]) source : ℕ) : ℝ) / (source : ℝ) * (1 + δ) :=
        mul_le_mul_of_nonneg_left hexp hratio
    _ = (1 + δ) * ((((syrM^[depth]) source : ℕ) : ℝ) / (source : ℝ)) := by ring

end

end ThreeXMinusOne
