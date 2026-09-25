import ThreeXMinusOne.GoodCoreCensus

/-!
# The source-weighted charge, and the good-core census

`fullTerminal_weighted_source_charge` and
`fullGoodCoreTerminal_mass_mul_lower_le_frozenPotential_mul_card`, mirrored.

Layer 38 proved the census with the constant weight `1` on sources.  What the count actually
needs is the census restricted to the sources that survive *both* filters, and the way the
artifact gets there is to run the same argument against an arbitrary non-negative weight `psi`
on sources, then take `psi` to be the indicator of the good source set.

So this file generalises Layer 38 once and instantiates it once.  The injectivity is Layer 34's,
the per-incidence charge is Layer 37's, and the generation excess rides along unchanged — it is
a constant factor, so it passes through the weighting untouched.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

theorem parentSourcePotentialM_nonneg
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) :
    0 ≤ U.parentSourcePotential := by
  classical
  letI := U.state.labelFintype
  unfold NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.parentSourcePotential
    ndGeom2PredictableRootSideParentSourcePotential
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (Nat.cast_nonneg _) (U.state.weight_nonneg i)

/-- **The census against an arbitrary non-negative weight on sources.** -/
theorem fullTerminalM_weighted_source_charge
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    (shift : (forwardIterateM U cap n).state.Label → ℕ) (K : ℕ)
    (hseed : ∀ i k, 0 < k → (syrM^[k]) (U.state.root i) ≠ U.state.root i)
    (X : ℝ) (hsource : ∀ z : FullTerminalAtM U cap n shift K, X ≤ (sourceM z : ℝ))
    (psi : ℕ → ℝ) (hp : ∀ x, 0 ≤ psi x) :
    letI := (forwardIterateM U cap n).state.labelFintype
    X * (∑ z : FullTerminalAtM U cap n shift K,
        weightM (forwardIterateM U cap n).state.outerWeight z * psi (sourceM z)) ≤
      generationExcessProductM U cap (n + 1) *
        (U.parentSourcePotential *
          ∑ x ∈ fullTerminalSourcesM U cap n shift K, psi x) := by
  classical
  letI := U.state.labelFintype
  letI := (forwardIterateM U cap n).state.labelFintype
  set P := fun i : U.state.Label => (U.state.root i : ℝ) * U.state.outerWeight i with hP
  set cell := fun z : FullTerminalAtM U cap n shift K =>
    (fullTerminalAncestorM z, sourceM z) with hcell
  set sources := fullTerminalSourcesM U cap n shift K with hsources
  have hinj : Function.Injective cell := by
    intro z w h
    exact fullTerminalM_eq_of_nonreturningSeed_ancestor_source_eq hseed
      (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hsub : Finset.univ.image cell ⊆ Finset.univ.product sources := by
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  have hprod := generationExcessProductM_nonneg U cap (n + 1)
  calc X * (∑ z : FullTerminalAtM U cap n shift K,
        weightM (forwardIterateM U cap n).state.outerWeight z * psi (sourceM z))
      = ∑ z, X * weightM (forwardIterateM U cap n).state.outerWeight z * psi (sourceM z) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
    _ ≤ ∑ z : FullTerminalAtM U cap n shift K,
        generationExcessProductM U cap (n + 1) * P (fullTerminalAncestorM z) *
          psi (sourceM z) := by
        refine Finset.sum_le_sum fun z _ => ?_
        have hw := weightM_nonneg (forwardIterateM U cap n).state.outerWeight
          (forwardIterateM U cap n).state.weight_nonneg z
        have hstep := (mul_le_mul_of_nonneg_right (hsource z) hw).trans
          (fullTerminalM_source_mul_weight_le_owner U cap n shift K z)
        exact mul_le_mul_of_nonneg_right hstep (hp _)
    _ = generationExcessProductM U cap (n + 1) *
        ∑ z : FullTerminalAtM U cap n shift K, P (fullTerminalAncestorM z) * psi (sourceM z) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
    _ ≤ generationExcessProductM U cap (n + 1) *
        (U.parentSourcePotential * ∑ x ∈ sources, psi x) := by
        refine mul_le_mul_of_nonneg_left ?_ hprod
        calc (∑ z : FullTerminalAtM U cap n shift K, P (fullTerminalAncestorM z) * psi (sourceM z))
            = ∑ c ∈ Finset.univ.image cell, P c.1 * psi c.2 := by
              rw [Finset.sum_image]
              exact fun a _ b _ h => hinj h
          _ ≤ ∑ c ∈ Finset.univ.product sources, P c.1 * psi c.2 := by
              refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun c _ _ => ?_
              exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (U.state.weight_nonneg c.1))
                (hp _)
          _ = ∑ i : U.state.Label, ∑ x ∈ sources, P i * psi x := Finset.sum_product _ _ _
          _ = U.parentSourcePotential * ∑ x ∈ sources, psi x := by
              simp only [← Finset.mul_sum]
              unfold NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.parentSourcePotential
                ndGeom2PredictableRootSideParentSourcePotential
                NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorAllLabels
              rw [Finset.sum_mul]

/-- **The good-core census.** -/
theorem fullGoodCoreTerminalM_mass_mul_lower_le_potential_mul_card
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ) (n : ℕ)
    (shift : (forwardIterateM U cap n).state.Label → ℕ) (K : ℕ)
    (hseed : ∀ i k, 0 < k → (syrM^[k]) (U.state.root i) ≠ U.state.root i)
    (X : ℝ) (hXpos : 0 < X)
    (hsource : ∀ z : FullTerminalAtM U cap n shift K, X ≤ (sourceM z : ℝ)) :
    X * fullGoodCoreTerminalMassM U cap width n shift K ≤
      generationExcessProductM U cap (n + 1) *
        (U.parentSourcePotential *
          (fullGoodCoreTerminalSourcesM U cap width n shift K).card) := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  set S := fullGoodCoreTerminalSourcesM U cap width n shift K with hS
  set psi := fun x : ℕ => if x ∈ S then (1 : ℝ) else 0 with hpsi
  have hp : ∀ x, 0 ≤ psi x := by intro x; dsimp only [psi]; split_ifs <;> norm_num
  have hm : fullGoodCoreTerminalMassM U cap width n shift K ≤
      ∑ z : FullTerminalAtM U cap n shift K,
        weightM (forwardIterateM U cap n).state.outerWeight z * psi (sourceM z) := by
    refine Finset.sum_le_sum fun z _ => ?_
    unfold fullGoodCoreTerminalWeightM ndTerminalDepthShiftIndicator
    by_cases hc : 0 < forwardCoreFactorM U cap width n (labelM z)
    · by_cases hgd : ndTerminalDepthShiftGood (forwardIterateM U cap n).floor
          (shift (labelM z)) (depthM z)
      · have hs : sourceM z ∈ S :=
          Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hgd⟩, rfl⟩
        simp only [if_pos hgd, mul_one, psi, if_pos hs]
        unfold weightM
        have h1 := forwardCoreOuterWeightM_le_original U cap width n (labelM z)
        have h2 := atomM_nonneg z
        nlinarith
      · simp only [if_neg hgd, mul_zero]
        exact mul_nonneg (weightM_nonneg _
          (forwardIterateM U cap n).state.weight_nonneg z) (hp _)
    · have hzero : forwardCoreFactorM U cap width n (labelM z) = 0 := by
        have := forwardCoreFactorM_nonneg U cap width n (labelM z); linarith
      have : weightM (forwardCoreOuterWeightM U cap width n) z = 0 := by
        unfold weightM forwardCoreOuterWeightM
        rw [hzero]; ring
      rw [this, zero_mul]
      exact mul_nonneg (weightM_nonneg _
        (forwardIterateM U cap n).state.weight_nonneg z) (hp _)
  have hsum : (∑ x ∈ fullTerminalSourcesM U cap n shift K, psi x) = (S.card : ℝ) := by
    calc (∑ x ∈ fullTerminalSourcesM U cap n shift K, psi x)
        = ∑ x ∈ S, psi x := by
          symm
          refine Finset.sum_subset (fullGoodCoreTerminalSourcesM_subset U cap width n shift K)
            fun x _ hx => ?_
          simp only [psi, if_neg hx]
      _ = (S.card : ℝ) := by simp [psi]
  have hcharge := fullTerminalM_weighted_source_charge U cap n shift K hseed X hsource psi hp
  rw [hsum] at hcharge
  exact (mul_le_mul_of_nonneg_left hm hXpos.le).trans hcharge

end

end ThreeXMinusOne
