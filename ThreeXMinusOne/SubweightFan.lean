import ThreeXMinusOne.ResidueCensus

/-!
# The fanned subweight bound

`fullTerminal_subweight_fan_two_conductor_bound_of_height_of_nonreturningSeed` and
`forwardGoodDepthShiftUnitMass_le_two_conductor_of_height_of_nonreturningSeed`, mirrored.

This is where the mixing input is spent.  The fanned sum evaluates the reference density at
`conductor k`; the mixing hypothesis says that density is close, in mean, to its projection at
the coarser conductor `m`, and the coarser one is bounded by a height `H`.  So each fan term is
at most `H` plus a discrepancy, the discrepancy sums against the weights by Layer 59's residue
census, and the fan coefficients sum to `4/3`.

**Where the negation goes.**  The minus mark is read at `−(source)`, so the test function is
`psi y = delta(−(residueFanM k j y))`.  Both negation and the residue fan are mean-preserving
bijections of `ZMod (3^k)`, so `mean psi = mean delta` and the mixing bound applies unchanged.
That composition is the only new step relative to `+1`.

Constants: `+1` has `33` from the residue census and `44 = (4/3)·33`; the wider minus window
gives `66` and `88`, and the generation excess rides along inside the charge.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

/-- **The fanned subweight bound.** -/
theorem fullTerminalM_subweight_fan_two_conductor_bound
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    (shift : (forwardIterateM U cap n).state.Label → ℕ) (K J : ℕ)
    (hseed : ∀ i k, 0 < k → (syrM^[k]) (U.state.root i) ≠ U.state.root i)
    (v : FullTerminalAtM U cap n shift K → ℝ) (hv : ∀ z, 0 ≤ v z)
    (hvw : ∀ z, v z ≤ weightM (forwardIterateM U cap n).state.outerWeight z)
    (m k : ℕ) (hmk : m ≤ k) (X : ℝ) (hX : 0 < X) (hQ : ((3 ^ k : ℕ) : ℝ) ≤ X)
    (hsource : ∀ z : FullTerminalAtM U cap n shift K,
      X ≤ (sourceM z : ℝ) ∧ (sourceM z : ℝ) < 64 * X)
    (hrootOdd : ∀ i, Odd ((forwardIterateM U cap n).state.root i))
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hL1 : ndTernaryUniformMean k (fun y => |ndSyracuseUnitReferenceDensity k y -
      ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|) ≤ epsilon)
    (H : ℝ) (hH : 0 ≤ H) (hheight : ∀ y, ndSyracuseUnitReferenceDensity m y ≤ H) :
    letI := (forwardIterateM U cap n).state.labelFintype
    (∑ z : FullTerminalAtM U cap n shift K, v z *
        ∑ j : Fin J, (1 / 4 : ℝ) ^ j.val * ndSyracuseUnitReferenceDensity k
          (-((sourceFanM j.val (sourceM z) : ℕ) : ZMod (3 ^ k)))) ≤
      (4 / 3 : ℝ) * H * (∑ z, v z) +
        88 * (generationExcessProductM U cap (n + 1) * U.parentSourcePotential) * epsilon := by
  classical
  letI := (forwardIterateM U cap n).state.labelFintype
  set delta := fun y : ZMod (3 ^ k) => |ndSyracuseUnitReferenceDensity k y -
    ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)| with hdelta
  have hmass : 0 ≤ ∑ z, v z := Finset.sum_nonneg fun z _ => hv z
  have hPnn : (0 : ℝ) ≤ generationExcessProductM U cap (n + 1) * U.parentSourcePotential :=
    mul_nonneg (generationExcessProductM_nonneg U cap (n + 1)) (parentSourcePotentialM_nonneg U)
  have hstep (j : ℕ) :
      (∑ z, v z * ndSyracuseUnitReferenceDensity k
        (-((sourceFanM j (sourceM z) : ℕ) : ZMod (3 ^ k)))) ≤
      H * (∑ z, v z) +
        66 * (generationExcessProductM U cap (n + 1) * U.parentSourcePotential) * epsilon := by
    set psi := fun y : ZMod (3 ^ k) => delta (-(residueFanM k j y)) with hpsi
    have hp : ∀ y, 0 ≤ psi y := fun _ => abs_nonneg _
    have hmean : ndTernaryUniformMean k psi ≤ epsilon := by
      have h1 : ndTernaryUniformMean k (fun y => delta (-(residueFanM k j y))) =
          ndTernaryUniformMean k (fun w => delta (-w)) :=
        residueFanM_fullMean k j (fun w => delta (-w))
      have h2 : ndTernaryUniformMean k (fun w => delta (-w)) = ndTernaryUniformMean k delta :=
        ndTernaryUniformMean_neg k delta
      rw [hpsi, h1, h2]
      exact hL1
    have hc := fullTerminalM_weighted_residue_census U cap n shift K hseed k X hX hQ hsource psi hp
    have hc' : (∑ z, v z * psi (((sourceM z : ℕ) : ZMod (3 ^ k)))) ≤
        66 * (generationExcessProductM U cap (n + 1) * U.parentSourcePotential) * epsilon := by
      refine le_trans (Finset.sum_le_sum (fun z _ =>
        mul_le_mul_of_nonneg_right (hvw z) (hp _))) ?_
      exact hc.trans (mul_le_mul_of_nonneg_left hmean
        (mul_nonneg (by norm_num) hPnn))
    have hpoint (z : FullTerminalAtM U cap n shift K) :
        ndSyracuseUnitReferenceDensity k
          (-((sourceFanM j (sourceM z) : ℕ) : ZMod (3 ^ k))) ≤
          H + psi (((sourceM z : ℕ) : ZMod (3 ^ k))) := by
      have hpos : 1 ≤ sourceM z := (sourceM_odd hrootOdd z).pos
      have hfan : residueFanM k j (((sourceM z : ℕ) : ZMod (3 ^ k))) =
          ((sourceFanM j (sourceM z) : ℕ) : ZMod (3 ^ k)) := residueFanM_natCast hpos k j
      rw [hpsi]
      simp only [hfan]
      have hb := hheight (Tao.taoZModThreeProjection hmk
        (-((sourceFanM j (sourceM z) : ℕ) : ZMod (3 ^ k))))
      have ha := le_abs_self (ndSyracuseUnitReferenceDensity k
          (-((sourceFanM j (sourceM z) : ℕ) : ZMod (3 ^ k))) -
        ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk
          (-((sourceFanM j (sourceM z) : ℕ) : ZMod (3 ^ k)))))
      rw [hdelta]
      linarith
    calc (∑ z, v z * ndSyracuseUnitReferenceDensity k
          (-((sourceFanM j (sourceM z) : ℕ) : ZMod (3 ^ k))))
        ≤ ∑ z, v z * (H + psi (((sourceM z : ℕ) : ZMod (3 ^ k)))) :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpoint z) (hv z)
      _ = H * (∑ z, v z) + ∑ z, v z * psi (((sourceM z : ℕ) : ZMod (3 ^ k))) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, mul_comm]
      _ ≤ _ := add_le_add_right hc' _
  set B := H * (∑ z, v z) +
    66 * (generationExcessProductM U cap (n + 1) * U.parentSourcePotential) * epsilon with hB
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact add_nonneg (mul_nonneg hH hmass)
      (mul_nonneg (mul_nonneg (by norm_num) hPnn) he)
  calc (∑ z : FullTerminalAtM U cap n shift K, v z *
        ∑ j : Fin J, (1 / 4 : ℝ) ^ j.val * ndSyracuseUnitReferenceDensity k
          (-((sourceFanM j.val (sourceM z) : ℕ) : ZMod (3 ^ k))))
      = ∑ j : Fin J, (1 / 4 : ℝ) ^ j.val *
          ∑ z, v z * ndSyracuseUnitReferenceDensity k
            (-((sourceFanM j.val (sourceM z) : ℕ) : ZMod (3 ^ k))) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun z _ => by ring
    _ ≤ ∑ _j : Fin J, (1 / 4 : ℝ) ^ (_j : ℕ) * B :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hstep _) (by positivity)
    _ = (∑ j : Fin J, (1 / 4 : ℝ) ^ j.val) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ (4 / 3 : ℝ) * B := mul_le_mul_of_nonneg_right (terminal_fan_coeff_sum_le J) hBnn
    _ = _ := by rw [hB]; ring

end

end ThreeXMinusOne
