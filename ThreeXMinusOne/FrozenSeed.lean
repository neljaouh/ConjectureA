import ThreeXMinusOne.GoodMargin
import ThreeXMinusOne.SeedMark

/-!
# The frozen seed

`exists_generalTarget_uniform_twoThirds_seed`, mirrored — with `1/4` in place of `2/3`, which is
what Layer 70's crude `E ≤ 2` certifies.

Layer 63 produced a seed whose singleton state carries core mass `≥ 255/256`.  Layer 70 says such
a seed keeps at least a quarter of its mass at *every* later generation.  This joins them: one
state, reaching the target, non-returning, whose good terminal mass is bounded below uniformly in
the generation.

**A small circularity, and how the floor recursion breaks it.**  The seed lemma is indexed by the
conductor `k`, which is the generation-`N` floor divided by four — and the generation-`N` floor
belongs to the state built *from* the seed.  But Layer 64 already showed that floor depends only
on the starting floor and the caps, never on the roots: it is `floorIterM b N`.  So the conductor
can be named before the seed exists.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

/-- The generation from which the margin holds. -/
def goodMarkedStartM (b C N : ℕ) : ℕ :=
  max N (explicitLogarithmicTerminalStart b C 1)

/-- **The frozen seed.** -/
theorem exists_frozenSeedStateM {a b : ℕ} (ha : 0 < a) (hthree : ¬ 3 ∣ a)
    (hb : 2 ^ 80 ≤ b) (C : ℕ) (hmix : Tao.syracFineScaleMixingAt 6 (C : ℝ))
    {N : ℕ} (hN : explicitLogarithmicSeedGeneration b C ≤ N) :
    ∃ U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState,
      U.floor = b ∧ U.denominator = 1 ∧ rootSpanM U 0 ∧
      (∀ i, ReachesM (U.state.root i) a) ∧
      (∀ i k, 0 < k → (syrM^[k]) (U.state.root i) ≠ U.state.root i) ∧
      0 < U.parentSourcePotential ∧
      ∀ n, goodMarkedStartM b C N ≤ n →
        ∀ (X : ℝ) (hX : 0 < X)
          (hi : ∀ i : (forwardIterateM U (fun j => 16 + j / 100) n).state.Label,
            ndGeom2ShiftedWideSymmetricPhysicalIntervalMin
                (forwardIterateM U (fun j => 16 + j / 100) n).floor
                ((forwardIterateM U (fun j => 16 + j / 100) n).state.root i) < X ∧
              X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
                (forwardIterateM U (fun j => 16 + j / 100) n).floor
                ((forwardIterateM U (fun j => 16 + j / 100) n).state.root i)),
          (1 / 4 : ℝ) ≤ forwardCoreTerminalGoodDepthShiftUnitMassM U
            (fun j => 16 + j / 100) ndRootCoreWidth n (16 + n / 100)
            ((forwardIterateM U (fun j => 16 + j / 100) n).floor / 4) X hX hi := by
  classical
  have hb200 : 200 ≤ b := (by norm_num : (200 : ℕ) ≤ 2 ^ 80).trans hb
  have hcap : ∀ j, (fun j => 16 + j / 100) j ≤ 17 * (j + 1) := by
    intro j
    have hj := Nat.div_le_self j 100
    simp only
    omega
  have hcaplo : ∀ j, 16 + j / 100 ≤ (fun j => 16 + j / 100) j := fun j => le_rfl
  have hfl := floorIterM_twoHundred hb200 N
  obtain ⟨r, hr, hl, htarget, hnonreturn, hunit, hmark⟩ :=
    exists_generalTargetM_full_core_mark (a := a) (b := b) (k := floorIterM b N / 4)
      ha hthree hb (by omega) (fun j => 16 + j / 100) hcaplo N
  refine ⟨ndRootCoreSingletonState b r hb200 hr hl, rfl, ?_, ?_, fun _ => htarget,
    fun _ => hnonreturn, ?_, ?_⟩
  · change ndGeom2PredictableOuterDenominator (Finset.univ : Finset Unit) (fun _ => (1 : ℝ)) = 1
    simp [ndGeom2PredictableOuterDenominator]
  · intro i j; change r ≤ 2 ^ 0 * r; simp
  · have hp : (ndRootCoreSingletonState b r hb200 hr hl).parentSourcePotential = (r : ℝ) := by
      change ndGeom2PredictableRootSideParentSourcePotential (Finset.univ : Finset Unit)
        (fun _ => (1 : ℝ)) (fun _ => r) = _
      simp [ndGeom2PredictableRootSideParentSourcePotential]
    rw [hp]; exact_mod_cast hr.pos
  · intro n hn X hX hi
    have hD : (ndRootCoreSingletonState b r hb200 hr hl).denominator = 1 := by
      change ndGeom2PredictableOuterDenominator (Finset.univ : Finset Unit) (fun _ => (1 : ℝ)) = 1
      simp [ndGeom2PredictableOuterDenominator]
    have hfloorN : (forwardIterateM (ndRootCoreSingletonState b r hb200 hr hl)
        (fun j => 16 + j / 100) N).floor = floorIterM b N :=
      forwardIterateM_floor_eq_iter _ _ _
    have hseed : (255 / 256 : ℝ) *
        (ndRootCoreSingletonState b r hb200 hr hl).denominator ≤
        coreMarkedSequenceM (ndRootCoreSingletonState b r hb200 hr hl)
          (fun j => 16 + j / 100) ndRootCoreWidth N := by
      rw [hD, mul_one]
      unfold coreMarkedSequenceM
      rw [hfloorN]
      exact hmark
    have hmargin := explicit_good_marked_marginM_logarithmic_full C hmix
      (ndRootCoreSingletonState b r hb200 hr hl)
      (show (32 : ℕ) ^ 5 ≤ b from (by norm_num : (32 : ℕ) ^ 5 ≤ 2 ^ 80).trans hb)
      (fun j => 16 + j / 100) 0 (by intro i j; change r ≤ 2 ^ 0 * r; simp)
      hcap hcaplo hN
      (le_trans (le_max_left _ _) hn)
      (by
        have := le_trans (le_max_right N (explicitLogarithmicTerminalStart b C 1)) hn
        simpa using this)
      hseed X hX hi
    rw [hD, mul_one] at hmargin
    exact hmargin

end

end ThreeXMinusOne
