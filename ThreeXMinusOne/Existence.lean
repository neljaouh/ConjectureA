import ThreeXMinusOne.Transport
import ThreeXMinusOne.DigitM

/-!
# Witnessing a nonzero transport by a `3x−1` incidence

Rung six: `exists_unitIncidence_of_referencePrefixTransportAt_ne_zero`.

The construction transfers cleanly.  The `+1` proof extracts a fibre point from a nonzero sum,
projects it to `taoSection7OffsetZMod d w = (root : ZMod (3^d))`, and builds the incidence from
that.  Here every occurrence of `root` is negated, and the projection lands on
`taoSection7OffsetZMod d w = -(root : ZMod (3^d))` — which is exactly the membership condition
`WordM` was defined with in Layer 7.  So the incidence builds with no friction, and the risk I
expected here (that constructing an incidence would expose the digit sign) is in fact where the
negation *helps*.

The friction is elsewhere: the unit hypothesis.  The artifact states it at natural-number casts,

    hunit : ∀ n : ℕ, ¬ IsUnit (n : ZMod (3^1)) → g (n : ZMod (3^k)) = 0

and the minus transport evaluates `g` at `-(source)`, which is not syntactically a natural cast.
It is one semantically — every `y : ZMod n` equals `(y.val : ℕ)` — and casting that
representative down to `ZMod 3` commutes with negation, so `IsUnit (-y) ↔ IsUnit y`.
`g_neg_eq_zero_of_not_isUnit` below is that bridge.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

/-- The artifact's unit hypothesis, transported across the negation. -/
theorem g_neg_eq_zero_of_not_isUnit {k : ℕ} (hk1 : 1 ≤ k) (g : ZMod (3 ^ k) → ℝ)
    (hunit : ∀ n : ℕ, ¬ IsUnit ((n : ℕ) : ZMod (3 ^ 1)) → g ((n : ℕ) : ZMod (3 ^ k)) = 0)
    (N : ℕ) (h : ¬ IsUnit ((N : ℕ) : ZMod (3 ^ 1))) :
    g (-((N : ℕ) : ZMod (3 ^ k))) = 0 := by
  classical
  set y : ZMod (3 ^ k) := -((N : ℕ) : ZMod (3 ^ k)) with hy
  set n₀ : ℕ := y.val with hn₀
  have hyval : ((n₀ : ℕ) : ZMod (3 ^ k)) = y := by
    rw [hn₀]; exact ZMod.natCast_zmod_val y
  have hproj : ((n₀ : ℕ) : ZMod (3 ^ 1)) = -((N : ℕ) : ZMod (3 ^ 1)) := by
    have h1 : Tao.taoZModThreeProjection hk1 ((n₀ : ℕ) : ZMod (3 ^ k)) =
        ((n₀ : ℕ) : ZMod (3 ^ 1)) := Tao.taoZModThreeProjection_natCast hk1 n₀
    have h2 : Tao.taoZModThreeProjection hk1 ((N : ℕ) : ZMod (3 ^ k)) =
        ((N : ℕ) : ZMod (3 ^ 1)) := Tao.taoZModThreeProjection_natCast hk1 N
    rw [← h1, hyval, hy, map_neg, h2]
  have hnu : ¬ IsUnit ((n₀ : ℕ) : ZMod (3 ^ 1)) := by
    rw [hproj]
    intro hc
    exact h ((IsUnit.neg_iff _).mp hc)
  have := hunit n₀ hnu
  rwa [hyval] at this

/-- **A nonzero transport at the negated residue is witnessed by a `3x−1` incidence.** -/
theorem exists_unitIncidenceM_of_transportAt_ne_zero
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ} {b a K : ℕ}
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (q k : ℕ) (hk1 : 1 ≤ k) (g : ZMod (3 ^ k) → ℝ)
    (hunit : ∀ n : ℕ, ¬ IsUnit ((n : ℕ) : ZMod (3 ^ 1)) → g ((n : ℕ) : ZMod (3 ^ k)) = 0)
    (x : {i : Label // i ∈ Labels} × ndShiftedReferenceSelectedWords b a K)
    (hlen : x.2.val.length ≤ q) (hk : k ≤ q - x.2.val.length)
    (hne : ndReferencePrefixTransportAt q x.2.val hlen
      (fun v => g (Tao.taoZModThreeProjection hk v))
      (-(((root x.1.val : ℕ)) : ZMod (3 ^ q))) ≠ 0) :
    ∃ z : UnitChildIncidenceM Labels root b a K, selectedWordM z = x := by
  classical
  set w := x.2.val with hw
  set d := w.length with hd
  set t := q - d with ht
  have hevent := (mem_shiftedReferenceSelectedWords_iff b a K w).mp x.2.property
  set Y : ZMod (3 ^ q) := -(((root x.1.val : ℕ)) : ZMod (3 ^ q)) with hY
  set M0 : ℕ := Y.val with hM0
  have hM0cast : ((M0 : ℕ) : ZMod (3 ^ q)) = Y := by
    rw [hM0]; exact ZMod.natCast_zmod_val Y
  have hne' : ndReferencePrefixTransportAt q w hlen
      (fun v => g (Tao.taoZModThreeProjection hk v)) ((M0 : ℕ) : ZMod (3 ^ q)) ≠ 0 := by
    rw [hM0cast]; exact hne
  have hsum : (∑ v : ZMod (3 ^ t),
      if ndReferencePrefixParent d t w v = ((M0 : ℕ) : ZMod (3 ^ (t + d)))
      then g (Tao.taoZModThreeProjection hk v) else 0) ≠ 0 := by
    intro hh
    apply hne'
    rw [referencePrefixTransportAt_apply_natCast, referenceWordTransport_eq_sum]
    change (3 : ℝ) ^ d * (2 : ℝ) ^ (-(Tao.taoTupleWeight w : ℤ)) * _ = 0
    rw [hh, mul_zero]
  obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hp : ndReferencePrefixParent d t w v = ((M0 : ℕ) : ZMod (3 ^ (t + d))) := by
    by_contra hh
    simp [hh] at hv
  have hdq : d ≤ q := hlen
  have hM0d : ((M0 : ℕ) : ZMod (3 ^ d)) = -(((root x.1.val : ℕ)) : ZMod (3 ^ d)) := by
    have h1 := Tao.taoZModThreeProjection_natCast hdq M0
    have h2 := Tao.taoZModThreeProjection_natCast hdq (root x.1.val)
    rw [← h1, hM0cast, hY, map_neg, h2]
  have hoffset : Tao.taoSection7OffsetZMod d w = -(((root x.1.val : ℕ)) : ZMod (3 ^ d)) := by
    have hh := referencePrefixParent_projection d t w v
    rw [hp, Tao.taoZModThreeProjection_natCast] at hh
    rw [← hh, hM0d]
  set sdep : NDGeom2ShiftedWideSymmetricBoundedOvershootDepth b := ⟨d, hevent.1.1⟩ with hsdep
  set p : IncidenceM Label root (fun _ => b) (fun _ => a) K :=
    ⟨x.1.val, sdep, ⟨w, mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff.mpr
      ⟨rfl, hevent, hoffset⟩⟩⟩ with hpdef
  set N := sourceM p with hN
  have ha : taoAffListM w.reverse ((N : ℕ) : ℚ) = ((root x.1.val : ℕ) : ℚ) := by
    simpa only [chronologicalWordM, hpdef, hN] using (sourceM_odd_and_affine hrootOdd p).2
  have hu : IsUnit (-((N : ℕ) : ZMod (3 ^ 1))) := by
    by_contra hh
    apply hne
    have hnotN : ¬ IsUnit ((N : ℕ) : ZMod (3 ^ 1)) := by
      intro hc
      exact hh (IsUnit.neg hc)
    have hzero : g (-((N : ℕ) : ZMod (3 ^ k))) = 0 :=
      g_neg_eq_zero_of_not_isUnit hk1 g hunit N hnotN
    rw [transportAtM_apply_physical_source q k w hlen hk ha g, hzero, mul_zero]
  have hc : ndReversedPrefixAmbientChild d w (-((N : ℕ) : ZMod (3 ^ 1))) =
      -(((root x.1.val : ℕ)) : ZMod (3 ^ (1 + d))) :=
    (natCastM_eq_ambientChild_negDigit_of_affineM rfl ha).symm
  refine ⟨⟨x.1, sdep, ⟨-((N : ℕ) : ZMod (3 ^ 1)), hu⟩, ⟨w,
    mem_ndGeom2ShiftedWideSymmetricRootSideUnitChildWordFinset_iff.mpr ⟨rfl, hevent, hc⟩⟩⟩, ?_⟩
  apply Prod.ext <;> rfl

end ThreeXMinusOne
