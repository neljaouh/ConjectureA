import ThreeXMinusOne.CapOneFan

/-!
# From singleton unit children to physical incidences

`ndTerminalUnitPhysicalMap` and `singleton_unit_terminal_depth_mark_le_physical`, mirrored.

The generational construction produces *unit-child* incidences, one packet per parent label; the
cap-one fan bound of Layer 42 is stated for *physical* incidences over the whole label type.
This is the injection between them: a unit child of the singleton `{i}` is a physical incidence
at `i`, via Layer 14's `toPhysicalM`, and distinct unit children give distinct physical
incidences by Layer 21.

Every projection is `rfl` — `toPhysicalM` was defined so that label, depth, word, source and
weight all agree on the nose.  That was a design choice at Layer 14 and it pays here.

**One deviation from the `+1` statement, forced by elaboration.**  The `+1` lemma sums over
`i` and then over that label's packet, and converts to a `Σ`-sum with `Fintype.sum_sigma`.
Inside this proof that conversion does not elaborate: it times out in `whnf`, and raising
`maxHeartbeats` from 200000 to 4000000 does not help.  Bisecting the file located it — the map,
its spec and its injectivity are all fine.

**Correction.**  I first recorded the cause as `Fintype.sum_sigma` forcing the Sigma instance
through the fibre's `noncomputable Fintype.ofFinset`.  That is wrong: `SigmaBridge` states
exactly that conversion for exactly these packets and it elaborates without trouble.  So the
timeout comes from the *interaction* — `Fintype.sum_sigma` inside a `calc` whose summand must
simultaneously be unified against `G (f z)` for the compression map `f` — and not from the
instance on its own.  I had asserted a cause I had not isolated; isolating it took one small
file.

So this is stated over the `Σ` type directly.  Nothing is lost: the sum a consumer wants *is*
the `Σ`-sum, and the double-sum form can be recovered at a use site where the instance can be
supplied explicitly.
-/

set_option maxHeartbeats 1000000

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

variable {Label : Type*} [DecidableEq Label] {root shift : Label → ℕ} {b K : ℕ}

/-- A unit child of `{i}` as a physical incidence at `i`. -/
def terminalUnitPhysicalMapM (root shift : Label → ℕ) (b K : ℕ)
    (z : Σ i : Label, UnitChildIncidenceM ({i} : Finset Label) root b (shift i) K) :
    IncidenceM Label root (fun _ => b) shift K := by
  rcases z with ⟨i, ⟨⟨j, hj⟩, s, u, w⟩⟩
  have hji : j = i := Finset.mem_singleton.mp hj
  subst j
  exact ⟨i, s, (toPhysicalM (⟨⟨i, hj⟩, s, u, w⟩ :
    UnitChildIncidenceM ({i} : Finset Label) root b (shift i) K)).2.2⟩

theorem terminalUnitPhysicalMapM_spec (root shift : Label → ℕ) (b K : ℕ)
    (z : Σ i : Label, UnitChildIncidenceM ({i} : Finset Label) root b (shift i) K) :
    labelM (terminalUnitPhysicalMapM root shift b K z) = z.1 ∧
    depthM (terminalUnitPhysicalMapM root shift b K z) = ucDepthM z.2 ∧
    rootSideWordM (terminalUnitPhysicalMapM root shift b K z) = ucWordM z.2 ∧
    sourceM (terminalUnitPhysicalMapM root shift b K z) = ucSourceM z.2 ∧
    ∀ outerWeight : Label → ℝ,
      weightM outerWeight (terminalUnitPhysicalMapM root shift b K z) =
        ucWeightM outerWeight z.2 := by
  rcases z with ⟨i, ⟨⟨j, hj⟩, s, u, w⟩⟩
  have hji : j = i := Finset.mem_singleton.mp hj
  subst j
  refine ⟨rfl, rfl, rfl, rfl, fun ow => ?_⟩
  simp only [weightM, ucWeightM, ucAtomM, atomM]
  rfl

theorem terminalUnitPhysicalMapM_injective (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hroot : ∀ i, 16 ^ b ≤ root i) :
    Function.Injective (terminalUnitPhysicalMapM root shift b K) := by
  rintro ⟨i, z⟩ ⟨j, w⟩ heq
  have hz := terminalUnitPhysicalMapM_spec root shift b K ⟨i, z⟩
  have hw := terminalUnitPhysicalMapM_spec root shift b K ⟨j, w⟩
  dsimp only at hz hw
  have hij : i = j := by rw [← hz.1, ← hw.1, heq]
  subst hij
  have hl : ucLabelM z = ucLabelM w :=
    (Finset.mem_singleton.mp z.1.2).trans (Finset.mem_singleton.mp w.1.2).symm
  have hd : ucDepthM z = ucDepthM w := by rw [← hz.2.1, ← hw.2.1, heq]
  have hwd : ucWordM z = ucWordM w := by rw [← hz.2.2.1, ← hw.2.2.1, heq]
  have hzw : z = w :=
    toPhysicalM_injective hrootOdd hb hroot
      (incidenceM_ext (by simpa only [toPhysicalM_label] using hl)
        (by simpa only [toPhysicalM_depth] using hd)
        (by simpa only [toPhysicalM_word] using hwd))
  exact congrArg (Sigma.mk i) hzw


set_option maxHeartbeats 1000000 in
/-- **The packet sum is dominated by the physical sum.** -/
theorem singleton_unit_terminal_depth_mark_le_physicalM [Fintype Label]
    (root shift : Label → ℕ) (b K : ℕ)
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b) (hroot : ∀ i, 16 ^ b ≤ root i)
    (outerWeight : Label → ℝ) (hw : ∀ i, 0 ≤ outerWeight i)
    (psi : Label → ℕ → ℝ) (hpsi : ∀ i s, 0 ≤ psi i s)
    (g : ℕ → ℝ) (hg : ∀ x, 0 ≤ g x) :
    (∑ z : Σ i : Label, UnitChildIncidenceM ({i} : Finset Label) root b (shift i) K,
      ucWeightM outerWeight z.2 * psi z.1 (ucDepthM z.2) * g (ucSourceM z.2)) ≤
    ∑ z : IncidenceM Label root (fun _ => b) shift K,
      weightM outerWeight z * psi (labelM z) (depthM z) * g (sourceM z) := by
  classical
  set f := terminalUnitPhysicalMapM root shift b K with hf
  set G : IncidenceM Label root (fun _ => b) shift K → ℝ := fun z =>
    weightM outerWeight z * psi (labelM z) (depthM z) * g (sourceM z) with hG
  have hGnn : ∀ z, 0 ≤ G z := fun z =>
    mul_nonneg (mul_nonneg (weightM_nonneg outerWeight hw z) (hpsi _ _)) (hg _)
  calc (∑ z : Σ i : Label, UnitChildIncidenceM ({i} : Finset Label) root b (shift i) K,
        ucWeightM outerWeight z.2 * psi z.1 (ucDepthM z.2) * g (ucSourceM z.2))
      = ∑ z, G (f z) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        have h := terminalUnitPhysicalMapM_spec root shift b K z
        dsimp only [G, f]
        rw [h.1, h.2.1, h.2.2.2.1, h.2.2.2.2 outerWeight]
    _ = ∑ z ∈ Finset.univ.image f, G z :=
        (Finset.sum_image fun z _ w _ h =>
          terminalUnitPhysicalMapM_injective hrootOdd hb hroot h).symm
    _ ≤ ∑ z, G z :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun z _ _ => hGnn z)

end

end ThreeXMinusOne
