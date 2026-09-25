import ThreeXMinusOne.CapOneCompression
import ThreeXMinusOne.TerminalCensus

/-!
# The cap-one fan bound

`ndPhysicalTerminalCompression` and `physical_terminal_depth_mark_le_cap_one_fan`, mirrored.

Layer 41 showed every cap-`K` incidence is a cap-one incidence raised by a fan index.  Choosing
that decomposition gives an injection from cap-`K` incidences into (cap-one incidences) ×
(fan indices), and since the atom scales by exactly `(1/4)^j` under the raise, any non-negative
weighted mark over cap-`K` incidences is dominated by the corresponding fanned sum over cap-one
ones.

This is what lets the whole argument be run at cap one, where the source window of Layer 39
applies, while the generational construction keeps its growing caps.

Nothing here is `3x−1`-specific beyond the objects: the proof is the `+1` proof with `sourceM`,
`atomM`, `weightM` and `sourceFanM` in place of their `+1` counterparts, and the injectivity comes
from Layer 18's `incidenceM_ext`.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

variable {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}

/-- The chosen cap-one decomposition. -/
def physicalTerminalCompressionM (hrootOdd : ∀ i, Odd (root i)) (hbase : ∀ i, 9 ≤ base i)
    (hroot : ∀ i, 16 ^ base i ≤ root i) (z : IncidenceM Label root base shift K) :
    IncidenceM Label root base shift 1 × Fin (K / 2 + 1) :=
  let h := exists_physical_terminal_cap_one_compressionM hrootOdd hbase hroot z
  ⟨h.choose, h.choose_spec.choose⟩

theorem physicalTerminalCompressionM_spec (hrootOdd : ∀ i, Odd (root i))
    (hbase : ∀ i, 9 ≤ base i) (hroot : ∀ i, 16 ^ base i ≤ root i)
    (z : IncidenceM Label root base shift K) :
    let p := physicalTerminalCompressionM hrootOdd hbase hroot z
    labelM z = labelM p.1 ∧ depthM z = depthM p.1 ∧
      rootSideWordM z = ndTerminalEvenRaise p.2.val (rootSideWordM p.1) ∧
      sourceM z = sourceFanM p.2.val (sourceM p.1) ∧
      atomM z = (1 / 4 : ℝ) ^ p.2.val * atomM p.1 :=
  (exists_physical_terminal_cap_one_compressionM hrootOdd hbase hroot z).choose_spec.choose_spec

theorem physicalTerminalCompressionM_injective (hrootOdd : ∀ i, Odd (root i))
    (hbase : ∀ i, 9 ≤ base i) (hroot : ∀ i, 16 ^ base i ≤ root i) :
    Function.Injective (physicalTerminalCompressionM (shift := shift) (K := K)
      hrootOdd hbase hroot) := by
  intro z w heq
  have hz := physicalTerminalCompressionM_spec hrootOdd hbase hroot z
  have hw := physicalTerminalCompressionM_spec hrootOdd hbase hroot w
  dsimp only at hz hw
  rw [heq] at hz
  exact incidenceM_ext (hz.1.trans hw.1.symm) (hz.2.1.trans hw.2.1.symm)
    (hz.2.2.1.trans hw.2.2.1.symm)

theorem physicalTerminalCompressionM_weighted_mark (hrootOdd : ∀ i, Odd (root i))
    (hbase : ∀ i, 9 ≤ base i) (hroot : ∀ i, 16 ^ base i ≤ root i)
    (outerWeight : Label → ℝ) (g : ℕ → ℝ) (z : IncidenceM Label root base shift K) :
    let p := physicalTerminalCompressionM hrootOdd hbase hroot z
    weightM outerWeight z * g (sourceM z) =
      weightM outerWeight p.1 *
        ((1 / 4 : ℝ) ^ p.2.val * g (sourceFanM p.2.val (sourceM p.1))) := by
  have h := physicalTerminalCompressionM_spec hrootOdd hbase hroot z
  dsimp only
  unfold weightM
  rw [h.1, h.2.2.2.1, h.2.2.2.2]
  ring

/-- **The cap-one fan bound.** -/
theorem physical_terminal_depth_mark_le_cap_one_fanM [Fintype Label]
    (hrootOdd : ∀ i, Odd (root i)) (hbase : ∀ i, 9 ≤ base i)
    (hroot : ∀ i, 16 ^ base i ≤ root i)
    (outerWeight : Label → ℝ) (hw : ∀ i, 0 ≤ outerWeight i)
    (psi : Label → ℕ → ℝ) (hpsi : ∀ i s, 0 ≤ psi i s)
    (g : ℕ → ℝ) (hg : ∀ x, 0 ≤ g x) :
    (∑ z : IncidenceM Label root base shift K,
      weightM outerWeight z * psi (labelM z) (depthM z) * g (sourceM z)) ≤
    ∑ z0 : IncidenceM Label root base shift 1,
      (weightM outerWeight z0 * psi (labelM z0) (depthM z0)) *
        ∑ j : Fin (K / 2 + 1), (1 / 4 : ℝ) ^ j.val * g (sourceFanM j.val (sourceM z0)) := by
  classical
  set f := physicalTerminalCompressionM (shift := shift) (K := K) hrootOdd hbase hroot with hf
  set G : (IncidenceM Label root base shift 1 × Fin (K / 2 + 1)) → ℝ := fun p =>
    (weightM outerWeight p.1 * psi (labelM p.1) (depthM p.1)) *
      ((1 / 4 : ℝ) ^ p.2.val * g (sourceFanM p.2.val (sourceM p.1))) with hG
  have hGnn : ∀ p, 0 ≤ G p := by
    intro p
    exact mul_nonneg (mul_nonneg (weightM_nonneg outerWeight hw p.1) (hpsi _ _))
      (mul_nonneg (by positivity) (hg _))
  calc (∑ z : IncidenceM Label root base shift K,
        weightM outerWeight z * psi (labelM z) (depthM z) * g (sourceM z))
      = ∑ z, G (f z) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        have hs := physicalTerminalCompressionM_spec hrootOdd hbase hroot z
        have ht := physicalTerminalCompressionM_weighted_mark hrootOdd hbase hroot
          outerWeight g z
        dsimp only at hs ht
        dsimp only [G, f]
        calc weightM outerWeight z * psi (labelM z) (depthM z) * g (sourceM z)
            = psi (labelM z) (depthM z) * (weightM outerWeight z * g (sourceM z)) := by ring
          _ = _ := by rw [ht, hs.1, hs.2.1]; ring
    _ = ∑ p ∈ Finset.univ.image f, G p :=
        (Finset.sum_image fun z _ w _ h =>
          physicalTerminalCompressionM_injective hrootOdd hbase hroot h).symm
    _ ≤ ∑ p, G p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => hGnn p)
    _ = _ := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun z0 _ => ?_
        dsimp [G]
        rw [Finset.mul_sum]

end

end ThreeXMinusOne
