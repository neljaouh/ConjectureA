import ThreeXMinusOne.Incidence
import ThreeXMinusOne.Count

/-!
# Sources of the `3x−1` reverse tree are predecessors of the target

The minus analogue of `fullTerminal_reaches_target_of_seed_reaches`, at the incidence level:
Layer 7 gives `syrM^[depth] source = root`, and `Map.reachesM_syrM_iterate` turns accelerated
steps into ordinary `3x−1` steps, so every incidence source is a genuine `colM`-predecessor of
whatever the root reaches.  Together with the unconditional charge bound this supplies two of the
three hypotheses of `Count.count_ge_of_window_and_charge`.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

variable {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}

theorem sourceM_pos (hrootOdd : ∀ i, Odd (root i))
    (z : IncidenceM Label root base shift K) : 0 < sourceM z :=
  (sourceM_odd hrootOdd z).pos

/-- A source reaches whatever its root reaches, under the ordinary `3x−1` map. -/
theorem sourceM_reachesM_of_root_reachesM (hrootOdd : ∀ i, Odd (root i)) {a : ℕ}
    (hreach : ∀ i, ReachesM (root i) a) (z : IncidenceM Label root base shift K) :
    ReachesM (sourceM z) a := by
  have h1 : ReachesM (sourceM z) ((syrM^[depthM z]) (sourceM z)) :=
    reachesM_syrM_iterate (sourceM_odd hrootOdd z) (depthM z)
  rw [sourceM_iterate hrootOdd z] at h1
  exact h1.trans (hreach _)

/-- Incidence sources are members of the `3x−1` predecessor set of the target. -/
theorem sourceM_mem_predecessorSetM (hrootOdd : ∀ i, Odd (root i)) {a : ℕ}
    (hreach : ∀ i, ReachesM (root i) a) (z : IncidenceM Label root base shift K) :
    sourceM z ∈ predecessorSetM a :=
  ⟨sourceM_pos hrootOdd z, sourceM_reachesM_of_root_reachesM hrootOdd hreach z⟩

end ThreeXMinusOne
