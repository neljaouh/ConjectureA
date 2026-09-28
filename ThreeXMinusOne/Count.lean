import ThreeXMinusOne.Charge
import ThreeXMinusOne.Residue
import Erdos1135.ND.PositiveDensity.A5SupportedTargetCounting

/-!
# The counting core for `3x−1`, and the statement of M2 for `3x−1`

Layer 5 of the port: `GeneralTargetPredecessorCount.generalTarget_publicCount_from_mass`
distilled to the step it actually performs — turning a charge inequality plus a mass lower
bound into a lower bound on the predecessor count.

`count_ge_of_window_and_charge` is proved here from scratch and is sign-agnostic.  The point of
stating it separately is `count_ge_of_window_and_charge_inflated`: the `3x−1` charge inequality
proved in `Charge.lean` carries a factor `1 + δ`, and this makes explicit that **the entire
price of the sign reversal is that the density constant is divided by `1 + δ`** — no other part
of the counting argument is affected.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

/-- The `3x−1` predecessor set of `a`. -/
def predecessorSetM (a : ℕ) : Set ℕ := {n | 0 < n ∧ ReachesM n a}

def HasPositiveLowerDensity (s : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X → c * (X : ℝ) ≤ (Terras.natCount s X : ℝ)

/-- **Positive lower density of `3x−1` predecessors** (M2 for the `3x−1` map), stated exactly as
`CollatzPredecessorDensity.predecessors_positive_lower_density` states it for `3x+1`. -/
def PredecessorDensity : Prop :=
  ∀ a : ℕ, 0 < a → ¬ 3 ∣ a → HasPositiveLowerDensity (predecessorSetM a)

/-- **The counting core.**  A window of sources carrying total mass `η`, each charged at most
`rootv`, forces `η·X/rootv` predecessors below `Y`. -/
theorem count_ge_of_window_and_charge
    {a Y : ℕ} {S : Finset ℕ} {atom : ℕ → ℝ} {X η rootv : ℝ}
    (hX : 0 < X) (hrootv : 0 < rootv)
    (hatom : ∀ s ∈ S, 0 ≤ atom s)
    (hwin : ∀ s ∈ S, X ≤ (s : ℝ))
    (hlt : ∀ s ∈ S, (s : ℝ) < (Y : ℝ))
    (hmem : ∀ s ∈ S, 0 < s ∧ ReachesM s a)
    (hmass : η ≤ ∑ s ∈ S, atom s)
    (hcharge : ∀ s ∈ S, (s : ℝ) * atom s ≤ rootv) :
    η / rootv * X ≤ (Terras.natCount (predecessorSetM a) Y : ℝ) := by
  classical
  have hpoint : ∀ s ∈ S, atom s ≤ rootv / X := by
    intro s hs
    rw [le_div_iff₀ hX]
    nlinarith [hwin s hs, hatom s hs, hcharge s hs]
  have h1 : ∑ s ∈ S, atom s ≤ ∑ _s ∈ S, rootv / X := Finset.sum_le_sum hpoint
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : η ≤ (S.card : ℝ) * (rootv / X) := hmass.trans h1
  have h3 : η * X ≤ (S.card : ℝ) * rootv := by
    have := mul_le_mul_of_nonneg_right h2 hX.le
    calc η * X ≤ (S.card : ℝ) * (rootv / X) * X := this
      _ = (S.card : ℝ) * rootv := by field_simp
  have hrange : S ⊆ Finset.range Y := by
    intro s hs
    exact Finset.mem_range.mpr (by exact_mod_cast hlt s hs)
  have hsub : (↑S : Set ℕ) ⊆ predecessorSetM a := by
    intro s hs
    exact hmem s (by exact_mod_cast hs)
  have hcard : (S.card : ℝ) ≤ (Terras.natCount (predecessorSetM a) Y : ℝ) := by
    exact_mod_cast finset_card_le_natCount_of_subset_range hrange hsub
  have h4 : η / rootv * X ≤ (S.card : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hrootv]
    linarith
  linarith

/-- **The price of the sign reversal, isolated.**  With the inflated charge bound that
`Charge.lean` delivers for `3x−1`, the same argument runs and the constant is exactly
`1/(1+δ)` times the `3x+1` constant. -/
theorem count_ge_of_window_and_charge_inflated
    {a Y : ℕ} {S : Finset ℕ} {atom : ℕ → ℝ} {X η rootv δ : ℝ}
    (hX : 0 < X) (hrootv : 0 < rootv) (hδ : 0 ≤ δ)
    (hatom : ∀ s ∈ S, 0 ≤ atom s)
    (hwin : ∀ s ∈ S, X ≤ (s : ℝ))
    (hlt : ∀ s ∈ S, (s : ℝ) < (Y : ℝ))
    (hmem : ∀ s ∈ S, 0 < s ∧ ReachesM s a)
    (hmass : η ≤ ∑ s ∈ S, atom s)
    (hcharge : ∀ s ∈ S, (s : ℝ) * atom s ≤ (1 + δ) * rootv) :
    η / ((1 + δ) * rootv) * X ≤ (Terras.natCount (predecessorSetM a) Y : ℝ) :=
  count_ge_of_window_and_charge hX (by nlinarith) hatom hwin hlt hmem hmass hcharge

end

end ThreeXMinusOne
