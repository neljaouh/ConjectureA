import CollatzPredecessorDensity

/-!
# Applegate–Lagarias Conjecture A, discharged against the M2 artifact

This file lives **inside the ProofAtlas M1+M2 tree**, so `MazurM2` is not a hypothesis here:
`CollatzPredecessorDensity.predecessors_positive_lower_density` is available as a theorem, and
Conjecture A is derived from it with no hypothesis of its own.

## The statement

Applegate–Lagarias, Part I §1, verbatim from the authors' preprint, immediately after (1.2):

> `(1.2)  π_a(x) = #{n : |n| ≤ x and some T^(k)(n) = a , k ≥ 0}`
>
> **Conjecture A.** For each `a ≢ 0 (mod 3)`, there is a positive constant `c_a` such that
> `π_a(x) ≥ c_a x` for all `x ≥ |a|`.

with `T` the **accelerated** map of (1.1): `x/2` on evens, `(3x+1)/2` on odds. The artifact's
theorem is about the **ordinary** map, and the two predecessor sets differ exactly on
`a ≡ 4 (mod 6)` — so the derivation below is not a relabelling.

## Scope, stated honestly

`conjectureA` below is Conjecture A **for positive targets**. AL quantify over `a ∈ ℤ`; the
negative case is Conjecture A for `3x−1`, a different dynamical system that the artifact says
nothing about. Nothing here closes that.

And this file inherits the artifact's status: the artifact is **unreviewed, AI-assisted** work.
A clean build establishes that its proof term type-checks, not that its mathematics is sound.
-/

namespace ALConjectureA

open Erdos1135

/-- The **accelerated** map `T` of Applegate–Lagarias (1.1). -/
def syr (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

def reachesSyr (n a : ℕ) : Prop := ∃ k : ℕ, syr^[k] n = a

/-- AL's `π_a(x)`, as (1.2), over positive `n < X`. -/
noncomputable def piA (a X : ℕ) : ℕ :=
  Terras.natCount {n : ℕ | 0 < n ∧ reachesSyr n a} X

/-- **Conjecture A** for positive targets. -/
def ConjectureA : Prop :=
  ∀ a : ℕ, 0 < a → ¬ 3 ∣ a →
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → c * X ≤ (piA a X : ℝ)

/-! ### One accelerated step is one or two ordinary steps -/

theorem collatzStep_even {n : ℕ} (he : Even n) : collatzStep n = n / 2 := by
  simp [collatzStep, CollatzConjecture.collatzStep, he]

theorem collatzStep_odd {n : ℕ} (ho : ¬ Even n) : collatzStep n = 3 * n + 1 := by
  simp [collatzStep, CollatzConjecture.collatzStep, ho]

theorem syr_even {n : ℕ} (h : n % 2 = 0) : syr n = collatzStep n := by
  have he : Even n := Nat.even_iff.mpr h
  rw [collatzStep_even he]
  simp [syr, h]

theorem syr_odd {n : ℕ} (h : n % 2 = 1) : syr n = collatzStep (collatzStep n) := by
  have ho : ¬ Even n := by rw [Nat.even_iff]; omega
  have he2 : Even (3 * n + 1) := by rw [Nat.even_iff]; omega
  rw [collatzStep_odd ho, collatzStep_even he2]
  simp [syr, show ¬ n % 2 = 0 by omega]

theorem reachesSyr_to_reaches {n a : ℕ} (h : reachesSyr n a) : Reaches n a := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing n with
  | zero => exact ⟨0, hk⟩
  | succ k ih =>
      rw [Function.iterate_succ_apply] at hk
      obtain ⟨t, ht⟩ := ih hk
      by_cases hp : n % 2 = 0
      · exact ⟨t + 1, by rw [Function.iterate_add_apply, Function.iterate_one,
          ← syr_even hp, ht]⟩
      · refine ⟨t + 2, ?_⟩
        rw [Function.iterate_add_apply, Function.iterate_succ_apply,
          Function.iterate_one, ← syr_odd (by omega), ht]

/-- A value entered by the odd rule is `3m+1` with `m` odd, hence `≡ 4 (mod 6)`. -/
theorem odd_step_mod_six {m : ℕ} (h : m % 2 = 1) : (3 * m + 1) % 6 = 4 := by omega

/-- **The load-bearing lemma.** For `a ≢ 4 (mod 6)` the two predecessor notions coincide. -/
theorem reaches_to_reachesSyr {a : ℕ} (ha : a % 6 ≠ 4) :
    ∀ (t n : ℕ), collatzStep^[t] n = a → reachesSyr n a := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro n hn
    match t with
    | 0 => exact ⟨0, hn⟩
    | (t + 1) =>
      rw [Function.iterate_succ_apply] at hn
      by_cases hp : n % 2 = 0
      · obtain ⟨k, hk⟩ := ih t (by omega) (collatzStep n) hn
        exact ⟨k + 1, by rw [Function.iterate_add_apply, Function.iterate_one,
          syr_even hp, hk]⟩
      · have hodd : n % 2 = 1 := by omega
        have ho : ¬ Even n := by rw [Nat.even_iff]; omega
        have hcol : collatzStep n = 3 * n + 1 := collatzStep_odd ho
        match t with
        | 0 =>
            rw [Function.iterate_zero_apply, hcol] at hn
            exact absurd (hn ▸ odd_step_mod_six hodd) ha
        | (s + 1) =>
            rw [Function.iterate_succ_apply] at hn
            rw [← syr_odd hodd] at hn
            obtain ⟨k, hk⟩ := ih s (by omega) (syr n) hn
            exact ⟨k + 1, by rw [Function.iterate_add_apply, Function.iterate_one, hk]⟩

theorem reachesSyr_iff {n a : ℕ} (ha : a % 6 ≠ 4) : reachesSyr n a ↔ Reaches n a :=
  ⟨reachesSyr_to_reaches, fun ⟨t, ht⟩ => reaches_to_reachesSyr ha t n ht⟩

/-- `syr (2a) = a`, so anything reaching `2a` reaches `a`. -/
theorem reachesSyr_two_mul {n a : ℕ} (h : reachesSyr n (2 * a)) : reachesSyr n a := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  rw [Function.iterate_succ_apply', hk]
  have h2 : (2 * a) % 2 = 0 := by omega
  simp only [syr, if_pos h2]
  omega

theorem two_mul_mod_six {a : ℕ} (h : a % 6 = 4) : (2 * a) % 6 ≠ 4 := by
  have : (2 * a) % 6 = 2 := by omega
  omega

/-! ### The monotone step: `natCount` of a subset -/

theorem natCount_mono {s t : Set ℕ} (h : s ⊆ t) (X : ℕ) :
    Terras.natCount s X ≤ Terras.natCount t X := by
  classical
  unfold Terras.natCount
  simp only [Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  exact ⟨hk.1, h hk.2⟩

/-- **Conjecture A for positive targets, discharged against the artifact.**

No hypothesis: `predecessors_positive_lower_density` is a theorem in this tree.

* `a ≢ 4 (mod 6)` — the accelerated and ordinary predecessor sets coincide, so the artifact's
  statement at `a` *is* Conjecture A at `a`.
* `a ≡ 4 (mod 6)` — they do not coincide, and the artifact's count is the larger one, so it
  does not transfer. But `syr (2a) = a` gives `π_a ≥ π_{2a}`, and `2a ≢ 4 (mod 6)`, so the
  artifact at `2a` transfers instead. -/
theorem conjectureA : ConjectureA := by
  intro a ha h3
  by_cases hmod : a % 6 = 4
  · -- bridge case
    have h3' : ¬ 3 ∣ 2 * a := by omega
    have ha' : 0 < 2 * a := by omega
    obtain ⟨c, hc, X₀, hX₀⟩ :=
      CollatzPredecessorDensity.predecessors_positive_lower_density ha' h3'
    refine ⟨c, hc, X₀, fun X hX => le_trans (hX₀ X hX) ?_⟩
    have hsub : {n : ℕ | 0 < n ∧ Reaches n (2 * a)} ⊆ {n : ℕ | 0 < n ∧ reachesSyr n a} := by
      intro k hk
      exact ⟨hk.1, reachesSyr_two_mul ((reachesSyr_iff (two_mul_mod_six hmod)).2 hk.2)⟩
    exact_mod_cast natCount_mono hsub X
  · -- direct case
    obtain ⟨c, hc, X₀, hX₀⟩ :=
      CollatzPredecessorDensity.predecessors_positive_lower_density ha h3
    refine ⟨c, hc, X₀, fun X hX => le_trans (hX₀ X hX) ?_⟩
    have hsub : {n : ℕ | 0 < n ∧ Reaches n a} ⊆ {n : ℕ | 0 < n ∧ reachesSyr n a} := by
      intro k hk
      exact ⟨hk.1, (reachesSyr_iff hmod).2 hk.2⟩
    exact_mod_cast natCount_mono hsub X

end ALConjectureA

set_option pp.fullNames true
#print axioms ALConjectureA.reaches_to_reachesSyr
#print axioms ALConjectureA.reachesSyr_iff
#print axioms ALConjectureA.conjectureA
