import ConjectureA
import ThreeXMinusOne.PositiveDensity

/-!
# Conjecture A over `ℤ`

Applegate–Lagarias state Conjecture A for `a ∈ ℤ`.  `ALConjectureA.conjectureA` proves it for
positive targets only; its own "Scope" note says the negative case is Conjecture A for `3x−1`.

That map is no longer outside the tree: `ThreeXMinusOne.mazurM2Neg` proves M2 for it.  This file
is the assembly.  Nothing here is deep — it is the conjugation `n ↦ −n`, a `ℕ → ℤ` cast, and the
two counting injections — but without it the `ℤ` statement has no proof term.

Three things had to be supplied that no file contained:

* the `ℕ → ℤ` cast for the **accelerated** map, so the positive half can be read at `ℤ`-shaped
  targets (`syrZ_natCast`);
* the `a ≡ 4 (mod 6)` case on the negative side.  `ThreeXMinusOne.mazurM2Neg` counts *ordinary*
  `3x−1` predecessors, and ordinary and accelerated reachability part company exactly at
  `4 (mod 6)`.  The positive file dodges this with `syr (2a) = a`; the same dodge works here
  because `syrZ (2A) = A`, and `A % 6 = 4 → (2A) % 6 ≠ 4` (`two_mul_mod_six_Z`).  Both lemmas
  already existed and were unused;
* the sign split at top level, which is where `natAbs` enters.

The result, `conjectureAZ`, is unconditional.
-/

namespace ALConjectureAZ

open Classical
open Erdos1135

/-! ## 1. The maps on `ℤ` -/

/-- The ordinary Collatz map on `ℤ`. -/
def colZ (n : ℤ) : ℤ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The **accelerated** map `T` of Applegate–Lagarias (1.1), on `ℤ`. -/
def syrZ (n : ℤ) : ℤ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

def reachesZ (n a : ℤ) : Prop := ∃ k : ℕ, colZ^[k] n = a
def reachesSyrZ (n a : ℤ) : Prop := ∃ k : ℕ, syrZ^[k] n = a

/-! ## 2. Negation conjugates the negative dynamics onto `3x−1`

`ThreeXMinusOne.colM` is the ordinary `3x−1` map on `ℕ`; this is the conjugacy that makes
`mazurM2Neg` a statement about negative Collatz targets. -/

/-- `colZ (−m) = −(colM m)` for `m ≥ 1`: the defining conjugation. -/
theorem neg_colZ {m : ℕ} (hm : 1 ≤ m) :
    colZ (-(m : ℤ)) = -((ThreeXMinusOne.colM m : ℕ) : ℤ) := by
  rcases Nat.even_or_odd m with he | ho
  · have h2 : m % 2 = 0 := Nat.even_iff.mp he
    have hz : (-(m : ℤ)) % 2 = 0 := by omega
    simp only [colZ, ThreeXMinusOne.colM, if_pos hz, if_pos h2]
    omega
  · have h2 : m % 2 = 1 := Nat.odd_iff.mp ho
    have hz : ¬ (-(m : ℤ)) % 2 = 0 := by omega
    have h2' : ¬ m % 2 = 0 := by omega
    simp only [colZ, ThreeXMinusOne.colM, if_neg hz, if_neg h2']
    omega

/-- One `3x−1` step keeps a positive integer positive. -/
theorem colM_step_pos {x : ℕ} (hx : 1 ≤ x) : 1 ≤ ThreeXMinusOne.colM x := by
  unfold ThreeXMinusOne.colM; split_ifs with hp <;> omega

/-- The `3x−1` orbit of a positive integer stays positive. -/
theorem colM_pos {m : ℕ} (hm : 1 ≤ m) : ∀ j : ℕ, 1 ≤ ThreeXMinusOne.colM^[j] m := by
  intro j
  induction j with
  | zero => simpa using hm
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact colM_step_pos ih

theorem colZ_iterate_neg {m : ℕ} (hm : 1 ≤ m) :
    ∀ k : ℕ, colZ^[k] (-(m : ℤ)) = -((ThreeXMinusOne.colM^[k] m : ℕ) : ℤ) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact neg_colZ (colM_pos hm k)

/-- **The reduction**: reaching a negative target is reaching the corresponding `3x−1` target. -/
theorem reachesZ_neg_of_reachesM {m a : ℕ} (hm : 1 ≤ m) (h : ThreeXMinusOne.ReachesM m a) :
    reachesZ (-(m : ℤ)) (-(a : ℤ)) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [colZ_iterate_neg hm k, hk]⟩

/-! ## 3. Sign preservation

Not needed for the bound — the injections below are one-sided — but it records that the
`m ↦ −m` image is *all* of the predecessor set of a negative target, not merely part of it. -/

theorem colZ_neg {n : ℤ} (h : n < 0) : colZ n < 0 := by
  unfold colZ; split_ifs with hp <;> omega

theorem colZ_pos {n : ℤ} (h : 0 < n) : 0 < colZ n := by
  unfold colZ; split_ifs with hp <;> omega

/-- `colZ` preserves sign, so a negative target has only negative predecessors. -/
theorem sign_preserved {n a : ℤ} (h : reachesZ n a) (ha : a < 0) : n < 0 := by
  obtain ⟨k, hk⟩ := h
  by_contra hn
  push_neg at hn
  rcases eq_or_lt_of_le hn with h0 | hpos
  · have : ∀ j : ℕ, colZ^[j] n = 0 := by
      intro j
      induction j with
      | zero => simpa using h0.symm
      | succ j ih =>
          rw [Function.iterate_succ_apply', ih]
          unfold colZ; norm_num
    rw [this k] at hk; omega
  · have hp : ∀ j : ℕ, 0 < colZ^[j] n := by
      intro j
      induction j with
      | zero => simpa using hpos
      | succ j ih => rw [Function.iterate_succ_apply']; exact colZ_pos ih
    have := hp k; omega

/-! ## 4. The accelerated/ordinary bridge, over `ℤ` -/

theorem syrZ_even {n : ℤ} (h : n % 2 = 0) : syrZ n = colZ n := by
  simp only [syrZ, colZ, if_pos h]

theorem syrZ_odd {n : ℤ} (h : ¬ n % 2 = 0) : syrZ n = colZ (colZ n) := by
  have h1 : colZ n = 3 * n + 1 := by simp only [colZ, if_neg h]
  have h2 : (3 * n + 1) % 2 = 0 := by omega
  rw [syrZ, if_neg h, h1, colZ, if_pos h2]

/-- A value entered by the odd rule is `3m+1` with `m` odd, hence `≡ 4 (mod 6)`.
`Int.emod` is non-negative, so this is the same residue for negative `m`. -/
theorem odd_step_mod_six_Z {m : ℤ} (h : ¬ m % 2 = 0) : (3 * m + 1) % 6 = 4 := by omega

theorem reachesSyrZ_to_reachesZ {n a : ℤ} (h : reachesSyrZ n a) : reachesZ n a := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing n with
  | zero => exact ⟨0, hk⟩
  | succ k ih =>
      rw [Function.iterate_succ_apply] at hk
      obtain ⟨t, ht⟩ := ih hk
      by_cases hp : n % 2 = 0
      · exact ⟨t + 1, by rw [Function.iterate_add_apply, Function.iterate_one,
          ← syrZ_even hp, ht]⟩
      · refine ⟨t + 2, ?_⟩
        rw [Function.iterate_add_apply, Function.iterate_succ_apply,
          Function.iterate_one, ← syrZ_odd hp, ht]

/-- **The load-bearing lemma, over `ℤ`.** For `a ≢ 4 (mod 6)`, ordinary reachability implies
accelerated reachability. -/
theorem reachesZ_to_reachesSyrZ {a : ℤ} (ha : a % 6 ≠ 4) :
    ∀ (t : ℕ) (n : ℤ), colZ^[t] n = a → reachesSyrZ n a := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro n hn
    match t with
    | 0 => exact ⟨0, hn⟩
    | (t + 1) =>
      rw [Function.iterate_succ_apply] at hn
      by_cases hp : n % 2 = 0
      · obtain ⟨k, hk⟩ := ih t (by omega) (colZ n) hn
        exact ⟨k + 1, by rw [Function.iterate_add_apply, Function.iterate_one,
          syrZ_even hp, hk]⟩
      · have hcol : colZ n = 3 * n + 1 := by simp only [colZ, if_neg hp]
        match t with
        | 0 =>
            rw [Function.iterate_zero_apply, hcol] at hn
            exact absurd (hn ▸ odd_step_mod_six_Z hp) ha
        | (s + 1) =>
            rw [Function.iterate_succ_apply] at hn
            rw [← syrZ_odd hp] at hn
            obtain ⟨k, hk⟩ := ih s (by omega) (syrZ n) hn
            exact ⟨k + 1, by rw [Function.iterate_add_apply, Function.iterate_one, hk]⟩

theorem reachesSyrZ_iff {n a : ℤ} (ha : a % 6 ≠ 4) : reachesSyrZ n a ↔ reachesZ n a :=
  ⟨reachesSyrZ_to_reachesZ, fun ⟨t, ht⟩ => reachesZ_to_reachesSyrZ ha t n ht⟩

/-- `syrZ (2a) = a`, so anything reaching `2a` reaches `a`. -/
theorem reachesSyrZ_two_mul {n a : ℤ} (h : reachesSyrZ n (2 * a)) : reachesSyrZ n a := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  rw [Function.iterate_succ_apply', hk]
  have h2 : (2 * a) % 2 = 0 := by omega
  simp only [syrZ, if_pos h2]
  omega

theorem two_mul_mod_six_Z {a : ℤ} (h : a % 6 = 4) : (2 * a) % 6 ≠ 4 := by omega

/-! ## 5. The `ℕ → ℤ` cast for the accelerated map

The positive half of Conjecture A is proved at `ℕ`-shaped targets against `ALConjectureA.syr`.
Casting it to `ℤ` needs `syrZ` and `syr` to agree on `ℕ`, which no file recorded. -/

theorem syrZ_natCast (n : ℕ) : syrZ (n : ℤ) = ((ALConjectureA.syr n : ℕ) : ℤ) := by
  by_cases h : n % 2 = 0
  · have hz : (n : ℤ) % 2 = 0 := by omega
    simp only [syrZ, if_pos hz, ALConjectureA.syr, if_pos h]
    omega
  · have hz : ¬ ((n : ℤ) % 2 = 0) := by omega
    simp only [syrZ, if_neg hz, ALConjectureA.syr, if_neg h]
    omega

theorem syrZ_iterate_natCast (n : ℕ) :
    ∀ k : ℕ, syrZ^[k] (n : ℤ) = ((ALConjectureA.syr^[k] n : ℕ) : ℤ) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, syrZ_natCast]

theorem reachesSyrZ_of_reachesSyr {n a : ℕ} (h : ALConjectureA.reachesSyr n a) :
    reachesSyrZ (n : ℤ) (a : ℤ) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [syrZ_iterate_natCast n k, hk]⟩

/-! ## 6. Conjecture A over `ℤ` -/

/-- AL's `π_a(x)` over `ℤ`, as (1.2): nonzero `n` with `|n| ≤ x` reaching `a`. -/
noncomputable def piAZ (a : ℤ) (x : ℕ) : ℕ :=
  ((Finset.Icc (-(x : ℤ)) (x : ℤ)).filter (fun n => n ≠ 0 ∧ reachesSyrZ n a)).card

/-- **Conjecture A**, over the integers, as Applegate–Lagarias print it. -/
def ConjectureAZ : Prop :=
  ∀ a : ℤ, ¬ (3 ∣ a) →
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → c * x ≤ (piAZ a x : ℝ)

theorem piAZ_mono {a b : ℤ} (h : ∀ n : ℤ, reachesSyrZ n a → reachesSyrZ n b) (x : ℕ) :
    piAZ a x ≤ piAZ b x := by
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1, h n hn.2.2⟩

/-! ## 7. The two counting injections

Both `ALConjectureA.piA` and `ThreeXMinusOne.MazurM2Neg` count with `Terras.natCount`, which is
`Nat.count` at a classical instance; `piAZ` is a `Finset.card`.  This is the bridge. -/

theorem natCount_eq_card_filter (s : Set ℕ) (X : ℕ) [DecidablePred (fun n => n ∈ s)] :
    Terras.natCount s X = ((Finset.range X).filter (fun n => n ∈ s)).card := by
  rw [Terras.natCount_eq_count s X, Nat.count_eq_card_filter_range]

/-- Positive targets: `n ↦ (n : ℤ)` embeds the `ℕ` predecessor count into the `ℤ` one. -/
theorem piA_le_piAZ (a X : ℕ) : ALConjectureA.piA a X ≤ piAZ (a : ℤ) X := by
  unfold ALConjectureA.piA
  rw [natCount_eq_card_filter]
  refine Finset.card_le_card_of_injOn (fun m : ℕ => (m : ℤ)) ?_ ?_
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq] at hm
    obtain ⟨hmX, hm0, hreach⟩ := hm
    show (m : ℤ) ∈ _
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega, ?_⟩)
    exact reachesSyrZ_of_reachesSyr hreach
  · intro x _ y _ h
    have h' : (x : ℤ) = (y : ℤ) := h
    omega

/-- Negative targets: `m ↦ −(m : ℤ)` embeds the `3x−1` count into the `ℤ` one. -/
theorem natCountM_le_piAZ {a : ℕ} (ha : 0 < a) (hmod : (-(a : ℤ)) % 6 ≠ 4) (X : ℕ) :
    Terras.natCount (ThreeXMinusOne.predecessorSetM a) X ≤ piAZ (-(a : ℤ)) X := by
  rw [natCount_eq_card_filter]
  refine Finset.card_le_card_of_injOn (fun m : ℕ => -(m : ℤ)) ?_ ?_
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hmX, hm0, hreach⟩ := hm
    show (-(m : ℤ)) ∈ _
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega, ?_⟩)
    exact (reachesSyrZ_iff hmod).2 (reachesZ_neg_of_reachesM hm0 hreach)
  · intro x _ y _ h
    have h' : (-(x : ℤ)) = (-(y : ℤ)) := h
    omega

/-! ## 8. The two halves -/

/-- **Positive targets.**  Unconditional: `ALConjectureA.conjectureA` is a theorem in this tree. -/
theorem conjectureAZ_pos (a : ℕ) (ha : 0 < a) (h3 : ¬ 3 ∣ a) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → c * x ≤ (piAZ (a : ℤ) x : ℝ) := by
  obtain ⟨c, hc, X₀, hX₀⟩ := ALConjectureA.conjectureA a ha h3
  refine ⟨c, hc, X₀, fun x hx => le_trans (hX₀ x hx) ?_⟩
  exact_mod_cast piA_le_piAZ a x

/-- **Negative targets, from M2 for `3x−1`.**

The `≡ 4 (mod 6)` case is the one the shortint file left open: there the ordinary count that
`MazurM2Neg` supplies is the *larger* set, so it does not transfer.  `syrZ (2A) = A` moves the
target to `2A`, where `two_mul_mod_six_Z` says the residue obstruction is gone. -/
theorem conjectureAZ_neg_of_mazurM2Neg (hNeg : ThreeXMinusOne.MazurM2Neg)
    (a : ℕ) (ha : 0 < a) (h3 : ¬ 3 ∣ a) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → c * x ≤ (piAZ (-(a : ℤ)) x : ℝ) := by
  have hdouble : (-((2 * a : ℕ) : ℤ)) = 2 * (-(a : ℤ)) := by push_cast; ring
  by_cases hmod : (-(a : ℤ)) % 6 = 4
  · -- bridge case: count at `2a` instead
    have ha' : 0 < 2 * a := by omega
    have h3' : ¬ 3 ∣ 2 * a := by omega
    obtain ⟨c, hc, X₀, hX₀⟩ := hNeg (2 * a) ha' h3'
    refine ⟨c, hc, X₀, fun x hx => le_trans (hX₀ x hx) ?_⟩
    have hmod' : (-((2 * a : ℕ) : ℤ)) % 6 ≠ 4 := by
      rw [hdouble]; exact two_mul_mod_six_Z hmod
    have h1 := natCountM_le_piAZ ha' hmod' x
    have h2 : piAZ (-((2 * a : ℕ) : ℤ)) x ≤ piAZ (-(a : ℤ)) x := by
      rw [hdouble]
      exact piAZ_mono (fun n h => reachesSyrZ_two_mul h) x
    exact_mod_cast le_trans h1 h2
  · obtain ⟨c, hc, X₀, hX₀⟩ := hNeg a ha h3
    refine ⟨c, hc, X₀, fun x hx => le_trans (hX₀ x hx) ?_⟩
    exact_mod_cast natCountM_le_piAZ ha hmod x

/-! ## 9. Conjecture A over `ℤ` -/

/-- **Conjecture A over `ℤ` from M2 for `3x−1`.**  The `3x+1` half needs no hypothesis here. -/
theorem conjectureAZ_of_mazurM2Neg (hNeg : ThreeXMinusOne.MazurM2Neg) : ConjectureAZ := by
  intro a h3
  rcases lt_trichotomy a 0 with hneg | hzero | hpos
  · have hA : a = -((a.natAbs : ℕ) : ℤ) := by omega
    have ha : 0 < a.natAbs := by omega
    have h3' : ¬ 3 ∣ a.natAbs := fun hd => h3 (by omega)
    rw [hA]
    exact conjectureAZ_neg_of_mazurM2Neg hNeg _ ha h3'
  · exact absurd (hzero ▸ (dvd_zero (3 : ℤ))) h3
  · have hA : a = ((a.natAbs : ℕ) : ℤ) := by omega
    have ha : 0 < a.natAbs := by omega
    have h3' : ¬ 3 ∣ a.natAbs := fun hd => h3 (by omega)
    rw [hA]
    exact conjectureAZ_pos _ ha h3'

/-- **Conjecture A over `ℤ`, unconditionally.**

`ALConjectureA.conjectureA` supplies the positive targets and `ThreeXMinusOne.mazurM2Neg` the
negative ones.  Both are theorems in this tree; neither is an axiom or a hypothesis. -/
theorem conjectureAZ : ConjectureAZ :=
  conjectureAZ_of_mazurM2Neg ThreeXMinusOne.mazurM2Neg

/-! ## 10. Applegate–Lagarias's own threshold

`ConjectureAZ` says `∃ x₀, ∀ x ≥ x₀`.  AL print the bound for all `x ≥ |a|`, which is formally
*stronger* — `conjectureAZ_of_conjectureAZ'` below records that implication.

The gap is removable with no new mathematical input.  On the finite range `|a| ≤ x < x₀` the
target counts itself: `a ≠ 0` because `3 ∣ 0`, `|a| ≤ x` puts `a` in `Icc (-x) x`, and `a` reaches
`a` in zero steps.  So `π_a(x) ≥ 1` there, and shrinking `c` to `min c (1/(x₀+1))` absorbs it. -/

/-- The target is its own predecessor, so the count is never zero past `|a|`. -/
theorem one_le_piAZ {a : ℤ} (ha : a ≠ 0) {x : ℕ} (hx : a.natAbs ≤ x) : 1 ≤ piAZ a x := by
  have hmem : a ∈ (Finset.Icc (-(x : ℤ)) (x : ℤ)).filter (fun n => n ≠ 0 ∧ reachesSyrZ n a) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ha, ⟨0, rfl⟩⟩
  exact Finset.card_pos.mpr ⟨a, hmem⟩

/-- **Conjecture A over `ℤ`, at AL's printed threshold.** -/
def ConjectureAZ' : Prop :=
  ∀ a : ℤ, ¬ (3 ∣ a) →
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℕ, a.natAbs ≤ x → c * x ≤ (piAZ a x : ℝ)

/-- The threshold form is the stronger one: it gives `ConjectureAZ` by taking `x₀ = |a|`. -/
theorem conjectureAZ_of_conjectureAZ' (h : ConjectureAZ') : ConjectureAZ := by
  intro a h3
  obtain ⟨c, hc, hb⟩ := h a h3
  exact ⟨c, hc, a.natAbs, hb⟩

/-- **Conjecture A over `ℤ` at AL's threshold, unconditionally.** -/
theorem conjectureAZ' : ConjectureAZ' := by
  intro a h3
  have ha0 : a ≠ 0 := by rintro rfl; exact h3 (dvd_zero 3)
  obtain ⟨c, hc, x₀, hx₀⟩ := conjectureAZ a h3
  have hpos : (0 : ℝ) < 1 / ((x₀ : ℝ) + 1) := by positivity
  refine ⟨min c (1 / ((x₀ : ℝ) + 1)), lt_min hc hpos, ?_⟩
  intro x hx
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  by_cases hge : x₀ ≤ x
  · exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hxnn) (hx₀ x hge)
  · push_neg at hge
    have h1 : (1 : ℝ) ≤ (piAZ a x : ℝ) := by exact_mod_cast one_le_piAZ ha0 hx
    refine le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hxnn) (le_trans ?_ h1)
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    have hle : (x : ℝ) ≤ (x₀ : ℝ) := by exact_mod_cast hge.le
    linarith

/-! ## 11. Real `x`

AL's `x` is a real variable; `∀ x : ℕ` above is weaker again.  `π_a` depends only on `⌊x⌋`, and
`⌊x⌋ ≥ x/2` once `x ≥ 1`, so halving the constant carries the bound to all real `x ≥ |a|`.
`x ≥ |a| ≥ 1` is what supplies `x ≥ 1`, so no extra hypothesis is needed. -/

/-- **Conjecture A over `ℤ`, at AL's threshold, for real `x`.** -/
def ConjectureAZReal : Prop :=
  ∀ a : ℤ, ¬ (3 ∣ a) →
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, (a.natAbs : ℝ) ≤ x → c * x ≤ (piAZ a ⌊x⌋₊ : ℝ)

theorem conjectureAZReal : ConjectureAZReal := by
  intro a h3
  have ha0 : a ≠ 0 := by rintro rfl; exact h3 (dvd_zero 3)
  have ha1 : 1 ≤ a.natAbs := by omega
  obtain ⟨c, hc, hb⟩ := conjectureAZ' a h3
  refine ⟨c / 2, by positivity, ?_⟩
  intro x hx
  have hfl : a.natAbs ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hfl1 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast (by omega : 1 ≤ ⌊x⌋₊)
  have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hhalf : x ≤ 2 * (⌊x⌋₊ : ℝ) := by linarith
  have hkey : c * (⌊x⌋₊ : ℝ) ≤ (piAZ a ⌊x⌋₊ : ℝ) := hb ⌊x⌋₊ hfl
  nlinarith [hc.le, hhalf, hkey]

/-! ## 12. Applegate–Lagarias's (1.2) and Conjecture A, verbatim

Everything above still differs from the printed conjecture in three ways, none of them deep:

* `piAZ` is indexed by a natural `x`, and `ConjectureAZReal` reaches real `x` only by writing
  `piAZ a ⌊x⌋₊`.  AL's `π_a` is a function of the real `x` directly, cut out by `|n| ≤ x`.
* `piAZ` filters on `n ≠ 0`.  AL's (1.2) has no such clause.  It is vacuous — `T 0 = 0`, so `0`
  reaches only `0`, and `3 ∤ a` gives `a ≠ 0` — but vacuous is not the same as absent.
* the threshold is spelled `a.natAbs ≤ x` rather than `|a| ≤ x`.

`piAL` below is (1.2) as AL write it: the cardinality of the *set*, with no window construction,
no sign restriction, and `k ≥ 0`. -/

theorem syrZ_zero : syrZ 0 = 0 := by norm_num [syrZ]

theorem syrZ_iterate_zero : ∀ k : ℕ, syrZ^[k] 0 = 0
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply', syrZ_iterate_zero k, syrZ_zero]

/-- `0` reaches only `0`, so AL's missing `n ≠ 0` clause costs nothing. -/
theorem not_reachesSyrZ_zero {a : ℤ} (ha : a ≠ 0) : ¬ reachesSyrZ 0 a := by
  rintro ⟨k, hk⟩
  rw [syrZ_iterate_zero k] at hk
  exact ha hk.symm

/-- **Applegate–Lagarias (1.2), verbatim.**

`π_a(x) = #{n : |n| ≤ x and some T^(k)(n) = a, k ≥ 0}` — `n` over all of `ℤ`, `x` real. -/
noncomputable def piAL (a : ℤ) (x : ℝ) : ℕ :=
  {n : ℤ | |(n : ℝ)| ≤ x ∧ reachesSyrZ n a}.ncard

theorem piAL_eq_piAZ {a : ℤ} (ha : a ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    piAL a x = piAZ a ⌊x⌋₊ := by
  have hset : {n : ℤ | |(n : ℝ)| ≤ x ∧ reachesSyrZ n a}
      = ↑((Finset.Icc (-(⌊x⌋₊ : ℤ)) ((⌊x⌋₊ : ℤ))).filter
          (fun n => n ≠ 0 ∧ reachesSyrZ n a)) := by
    ext n
    have habs : |(n : ℝ)| = ((n.natAbs : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have hwin : |(n : ℝ)| ≤ x ↔ n.natAbs ≤ ⌊x⌋₊ := by
      rw [habs, Nat.le_floor_iff hx]
    rw [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, hwin]
    constructor
    · rintro ⟨hn, hr⟩
      have hn0 : n ≠ 0 := by rintro rfl; exact not_reachesSyrZ_zero ha hr
      exact ⟨⟨by omega, by omega⟩, hn0, hr⟩
    · rintro ⟨⟨h1, h2⟩, _, hr⟩
      exact ⟨by omega, hr⟩
  rw [piAL, hset, Set.ncard_coe_finset]
  rfl

/-- **Applegate–Lagarias Conjecture A, verbatim.**

"For each `a ≢ 0 (mod 3)`, there is a positive constant `c_a` such that `π_a(x) ≥ c_a x` for all
`x ≥ |a|`." -/
def ConjectureA_AL : Prop :=
  ∀ a : ℤ, ¬ (3 ∣ a) →
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, |(a : ℝ)| ≤ x → c * x ≤ (piAL a x : ℝ)

/-- **Conjecture A, as printed, unconditionally.** -/
theorem conjectureA_AL : ConjectureA_AL := by
  intro a h3
  have ha0 : a ≠ 0 := by rintro rfl; exact h3 (dvd_zero 3)
  have hcast : ((a.natAbs : ℕ) : ℝ) = |(a : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  obtain ⟨c, hc, hb⟩ := conjectureAZReal a h3
  refine ⟨c, hc, ?_⟩
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := le_trans (abs_nonneg _) hx
  rw [piAL_eq_piAZ ha0 hx0]
  exact hb x (by rw [hcast]; exact hx)

end ALConjectureAZ
