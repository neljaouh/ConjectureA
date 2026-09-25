import ThreeXMinusOne.TerminalCensus
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideCommonFloorFullTerminalPhysical

/-!
# The terminal source window

`ndGeom2RootSideCommonFloor_capOne_source_bounds` and
`fullTerminal_source_mem_target_and_window`, mirrored — the part `Assembly` needs for `hwin`
and `hlt`.

**Two things here need no porting at all.**  `fullTerminalShift` and `fullTerminalShift_spec`
choose, for each label, a shift index whose physical lower scale lands in `[X, 2X)`.  They are
indexed only by the state wrapper and never mention an incidence or a map, and the `3x−1`
construction inhabits that same wrapper — so they are used here verbatim, as the artifact's own.

What does change is the constant.  The minus shell (Layer 13) has upper constant `4·2^K` where
`+1` has `2·2^K`, so at `K = 1` a terminal source sits in `[ℓ, 32ℓ]` rather than `[ℓ, 16ℓ]`, and
with `ℓ ∈ [X, 2X)` the window is `[X, 64X)` rather than `[X, 32X)`.  That is the same factor two
as everywhere else, and it is the factor by which the final density constant differs.

The `+1` file also proves the source stays in `oddSyracuseLogTimeOneSet C` — that it still
reaches `1` in logarithmic time.  That is for the Conjecture A instantiation, not for a general
target: `generalTarget_publicCount_from_mass` asks only for `Reaches` and a non-returning seed.
`3x−1` has no `1` to reach, so there is nothing to mirror; `Reach.sourceM_mem_predecessorSetM`
(Layer 10) already carries reachability down to sources.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

variable {Label : Type*} {root shift : Label → ℕ} {b : ℕ}

/-- **Two-sided physical bounds on a `3x−1` terminal source**, at cap one.
`+1` has `16 * ell`; the minus shell gives `32 * ell`. -/
theorem capOne_source_boundsM (hodd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hlower : ∀ i, 16 ^ b ≤ root i)
    (z : IncidenceM Label root (fun _ => b) shift 1) :
    let i := labelM z;
    let ell := ndGeom2ShiftedWideSymmetricPhysicalLowerScale b (shift i) (root i);
    ell ≤ (sourceM z : ℝ) ∧ (sourceM z : ℝ) ≤ 32 * ell := by
  let i := labelM z
  let r := ndGeom2ShiftedWideSymmetricShiftRadius b
  let num := 2 ^ shift i * 4 ^ b * root i
  let den := 4 * 2 ^ r * 3 ^ b
  have hden : (0 : ℝ) < ((den : ℕ) : ℝ) := by dsimp [den]; positivity
  have h := sourceM_shell hodd (fun _ => hb) hlower z
  change ((num : ℕ) : ℝ) / den ≤ (sourceM z : ℝ) ∧
    (sourceM z : ℝ) ≤ 32 * (((num : ℕ) : ℝ) / den)
  constructor
  · apply (div_le_iff₀ hden).2
    exact_mod_cast (show num ≤ sourceM z * den by
      simpa only [num, den, r, i, Nat.mul_comm] using h.1)
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hden).2
    have hu : sourceM z * den ≤ 32 * num := by
      have hu' := Nat.mul_le_mul_left 4 h.2
      dsimp only [den, num, r, i] at hu' ⊢
      norm_num only [pow_one] at hu'
      nlinarith only [hu']
    exact_mod_cast hu

/-- Terminal incidences of the `3x−1` construction at the chosen shift. -/
abbrev FullTerminalIncidenceM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : U.state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin U.floor (U.state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax U.floor (U.state.root i)) :=
  IncidenceM U.state.Label U.state.root (fun _ => U.floor) (U.fullTerminalShift X hX hi) 1

/-- **The window.**  `+1` has `32 * X`; the minus shell gives `64 * X`. -/
theorem fullTerminalM_source_window (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : U.state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin U.floor (U.state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax U.floor (U.state.root i))
    (z : FullTerminalIncidenceM U X hX hi) :
    X ≤ (sourceM z : ℝ) ∧ (sourceM z : ℝ) < 64 * X := by
  have hpacket : ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
    (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans (U.state.rootLower i)
  have hs := U.fullTerminalShift_spec X hX hi (labelM z)
  have hb := capOne_source_boundsM U.state.root_odd
    (by have h := U.floor_twoHundred; omega) hpacket z
  exact ⟨hs.2.1.trans hb.1, by nlinarith only [hb.2, hs.2.2]⟩

end

end ThreeXMinusOne
