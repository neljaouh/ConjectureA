import ConjectureAZ
import GrowthExponent
import Lean

/-!
# Independent audit of `conjectureA_AL`

Two checks that do not trust any definition in this tree.

1. **Statement fidelity.**  Applegate–Lagarias's Conjecture A is restated here *from scratch* —
   the accelerated map, reachability and `π_a` all written inline — and discharged by
   `ALConjectureAZ.conjectureA_AL` with `exact`.  If that elaborates, every definition in the
   chain unfolds to exactly what AL print; nothing can be hiding in a name.

2. **Axiom closure**, checked programmatically rather than by reading `#print axioms` output.
-/

open Lean Elab Command

/-- AL Conjecture A, written out with no reference to any definition in this tree. -/
example :
    ∀ a : ℤ, ¬ (3 ∣ a) →
      ∃ c : ℝ, 0 < c ∧
        ∀ x : ℝ, |(a : ℝ)| ≤ x →
          c * x ≤
            ({ n : ℤ | |(n : ℝ)| ≤ x ∧
                ∃ k : ℕ,
                  (fun m : ℤ => if m % 2 = 0 then m / 2 else (3 * m + 1) / 2)^[k] n = a
             }.ncard : ℝ) :=
  ALConjectureAZ.conjectureA_AL

/-- The same for the `ℕ`-indexed threshold form, and for the `3x−1` input it rests on. -/
example :
    ∀ a : ℕ, 0 < a → ¬ 3 ∣ a →
      ∃ c : ℝ, 0 < c ∧ ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
        c * (X : ℝ) ≤
          (Erdos1135.Terras.natCount
            {n : ℕ | 0 < n ∧ ∃ m : ℕ,
              (fun t : ℕ => if t % 2 = 0 then t / 2 else 3 * t - 1)^[m] n = a} X : ℝ) :=
  ThreeXMinusOne.predecessors_positive_lower_density

/-- The growth exponent conjecture, likewise written from scratch. -/
example :
    ∀ a : ℤ, ¬ (3 ∣ a) →
      Filter.liminf (fun x : ℝ =>
        Real.log ({ n : ℤ | |(n : ℝ)| ≤ x ∧ ∃ k : ℕ,
            (fun m : ℤ => if m % 2 = 0 then m / 2 else (3 * m + 1) / 2)^[k] n = a }.ncard : ℝ)
          / Real.log x) Filter.atTop = 1
      ∧
      Filter.limsup (fun x : ℝ =>
        Real.log ({ n : ℤ | |(n : ℝ)| ≤ x ∧ ∃ k : ℕ,
            (fun m : ℤ => if m % 2 = 0 then m / 2 else (3 * m + 1) / 2)^[k] n = a }.ncard : ℝ)
          / Real.log x) Filter.atTop = 1 :=
  ALConjectureAZ.growthExponentConjecture

run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let roots := #[`ALConjectureAZ.conjectureA_AL, `ALConjectureAZ.conjectureAZReal,
    `ALConjectureAZ.conjectureAZ', `ALConjectureAZ.conjectureAZ,
    `ALConjectureAZ.growthExponentConjecture, `ALConjectureAZ.tendsto_growthRatio,
    `ThreeXMinusOne.predecessors_positive_lower_density, `ALConjectureA.conjectureA]
  for root in roots do
    unless env.contains root do throwError "Missing theorem {root}"
    let some info := env.find? root | throwError "Missing declaration {root}"
    -- the theorem must be a closed term: no free hypotheses smuggled into the type
    unless info.type.hasFVar == false do throwError "{root} has free variables in its type"
    for axiomName in (← collectAxioms root) do
      unless allowed.contains axiomName do
        throwError "Unexpected dependency: {root} uses {axiomName}"
  logInfo m!"all {roots.size} roots closed under {allowed}"

-- No universal Collatz conjecture may have leaked in as an assumption.
run_cmd do
  let env ← getEnv
  for bad in #[`CollatzConjecture.collatz_conjecture, `Collatz.conjecture] do
    if env.contains bad then throwError "Unproved universal conjecture imported: {bad}"
  logInfo "no universal-conjecture declaration present"
