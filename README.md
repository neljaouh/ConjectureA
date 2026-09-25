# ConjectureA

Lean 4 proofs of two open conjectures about the 3x+1 (Collatz) problem:

* **Applegate–Lagarias Conjecture A**, exactly as printed in *Density Bounds for the
  3x+1 Problem I* (Math. Comp. 64, 1995), over all integer targets.
* **The 3x+1 Growth Exponent Conjecture** (Kontorovich–Lagarias), as a corollary.

Both are theorems in this repository, closed under `propext`, `Classical.choice` and
`Quot.sound` only. No `sorry`, no new `axiom`, no `native_decide`.

The proofs rest on Lech Mazur's formalisation of the positive lower density of Collatz
predecessors (his packages M1 and M2, Apache-2.0), which is vendored here unmodified.
See [What the proof depends on](#what-the-proof-depends-on) before citing anything.

## The two statements

Written out with no reference to any definition in this tree, exactly as they are
discharged in [Verification/ConjectureAExact.lean](Verification/ConjectureAExact.lean).
`T` is the accelerated map of Applegate–Lagarias (1.1): `x/2` on evens, `(3x+1)/2` on odds.
`π_a(x) = #{n ∈ ℤ : |n| ≤ x and T^k(n) = a for some k ≥ 0}` is their (1.2).

**Conjecture A** (`ALConjectureAZ.conjectureA_AL`). For each `a ≢ 0 (mod 3)` there is a
constant `c_a > 0` with `π_a(x) ≥ c_a · x` for all real `x ≥ |a|`:

```lean
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
```

**Growth Exponent Conjecture** (`ALConjectureAZ.growthExponentConjecture`). For each
`a ≢ 0 (mod 3)`, `η₃⁻(a) = η₃⁺(a) = 1`, where
`η₃⁻(a) = liminf log π_a(x) / log x` and `η₃⁺(a) = limsup log π_a(x) / log x`:

```lean
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
```

What is actually proved for the growth exponent is stronger: `tendsto_growthRatio` shows the
ratio `log π_a(x) / log x` *converges* to `1`; the two one-sided exponents fall out as
`h.liminf_eq` and `h.limsup_eq`.

## How the proof is put together

| File | Content |
|---|---|
| [ConjectureA.lean](ConjectureA.lean) | Conjecture A for **positive** targets, from M2's `predecessors_positive_lower_density`. M2 counts *ordinary* predecessors (`3n+1`, `n/2`); AL count *accelerated* ones. The two notions coincide except at `a ≡ 4 (mod 6)`, where `T(2a) = a` lets the bound at `2a` transfer. |
| [ThreeXMinusOne/](ThreeXMinusOne/) | A port of M2 to the **3x−1** map (71 modules, root `ThreeXMinusOne/PositiveDensity.lean`). `ThreeXMinusOne.mazurM2Neg` gives positive lower density of 3x−1 predecessors for every positive target not divisible by 3. Negation conjugates the negative-integer 3x+1 dynamics onto positive 3x−1, so this is what closes the `a < 0` case. |
| [ConjectureAZ.lean](ConjectureAZ.lean) | The assembly over `ℤ`: the conjugation `n ↦ −n`, the `ℕ → ℤ` cast of the accelerated map, the sign split, then the threshold `x ≥ |a|` (the target counts itself, so the finite window below any `X₀` is absorbed into the constant) and the passage from `x : ℕ` to `x : ℝ` and to AL's own `π_a` as a set cardinality. Weakest to strongest: `conjectureAZ`, `conjectureAZ'`, `conjectureAZReal`, `conjectureA_AL`. |
| [GrowthExponent.lean](GrowthExponent.lean) | The squeeze `(log c_a + log x)/log x ≤ log π_a(x)/log x ≤ (log 3 + log x)/log x` for `x ≥ max(|a|, 2)`, using the trivial bound `π_a(x) ≤ 2x + 1`. |
| [Verification/ConjectureAExact.lean](Verification/ConjectureAExact.lean) | The audit: both statements restated from scratch and discharged with `exact`; a `run_cmd` that walks the transitive dependencies of eight roots, rejects any axiom outside the three standard ones, rejects free variables in any root's type, and fails if a universal Collatz conjecture declaration is present in the environment at all. |

### What the proof depends on

Everything above reduces to a single mathematical input:

> **M2** (`CollatzPredecessorDensity.predecessors_positive_lower_density`). For every positive
> target `a` with `3 ∤ a`, the set of `n` whose ordinary Collatz orbit reaches `a` has positive
> lower natural density.

M2 is a theorem in this tree, proved in Lech Mazur's vendored sources (see
[Provenance](#provenance-and-licence)); it is not assumed. Two things should be said plainly:

* Mazur's packages describe themselves as **AI-assisted and not independently refereed**
  (see [UPSTREAM/M1/README.md](UPSTREAM/M1/README.md) and
  [UPSTREAM/M2/README.md](UPSTREAM/M2/README.md)). A clean build establishes that the proof
  terms type-check against Mathlib, not that a human referee has reviewed the mathematics.
  The same is true of the 3x−1 port in `ThreeXMinusOne/`, which mirrors M2's argument.
* The constant `c_a` is **not explicit** and depends on `a`. Nothing here gives a uniform
  constant, and a uniform constant is false: `π_a(|a|) = 1` for `a = 100`, `10000`, …

## Verification

The tree these files were elaborated in (Lean `v4.30.0-rc2`, Mathlib `5450b53e`) recorded:

* `#print axioms` on every root: `[propext, Classical.choice, Quot.sound]`.
* `Verification/ConjectureAExact.lean` elaborates and reports `all 8 roots closed`.
* `leanchecker --fresh ConjectureAZ` and `leanchecker --fresh GrowthExponent` both exit 0.
  `--fresh` replays every declaration into a fresh kernel environment (it took roughly 23× as
  long as the non-fresh run, which is how one can tell the replay is real). A missing module
  exits 1 and a truncated `.olean` exits 139, so exit 0 is informative.
* No file in the tree contains `sorry`, `axiom` or `native_decide` (checked by grep as well as
  by the axiom walk).

To reproduce:

```bash
lake exe cache get   # pinned Mathlib objects
lake build           # builds GrowthExponent and Verification, hence the whole chain
```

then, for the kernel replay,

```bash
lake env leanchecker --fresh ConjectureAZ GrowthExponent
```

A cold build of the vendored library (463 modules) is heavy. Mazur's own reproduction notes
recommend 16 GB or more and running one heavy job at a time; on an 8 GB machine it takes hours.

## Layout

```
ConjectureA.lean                 Conjecture A, positive targets           (this repo)
ConjectureAZ.lean                Conjecture A over ℤ, AL's exact form     (this repo)
GrowthExponent.lean              Growth Exponent Conjecture               (this repo)
ThreeXMinusOne/                  M2 ported to 3x−1, 71 modules            (this repo)
Verification/ConjectureAExact.lean   from-scratch restatement + axiom walk (this repo)
CollatzPredecessorDensity.lean   M2 public interface                      (Mazur, vendored)
Erdos1135/                       M1 supporting library + M2 modules       (Mazur, vendored)
FormalConjectures/               the Collatz map definition               (Formal Conjectures Authors, via M1)
UPSTREAM/M1, UPSTREAM/M2         upstream README, NOTICE, rights, manifests
scripts/verify_upstream.py       checks every vendored file against the upstream manifests
```

The Lean files here are the exact import closure of `GrowthExponent`, `ConjectureAZ`,
`ConjectureA` and `Verification.ConjectureAExact`, and nothing else.

## Provenance and licence

The files original to this repository (`ConjectureA.lean`, `ConjectureAZ.lean`,
`GrowthExponent.lean`, `ThreeXMinusOne/`, `Verification/`) are Copyright 2026
Naoufal El Jaouhari and released under the Apache License 2.0 ([LICENSE](LICENSE)).
Generative AI (Anthropic Claude, via Claude Code) contributed substantially to writing them.

The remaining 388 Lean files are redistributed **byte-for-byte unmodified** from two
Apache-2.0 source packages by Lech Mazur:

* *Explicit Positive-Density Collatz Convergence in Logarithmic Time*, source package v2.1
  (377 files: `Erdos1135/`, `FormalConjectures/`).
* *Positive Lower Density of Collatz Predecessors* (11 files: `CollatzPredecessorDensity.lean`,
  `Erdos1135/StoppingTime.lean`, ten modules under `Erdos1135/ND/PositiveDensity/`).

Their original README, NOTICE, RIGHTS.md, license.json and source manifests are kept under
[UPSTREAM/](UPSTREAM/), and [NOTICE](NOTICE) carries the required attribution.
`python3 scripts/verify_upstream.py` recomputes the SHA-256 of every vendored file and checks it
against those manifests; it currently reports `M1=377 M2=11` verified and lists the 75 files
that are original here.

## References

* D. Applegate and J. C. Lagarias, *Density bounds for the 3x+1 problem. I. Tree-search
  method*, Math. Comp. **64** (1995), 411–426. Conjecture A is stated in §1 after (1.2).
* A. V. Kontorovich and J. C. Lagarias, *Stochastic models for the 3x+1 and 5x+1 problems and
  related problems*, in *The Ultimate Challenge: The 3x+1 Problem*, AMS, 2010. The growth
  exponent conjecture, recorded there as weaker than Conjecture A.
* L. Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time* and
  *Positive Lower Density of Collatz Predecessors*, 2026, via ProofAtlas
  (<https://proofatlas.ai/formalizations/positive-density-log-time-collatz/>).
