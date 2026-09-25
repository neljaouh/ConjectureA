# Explicit positive-density Collatz convergence

Version 2.1 · theorem-specific source package.

This source package accompanies Lech Mazur, *Explicit Positive-Density Collatz
Convergence in Logarithmic Time*. Start with `CollatzPositiveDensity.lean`.

For the ordinary Collatz map, the public theorem gives fixed explicitly defined
`c > 0` and `X0 > 0` such that every natural `X >= X0` has at least `c * X`
positive integers `n < X` reaching one in at most `(523/50) * ln(n)` ordinary
steps. The same constants also give the weaker `10.48` statement.

The four public theorem roots are:

- `CollatzPositiveDensity.densityConstant_pos`
- `CollatzPositiveDensity.cutoff_pos`
- `CollatzPositiveDensity.positive_density`
- `CollatzPositiveDensity.positive_density_ten48`

An odd step is `3*n+1`, without a division by two. Counts are strictly below
the natural cutoff, zero is excluded, and logarithms are natural. The constants
are closed arithmetic expressions with astronomical sizes. Positive lower
natural density is not density-one convergence, an asymptotic counting formula,
a practical numerical bound, or a proof of the full Collatz conjecture.

## Source and verification

This successor source layout retains selected theorem-supporting definitions,
proofs and elaboration helpers, with repaired imports. Its public mathematical
statement and constant recipes are unchanged. `source-manifest.json` identifies
the retained source bytes and their public-source origin. The package is not
claimed to be the smallest possible mathematical proof.

Lean is pinned to `4.30.0-rc2` and Mathlib to
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`; the dependency lock records all
package revisions. Third-party sources and compiled caches are not bundled.
Do not substitute project objects built from different source bytes.

All 386 project modules were compiled afresh from the included reduced sources,
in import order, without original project objects. The three additional Lean
files under `Verification/` check the public interface and its dependencies.
All four public roots use only `propext`, `Classical.choice` and `Quot.sound`:
no admitted proof, unproved project axiom or native-evaluation axiom occurs in
their transitive dependencies. Exact byte-bound receipts are under `evidence/`.

In addition to the public-root checks, `Verification/Statements.lean` checks
the literal ordinary-map counting statement without implementation predicates.
Source scans supplement, and do not replace, the transitive axiom checks.
The recorded build used serial direct Lean compilation with pinned third-party
caches. It did not rebuild Mathlib, run an independent `leanchecker`, or claim
a Lake-orchestrated build. The Lake command below is the standard reproduction
route; successful local checks alone are not ProofAtlas acceptance.

To reproduce, install the pinned Lean toolchain, fetch the pinned dependencies
and their published Mathlib cache with `lake exe cache get`, then run:

```sh
bash scripts/validate.sh
```

The wrapper records the public-target build, literal statement, public-root
axioms, declaration dependencies and exact source-integrity checks. It applies
finite memory/time limits and does not download caches itself. Run it alone,
without another heavy proof job. `scripts/check-cached.sh` is for checks using
already authenticated current project objects; it is not a substitute for a
source build after an edit.
The resource-limited wrappers target Linux and require Bash, Python 3, jq,
util-linux and coreutils, in addition to the pinned Lean toolchain.

## Attribution and rights

Lech Mazur directed the research and is the named author. Generative AI
contributed substantially through the ProofAtlas.ai harness with OpenAI models
accessed through Codex. Anthropic Claude assisted with the original manuscript
review. AI review is not formal verification or an independent acceptance gate.

Author-owned code and build/verification scripts are Apache-2.0; see `LICENSE`,
`NOTICE`, `RIGHTS.md` and `license.json`. Upstream notices remain attached.
This grant does not cover the paper or infographic. A source package and its
checks do not themselves authorize publication or grant ProofAtlas acceptance.

[Result and paper](https://proofatlas.ai/formalizations/positive-density-log-time-collatz/)
 · [Formal source and evidence](https://proofatlas.ai/sources/positive-density-log-time-collatz/)
