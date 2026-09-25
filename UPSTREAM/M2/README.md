# Positive lower density of Collatz predecessors

**Migration verification passed on September 7, 2026, at 3:16:31 AM EDT.**
Against the public slim version 2.1 supporting library, all ten
implementation/support modules and the public interface were freshly compiled,
and the three advertised statements and their axiom sets were checked.
Supporting compiled dependencies were reused with the limitations below.
This is a new check of the migration, not a reuse of the earlier result. See
[release status](release-status.json) and
[verification evidence](evidence/verification.json).

This is a narrowed formal-source follow-up to *Explicit Positive-Density Collatz
Convergence in Logarithmic Time*. It contains ten scoped implementation/support
modules, a public interface with three theorem aliases, and one audit harness.
The already-public supporting library is obtained from one digest-pinned source
archive; it is not republished inside this thin package.

Start with [CollatzPredecessorDensity.lean](CollatzPredecessorDensity.lean).

| Public theorem | Exact conclusion |
| --- | --- |
| `predecessors_positive_lower_density` | For every positive target not divisible by 3, its ordinary predecessors have positive lower natural density. |
| `nonconvergence_positive_lower_density_of_counterexample` | Any positive start that never reaches 1 forces a positive lower density of such starts. |
| `universal_reaches_one_of_arbitrarily_dense_convergence` | If the proportion reaching 1 is arbitrarily close to one at arbitrarily large cutoffs, every positive start reaches 1. |

The ordinary map uses `n/2` at even inputs and `3*n+1` at odd inputs. Counts
are of positive integers strictly below the natural cutoff. Constants in the
first theorem may depend on the target. “Never reaches 1” includes the possibility
of a different cycle; it does not mean proved unbounded growth.

The third theorem retains an explicit statistical hypothesis. A density-one
limit of convergence to 1 would imply that hypothesis; this package does not
establish it. No general-target 10.46 clock, uniform density constant, effective
target-to-constants algorithm, or full Collatz theorem is claimed.

## Source identity and scope

The implementation sources are narrowed derivatives, not unchanged archival
bytes. Unused declarations and research exposition have been omitted; the
nonconvergence argument is specialized to the stated result. Supporting proofs
needed by the three announced roots remain transparent.
[source-manifest.json](source-manifest.json) records every released file hash.
The original private snapshot, origin revision, restoration information,
research plans and review notes are not part of this package.

Source review and static assembly alone do not establish that edited Lean files
compile. This release also passed fresh compilation and a root audit of its
exact migrated sources. [release-status.json](release-status.json) identifies
that completed check and its dependency-reuse limitations.

The supporting source dependency is public slim release version 2.1 at
`830b9d3f38f2a8da8cd921bf6a9310dd69336fd0`:

- [Source archive](https://www.proofatlas.ai/papers/positive-density-log-time-collatz/positive-density-log-time-collatz-v2.1-source.zip)
- SHA-256: `23f5cac4d66e696401144658752cf180a13ce70373a122f00693e1e1fe969c1f`
- Size: 914,975 bytes.

These identities are recorded in [baseline.json](baseline.json). Assembly
selects 377 supporting modules. With ten implementation/support modules,
the public wrapper and audit, the assembled project has 389 Lean source
files. The manifest records that exact import closure. The public slim
archive remains unchanged. Necessary companion-only proofs are supplied in
`PredecessorCountSupport.lean`, `PredecessorAnalyticSupport.lean`, and the
minimal reachability adaptation in `StoppingTime.lean`, alongside the other
new implementation modules. This does not restore the superseded oversized
library or modify the preceding paper's statements.

Prior route documents, other lanes, later research, compiled artifacts and
shared dependency checkouts are not included. The earlier source archives
were previously distributed; using a smaller current dependency does
not retract their previous disclosure.

## Assemble and reproduce

The thin directory alone is intentionally not an import-complete Lake project.
The download option requires curl and uses bounded HTTPS-only transport; the
complete archive digest is checked before any source member is accepted.
Choose a fresh destination, then assemble from the exact public dependency:

```sh
prlimit --as=34359738368 --cpu=55 timeout 60s \
  python3 scripts/assemble.py --download --output /absolute/new/assembled
```

Alternatively use `--baseline-zip /path/to/positive-density-log-time-collatz-v2.1-source.zip`
instead of `--download`. The assembler authenticates the archive before reading
members, verifies every baseline and extension source hash, checks the complete
static import closure, and refuses to replace an existing destination.

In the assembled directory, install the pinned Lean toolchain, fetch the pinned
external dependency cache, then run the bounded serial reproduction script:

```sh
bash scripts/lake-bounded.sh exe cache get
bash scripts/reproduce.sh
```

Use one heavy job at a time. A cold supporting-source build can require more
time than the supplied one-hour bound; a timeout is not successful verification.
The script retains its build and public-root audit logs under `build/`.
The Linux wrapper requires a working user systemd service and `flock`: it
enforces a 32 GiB aggregate memory cap and admits one actual compiler process
at a time, not just one thread per compiler. It fails if those safeguards are
unavailable.

[REPRODUCIBILITY.md](REPRODUCIBILITY.md) distinguishes an ordinary source build
from the optional local validation that reuses existing supporting artifacts.
The completed migration check used a later authenticated successful build
receipt for the same clean slim source revision. All 377 reused supporting
objects differ from the earlier archive's object inventory, and the later
receipt has no per-object hashes. The driver recorded the current object
hashes and verified its private copies, but did not independently authenticate
their historical source-to-object mapping. Third-party compiled dependencies
were also reused. No full cold rebuild or independent LeanChecker run is claimed.
Successful compilation proves only the exact checked declarations. It does not
constitute ProofAtlas acceptance or publication review.

## License

New formalization code and its build/verification tools are Apache-2.0 licensed
under Lech Mazur's explicit September 6, 2026 EDT approval. Baseline and upstream
notices remain separate and unchanged. See [LICENSE](LICENSE), [NOTICE](NOTICE),
[RIGHTS.md](RIGHTS.md), and [license.json](license.json). The source license does
not cover the accompanying paper or images.
