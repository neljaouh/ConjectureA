# Reproducibility and validation scope

**Verification of the public slim version 2.1 migration passed on September 7,
2026, at 3:16:31 AM EDT.** All eleven source compilations and the separate
three-root statement/axiom audit completed successfully. Supporting compiled
dependencies were reused under the provenance limitations explained below.
This is a new verification of the migrated sources, not a reuse of the
earlier result against a different dependency. See
[the verification summary](evidence/verification.json) and
[release status](release-status.json).

The public wrapper states the three announced results using direct proofs from
the narrowed implementation sources. It introduces no new hypothesis or
unproved assumption. Source inspection is not a compiler check. The release
audit independently restates the underlying
counting predicates and statistical quantifiers before inspecting all three
actual wrapper-root axiom closures.

The pinned toolchain is `leanprover/lean4:v4.30.0-rc2`; mathlib resolves to
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`. All nine external package revisions
are retained in `lake-manifest.json`. The assembled project has no source
dependency on a private research checkout.

The supporting source archive is the public slim version 2.1 release at
commit `830b9d3f38f2a8da8cd921bf6a9310dd69336fd0`, available as
[positive-density-log-time-collatz-v2.1-source.zip](https://www.proofatlas.ai/papers/positive-density-log-time-collatz/positive-density-log-time-collatz-v2.1-source.zip).
Its SHA-256 is
`23f5cac4d66e696401144658752cf180a13ce70373a122f00693e1e1fe969c1f`
and its length is 914,975 bytes. The exact identity is fixed in `baseline.json`.

## Static source checks

`scripts/assemble.py` verifies the baseline archive's full SHA-256, its internal
release commit, every baseline source digest, and each thin-manifest input. It
authenticates the ten implementation/support files and rejects unexpected
replacement of a baseline module. It then computes the transitive local import
closure of the new wrapper and audit, verifies the extension's build order, and writes only
selected source files and required release metadata to a fresh directory.
The selected closure contains 377 supporting baseline modules, ten
implementation/support modules, the public wrapper and the audit: 389 Lean
source files in total. The public slim archive itself remains unchanged.

`scripts/verify-assembly.py` rechecks every assembled file against the resulting
manifest and verifies that all recorded imports resolve. These are byte and
import checks, not compiler or proof checks.

## Fresh extension replay with reused dependencies

For a local environment that has the exact public slim baseline checkout and
its supporting compiled artifacts, the completed migration used the following
later-build receipt mode:

```sh
prlimit --as=34359738368 --cpu=3000 timeout 3300s \
  python3 scripts/replay.py \
    --assembled /absolute/assembled \
    --baseline-cache /absolute/slim-v2.1-baseline-checkout \
    --later-baseline-build-receipt /absolute/evidence/later-baseline-build.json \
    --later-baseline-build-receipt-sha256 5b4d776fbb4638792e84d8597d03ce2f742f36fd568ba1e91063e0e9df2cecf5
```

The driver requires a clean baseline checkout at exactly the recorded public
commit and verifies that its selected source files match the authenticated
public archive. It also authenticates the archive's `evidence/project-build.json`
receipt against the assembled manifest. That earlier public receipt records
386 freshly built project modules, but its per-object inventory predates a
later `lake --rehash build CollatzPositiveDensity` on the same source revision.
All 377 objects reused by this extension differ from that earlier inventory;
the completed replay records all 377 mismatches rather than claiming a match.

The later receipt, dated September 7, 2026 at 12:52:40.599 AM EDT, has SHA-256
`5b4d776fbb4638792e84d8597d03ce2f742f36fd568ba1e91063e0e9df2cecf5`.
The two optional flags above supply that receipt and its expected digest.
The driver verifies the exact source revision, clean source state before and
after the build, pinned toolchain and dependency lockfile, successful build
command and exit code, and recorded baseline axiom audit. The earlier
source-manifest and project-build receipt remain authenticated as well.

The later receipt contains no per-object hashes. Accordingly, for every
selected supporting object the driver hashes the bytes currently used,
makes a private copy, and verifies the copied bytes have the same hash.
This identifies the present build inputs; it does not independently prove
the historical mapping from source files to those compiled objects. The
replay explicitly records that limitation. Without the later-receipt flags,
exact object matches to the older authenticated inventory are required.

External package Git revisions and tracked-source cleanliness are checked;
their existing compiled artifacts are reused without changing the shared
packages. Neither current object hashing nor the later build receipt
independently rebuilds or authenticates the historical provenance of all
third-party compiled artifacts.

It compiles all ten implementation/support modules and the public wrapper from
their source files, serially, then runs the exact-statement and axiom audit.
Each Lean child has one thread, a 32 GiB address-space cap, a 240 CPU-second
limit and a 300-second wall limit. It refuses to start when another Lean or
leanchecker process is active and rechecks between modules. Scheduling still
requires coordination; an empty process list between another worker's modules
does not authorize preempting that worker's priority.

Each stage retains its command, return code, duration and log digest in
`build/replay.json`. Success requires all eleven source compilations and the
audit to complete successfully, with all three printed root axiom sets
containing only `propext`, `Classical.choice`, and `Quot.sound`.

This mode is **fresh extension source replay with reused dependency artifacts**.
The completed run authenticated the later successful baseline build receipt
and exact source/dependency identities, while separately recording the present
object hashes. Because the later receipt has no per-object inventory,
independent historical source-to-object authentication remains false; the
earlier object-inventory mismatch is disclosed. This is not an independent
reconstruction of the baseline build. Third-party compiled dependencies remain
reused. No full cold rebuild of all dependencies or independent LeanChecker
run is implied.

## Owning-target source build

`scripts/reproduce.sh` uses `lake --rehash build` for the new owning target,
followed by the same audit. Run this in an isolated assembled tree with its
own external packages; do not ask Lake to rehash a shared dependency checkout
that another release owns. This procedure is distinct from the direct replay
above. A retained direct-replay success must not be relabelled as a Lake rebuild.

The cold-build wrapper uses a systemd scope with `MemoryMax=32G` and no swap
for the complete process tree. A private Lean wrapper holds a `flock` mutex
across every compiler invocation, forcing actual compiler processes to run
serially even if Lake schedules several jobs. Runtime environment settings
also give Lake one scheduler thread and each compiler one thread. These are
distinct controls; a thread-count setting alone is not the process-count guard.

## Current evidence

The extension replay against the slim version 2.1 dependency completed at
3:16:31 AM EDT on September 7, 2026 (`2026-09-07T07:16:31Z`). All eleven
source compilations and the separate statement/axiom audit returned zero.
Every advertised root reported exactly `propext`, `Classical.choice`, and
`Quot.sound`; no admitted, custom project or generated native-evaluation
axiom appeared. The assembled inputs and baseline checkout remained unchanged
during verification. This result covers the new companion-only adaptations
and does not borrow acceptance from the earlier extension or baseline build.

The public summary binds the exact compiled sources, slim dependency and
checking procedure, including the later-receipt mode and all 377 earlier
object-inventory mismatches. Later documentation/status updates may be
included in the final source manifest only with the distinction from compiled
Lean inputs preserved. Private cache inventories and local operational logs
are not public payloads.

The authoritative result of a replay is its completed `build/replay.json`,
bound to the actual assembled input and logs. A running, absent, interrupted or
failed receipt is not a successful check. Public handoff metadata must state
which procedure completed and retain its limitations. The inherited owner's
earlier audit receipts are historical evidence, not this new interface check.

## Scope of this baseline migration

This candidate makes the authorized move to the unchanged public slim version
2.1 archive. Compatibility requires companion-only proofs that the main
target-one release did not need: these are retained in
`PredecessorCountSupport.lean`, `PredecessorAnalyticSupport.lean` and the
minimal reachability adaptation in `StoppingTime.lean`. Together with the
other seven implementation modules, these make ten implementation/support
modules and one public wrapper, not a restoration of the old oversized library.

The three public theorem statements remain the same. Source/import checks
and new dependency pins document the migration, and the separate fresh
compilation and root-axiom checks against this exact slim dependency have now
passed with the stated dependency-reuse limitations. Any subsequent dependency replacement requires a new
compatibility check and fresh evidence again; changing only a URL or hash is
never sufficient.
