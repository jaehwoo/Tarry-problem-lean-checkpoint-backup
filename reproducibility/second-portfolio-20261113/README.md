# Paper I second portfolio: standalone reproduction

This package recompiles the three statements published on 13 November 2026 from preserved Lean source. It includes their complete local import closure: **598 PaperILean modules**, including the 25 checkpoint modules. The original proof files are copied byte for byte. No historical project `.olean` or `.ilean` is used to build them.

The upstream repository is `jaehwoo/Tarry-problem-lean-checkpoint-backup`, frozen at commit `12f7745a8963901f321d8c9ede8825a94501459b`. All source origins, archive members, and SHA-256 hashes are in `provenance/source-manifest.json`. Additional dependencies recovered from saved archives are included as source; those archives are not needed to run this package.

## Fixed environment

- Lean: `leanprover/lean4:v4.19.0`.
- Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- All eight transitive Lake package revisions are locked in `lake-manifest.json` and checked against `provenance/dependency-pins.json`.
- Required host tools: Git, Python 3.10 or newer, curl, tar, and Lean/Lake 4.19.0 (usually managed by elan). No Python packages are required.
- Linux and macOS use the same Python commands; Windows users can use WSL. The executed platform and results are recorded in `evidence/RESULTS.md`; other platforms are not claimed as tested.

The initial dependency preparation needs internet access. Lean, Mathlib, their dependency sources, and their platform binaries are not bundled. This is an independent project source package, not a complete offline operating-system image. It does not depend on an old working directory, private cache, Library access, or the original development environment.

## Run

Install Lean 4.19.0 with elan, if elan is already installed:

```sh
elan toolchain install leanprover/lean4:v4.19.0
```

Alternatively, install the matching official Lean release and put its `bin` directory on `PATH`. The package checks the compiler version and installed Git revisions before compiling project sources.

Optionally verify all delivered-file hashes with `sha256sum -c SHA256SUMS` (or `shasum -a 256 -c SHA256SUMS` on macOS).

From this directory:

```sh
python3 scripts/verify_sources.py
python3 scripts/reproduce.py --jobs 2
```

The second command prepares the pinned third-party cache, then recompiles every local module from source, checks the four endpoints, rechecks their proof bodies with the Lean kernel, and checks their transitive axiom sets. It records each command, exit code, log hash, product hash, timeout, failed module, and blocked dependent under a new `run-results/` directory. A failed step returns a nonzero exit code. There are no automatic proof edits or proof retries.

Each Lean process uses one worker. The package defaults are `maxHeartbeats=200000` and `maxRecDepth=512`. The 25 checkpoint sources contain no overrides of these limits. Seventeen older dependency source files retain their original explicit heartbeat settings; `scripts/verify_sources.py` lists them. These settings have not been raised or deleted for this reproduction.

A module has a 180-second wall-time limit; the full first-party compilation has a 3,600-second limit. These are execution limits, not mathematical assumptions. They can be adjusted with `--module-timeout` and `--total-timeout` on slower machines without changing Lean proof limits. The runner terminates its active Lean processes when interrupted.

## Separate preparation, compilation, and audit

```sh
python3 scripts/reproduce.py --prepare-only
python3 scripts/verify_sources.py --installed
python3 scripts/reproduce.py --skip-cache --jobs 2
```

After a successful project compilation, the declaration and axiom audit can also be run directly:

```sh
lake env lean -j1 -DmaxHeartbeats=200000 -DmaxRecDepth=512 Repro/Endpoints.lean
lake env lean -j1 -DmaxHeartbeats=200000 -DmaxRecDepth=512 Repro/AuditEndpoints.lean
```

`Repro/AuditEndpoints.lean` requires each endpoint to be a safe, non-partial theorem with a closed proof body, rechecks its type and proof body, and rejects any transitive axiom outside the saved set. Its `#check` output exposes the actual theorem parameters, and its `#print axioms` output records the kernel axiom dependencies. The script prints exactly four `ENDPOINT_AUDIT_PASS` lines on success.

To save a separate audit-only receipt:

```sh
python3 scripts/reproduce.py --audit-only
```

An audit-only receipt is labelled `AUDIT_ONLY_PASS`; it is not fresh compilation evidence. The standard Lake target `lake build Repro` is available for normal use, but the Python runner is the documented fresh-build path: it removes only generated first-party products, compiles in dependency order, bounds execution, and records failures explicitly.

The optional product comparison keeps historical and fresh checksums separate:

```sh
python3 scripts/compare_checkpoint_products.py
```

## Mathematical scope

| Statement | Paper I lines | Lean endpoints |
| --- | --- | --- |
| Parabolic collars | I980-I993 | `PaperI.ParabolicCollar.parabolic_collars_local_boxes` |
| Derivative good points and curved strips | I3202-I3218 | `PaperI.GoodStrips.derivative_good_points_rectangle`; `PaperI.derivative_good_points_curved_strips` |
| Algebraic surface packing cutoff | I3312-I3317 | `PaperI.AffineArea.algebraic_surface_packing_cutoff` |

`provenance/original-verification-summary.json` is an unmodified copy of the public checkpoint summary. Its retained published theorem inputs remain explicit parameters of the original statements. They are not inserted as new Lean axioms or discharged by this package. The distinction matters: a theorem quantified over an external theorem parameter can have only the standard kernel axioms while still depending mathematically on that parameter.

| Statement | Retained published theorem inputs, copied from the original summary |
| --- | --- |
| Algebraic surface packing cutoff | `PublishedNonsingularBezout` |
| Parabolic collars | `PublishedQuantitativeRealQE`; `PublishedFiniteConnectedCover`; `PublishedSemialgebraicHardtTriviality`; `PublishedRealSemialgebraicity` |
| Derivative good points and curved strips | `PublishedEquispacedDividedDifferenceMeanValue`; `PublishedFiniteConnectedCover`; `PublishedSemialgebraicHardtTriviality`; `PublishedRealSemialgebraicity`; `PublishedPiecewiseNashExtensions`; `PublishedCylindricalInitialBandDecomposition`; `PublishedSemialgebraicCellDecomposition`; `PublishedCompatibleSemialgebraicHardtTriviality`; `PublishedOneVariableMonotonicity` |

The saved endpoint axiom set is `propext`, `Classical.choice`, and `Quot.sound`. This package rejects `sorry`, `admit`, custom `axiom` declarations in the copied project sources, and unexpected endpoint axioms. It does not replace missing dependencies with assumptions.

The historical **797-import integration check** is wider than this **598-module local dependency closure**. Recompiling the latter is not a rerun of the former. Likewise, the historical audit of 375 mathematical declarations and 83 compiler/runtime entries remains historical evidence; the new endpoint audit explicitly covers four theorem declarations. A successful fresh build checks all 598 source modules through the compiler, but does not repeat the historical manuscript correspondence reviews or runtime inventory review.

This is not a proof of the full Tarry convergence theorem or completion of human verification. The width-band lemma I1113-I1138, exhaustive measurable assignment at I472, and same-`P` estimate at I773 remain open as recorded in the checkpoint.

## Failures and diagnostics

- Source/hash/import failures occur before compilation; the diagnostic names the altered or missing file.
- Dependency checkout/cache errors are environment preparation failures. They do not establish a mathematical gap.
- A Lean error is preserved in the named module log. Its dependents are marked blocked; independent modules may still compile. No proof is changed automatically.
- A timeout is recorded separately from a Lean compiler error.
- Historical product hashes are reference data. Fresh product hashes and any comparison with them are reported separately; a different product hash alone is not a proof error.

If the official cache returns HTTP 429, wait for that service's rate limit to clear or use the bounded-download example in `scripts/prepare_cache_limited.sh`. This changes curl concurrency only. It does not change Mathlib or its revisions.

## Files

- `PaperILean/`: unchanged project sources and local dependencies.
- `Repro/`: new endpoint checks and kernel/axiom audit commands.
- `scripts/`: source/pin validation and bounded fresh compilation.
- `provenance/`: immutable source origins, original summary, and dependency pins.
- `evidence/`: results and logs from the creation of this package.
- `SHA256SUMS`: delivered-file hashes; generated `.lake/` and future `run-results/` files are excluded.

No manuscript, existing proof, original verification report, historical compiled product, or historical record is modified by this package.
