# Replay the November 21 collar revision

The original full replay archive has been recovered with the checksum recorded in the historical README. It contains all 1,879 inherited Lean objects. The revision sources, `Audit.lean`, original replay driver, correspondence, dependency pins and historical evidence are unchanged.

This procedure recompiles the 21 revision modules and their root import, then reruns the declaration audit against the retained inherited objects. It does not compile every inherited mathematical theorem from source. The audit traverses inherited types and bodies, while its additional kernel recheck applies to the reachable revision bodies. The explicit mathematical hypotheses and accepted external inputs of the original formalization remain in force. This is not a verification of all of Paper I.

## Inputs

- Linux x86-64 with Lean 4.19.0, compiler commit `6caaee842e94`; use the official Linux release or elan with the existing `lean-toolchain` file.
- Python 3.9 or later, Git, curl and tools required by Mathlib's cache. The replay and added scripts use Python's standard library.
- The unchanged `lake-manifest.json`, pinning Mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b` and eight other dependencies.
- [Original full replay ZIP](https://github.com/jaehwoo/Tarry-problem-lean-checkpoint-backup/releases/download/collar-replay-20261121/Paper_I_Collar_Lean_Replay.zip). This asset must be published at release tag `collar-replay-20261121` before the workflow is invoked. The release is a delivery location; content identity is enforced by the checksum below.

```
38986e227e918049298bb32b6090f6fccfcd3e9de1f47f10a3d48cc876fefe5c  Paper_I_Collar_Lean_Replay.zip
```

The ZIP is 257,609,922 bytes. Its inherited objects occupy 730,188,688 bytes uncompressed. Allow additional space for the compiler and upstream cache. Windows and macOS replay have not been tested; the retained object payload and CI procedure are tested on Linux.

## Replay from a repository checkout

Download the archive above. From this checkpoint directory, with the pinned Lean installation on `PATH`, run:

```sh
mkdir -p run-results
python3 scripts/prepare_baseline.py --archive /absolute/path/Paper_I_Collar_Lean_Replay.zip --receipt run-results/baseline.json
lake exe cache get
python3 scripts/check_environment.py --receipt run-results/environment.json
python3 replay.py --out run-results/replay --jobs 2
python3 scripts/check_results.py --out run-results/replay
```

Use a new or empty replay output directory. Remove any unrelated `LEAN_PATH` or `LEAN_SRC_PATH` override from your shell before fetching dependencies or replaying. The restoration script checks the archive, original source manifest, every revision source and every inherited object. It extracts only the inherited objects, preserves old evidence, and rejects conflicting existing objects rather than replacing them.

The unchanged original ZIP is also a portable package on its own: unpack it into an empty directory, install the pinned compiler and dependencies, then run `lake exe cache get` and `python3 replay.py --out replay-run --jobs 2` there. Its original README, manuscript, report and historical evidence remain inside it. The additional repository scripts are not required for that original route.

For an offline installation, the unchanged driver accepts `--lean /absolute/path/to/lean --mathlib-paths "$MATHLIB_PATHS"`. Supply only the pinned upstream object directories, separated by the OS path separator. Revision objects are always built into a new directory; project object directories are rejected in the upstream path.

## Expected evidence and interpretation

| Check | Expected result |
| --- | --- |
| Retained inherited object hashes | 1,879 match `baseline/SHA256SUMS.json` |
| Dependency checkouts | All nine commits match `toolchain.json`, with no tracked source changes |
| Fresh revision compilation | 22 successful compiler invocations including the root import |
| Public declarations | 34 |
| Reachable revision bodies checked again in the kernel | 92 |
| Transitive declarations scanned | 57,733 in the historical/preserved-cache run; 57,715 with the refreshed pinned upstream cache |
| Transitive axiom set | `propext`, `Classical.choice`, `Quot.sound` |
| Comparison to historical evidence | Public/revision counts, 92 kernel-expression fingerprints, project modules and all per-entry axiom reports agree; transitive scan count recorded separately |

`run-results/replay/evidence/` contains individual compiler logs, full axiom output, `build.json`, `closure-summary.txt`, `kernel-bodies.tsv` and `loaded-project-modules.txt`. `build.json` records commands, compiler version, object hashes, timing and actual upstream search paths. Recompiled object SHA-256 hashes may depend on output paths; the comparison uses kernel-expression fingerprints instead of requiring identical new object bytes.

The upstream cache refresh changes the proof bodies of seven named upstream theorems and some generated proof helpers; the seven named theorem types agree. Nineteen helper declarations disappear from the reachable closure and one appears, accounting for the net difference of 18. The revision fingerprints and all 68 per-entry axiom reports remain unchanged. `check_results.py` records this diagnostic count in `comparison.json`; it requires matching public/revision counts, revision fingerprints, project modules, axiom reports and a successful unchanged Lean audit. See `reproduction-evidence-20261123/` for the comparison and diagnostic details. Matching the historical upstream object bytes is not claimed for the refreshed cache.

## Manual public CI

The workflow `.github/workflows/reproduce-collar-20261121.yml` is manual only (`workflow_dispatch`) and has read-only repository permissions. It downloads the original archive, enforces its checksum, restores the inherited objects, installs the exact checksum-pinned Linux compiler, fetches the upstream cache, checks the dependency revisions, recompiles the revision and compares the audit. Logs are uploaded on success or failure with 90-day artifact retention. Publication of the workflow does not start it automatically.

The workflow limits cache downloads to four parallel transfers and four new transfers per second to reduce HTTP 429 failures. Cache download errors remain failures; they are not bypassed by changing pins or substituting project prerequisites.

Before the first run, upload the unchanged original ZIP to release tag `collar-replay-20261121`. A missing asset causes an explicit download failure. A changed asset fails checksum verification. No GitHub Actions success is claimed until an actual public run completes.

## Reproduction helper checks

Run `python3 tests/test_reproduction.py --archive /absolute/path/Paper_I_Collar_Lean_Replay.zip`. This exercises complete restoration, repeated verification, changed archive rejection, source and manifest integrity checks, conflicting inherited objects and comparison with fresh audit evidence. These are checks of the delivery tools; they add no mathematical proof credit.
