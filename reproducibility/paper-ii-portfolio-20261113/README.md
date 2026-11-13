# Reproduce the five verified Paper II lemmas

This checkpoint rebuilds the Paper II proofs verified on 13 November 2026 using Lean 4.19.0, revision `6caaee842e94`. The [published checkpoint](../../verification-20261113-paper-ii-portfolio/) identifies the five lemmas and their manuscript lines, original hypotheses, Lean declarations, and audit evidence. Complete verification of the main theorem remains pending.

## Run locally

Use a Unix-like environment with Python 3.9 or later, Git, and Lean 4.19.0 with its matching Lake. Install the pinned Lean release and put its `bin` directory on your path. For Elan, use `elan toolchain install leanprover/lean4:v4.19.0` and set the path to the installed toolchain’s `bin` directory, or run each command below through `elan run leanprover/lean4:v4.19.0`. Run from the root of this repository.

```sh
reproduction=reproducibility/paper-ii-portfolio-20261113
bash "$reproduction/prepare-dependencies.sh" run-results/paper-ii-mathlib
python3 "$reproduction/reproduce.py" \
  --mathlib run-results/paper-ii-mathlib \
  --output run-results/paper-ii
```

The dependency preparation step requires network access to fetch the pinned Mathlib source, its eight package dependencies, and the compiled cache for the project’s 40 Mathlib imports and their dependencies. If those caches are already prepared, pass the existing clean pinned Mathlib checkout to `--mathlib`. For a separately installed compiler, pass `--lean /path/to/lean`; its matching `lake` executable should be beside it. The output directory must be new. After a failed run, keep that directory for diagnostics and use a fresh output directory to rerun.

The [GitHub Actions workflow](../../.github/workflows/reproduce-paper-ii-portfolio.yml) prepares the same dependency cache and runs the same verifier on Linux. The [source manifest](source-manifest.json) records the module order, hashes, and exact revisions. The [audit baseline](AuditBaseline.json) records the declaration signatures and per-entry compiler payload hashes that passed independent review.

## Checks and evidence

- The runner validates the archived source bytes and exact dependency revisions, then rebuilds all 34 project modules directly from source. It builds the five proof modules again in a fresh Lake package and compares all ten same-run `.olean` and `.ilean` products.
- The 34-module integration import, declaration inventory, and mathematical audit run at Lean trust level zero. Every one of the 274 mathematical declarations receives a kernel type and body check, a body/type agreement check, and transitive axiom collection. The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- The runner checks that mathematical payloads refer to none of the 112 compiler-generated runtime entries. It matches every runtime inventory record and exact printed payload hash to the previously reviewed baseline. This check covers compiler/proof separation. Runtime implementations of real differentiation carry no mathematical verification.
- Proof and audit invocations use one Lean worker, 200,000 heartbeats, and recursion depth 512. Each child process group has a 180-second watchdog with cleanup through 185 seconds. The dependency download is a separate preparation step.
- Success writes `Verification.json` to the requested output directory. The same directory contains process logs, the compiled kind inventory and runtime payload dump, and the per-declaration kernel receipts. The import check covers the 34 project modules and their dependencies. The larger historical archive was outside this run’s scope.

The ten proof build products are compared within each run. A platform’s compiled bytes can differ from the archived Apple Silicon products. The declaration signatures and runtime payloads are checked against the audited baseline on each run.
