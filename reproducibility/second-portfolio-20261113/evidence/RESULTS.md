# Recorded reproduction results

Status: **PASS**. This is the result of the new run, not a restatement of the historical checkpoint.

- Freshly compiled project modules: 598/598.
- Endpoint audit passes: 4/4.
- Failed compiler/audit jobs: 0; blocked dependent modules: 0.
- Recorded first-party build and endpoint-check time: 1073.155 seconds.
- Host: Linux x86_64; Lean 4.19.0; four module jobs, one worker per Lean process.
- Mathlib and all eight transitive package Git revisions match the frozen lockfile.
- All 598 project sources were compiled from source; historical project products were not seeded.
- The Lean search path contains only this standalone project, its pinned packages, and the official toolchain.

## Preserved records and byte comparison

- All 25 public checkpoint source SHA-256 hashes match.
- All 50 original compiled product hashes, the original archive hash, and the original verification report hash match the public summary.
- The original public-repository working copy is clean. No existing proof, manuscript, report, compiled product, or historical record was changed.
- Fresh checkpoint product comparison: 50 match, 0 differ, 0 missing. See `fresh-product-comparison.json`; byte equality and logical verification are distinct checks.

## Environment preparation

The first two official Mathlib cache attempts stopped with HTTP 429 (4,402 and 2,586 failed downloads respectively). They are retained as failed preparation logs. The third attempt limited curl concurrency to four and rate to four requests per second, downloaded all remaining entries, and unpacked the 6,641 requested cache entries. The fresh project build then ran with `--skip-cache` against this prepared pinned cache.

## Limits of the result

The 598-module closure targets the four endpoints of three statements. It does not rerun the historical 797-import integration root or the separate historical full declaration/runtime audit. The new endpoint audit checks the four theorem declarations, their kernel proof bodies, closedness, safe/non-partial status, and exact allowed transitive axiom set.

The published theorem inputs remain exactly as in the original summary. They are explicit parameters, not newly introduced axioms. An axiom print containing only `propext`, `Classical.choice`, and `Quot.sound` does not discharge these external theorem parameters.

The 25 target sources have no proof-limit overrides. Seventeen older dependency sources retain their original heartbeat settings. No override was introduced or increased for this reproduction.

This is not complete Lean verification or human verification of the Tarry convergence theorem. The checkpoint-recorded obligations I1113-I1138, I472, and I773 remain open. No new proof was attempted.

The source ZIP includes every project dependency used by the target closure. The initial Lean/Mathlib preparation still needs network access. Compiler binaries and third-party dependency trees are not included; all their revisions are pinned. Other operating systems and the proposed GitHub Actions workflow have not been executed here.

## Evidence

- `fresh-run/build-summary.json`: each command, exit code, timeout, source-module result, blocked dependency and output hash.
- `fresh-run/Repro.Endpoints.log` and `fresh-run/Repro.AuditEndpoints.log`: actual declaration signatures and endpoint audits, if reached.
- `fresh-run/*.log`: full logs for every attempted project module.
- `original-checkpoint-preservation.json`: preserved original source/product/report hash verification.
- `integrity-negative-checks.json`: changed-source, missing-dependency, and altered-pin rejection checks.
- `environment.json`, `lean-search-path.json`, and the three Mathlib cache logs: environment and preparation evidence.

## Proposed GitHub changes

Only a new `reproducibility/second-portfolio-20261113/` package directory, a new `REPRODUCIBILITY.md`, and a new dedicated workflow are proposed. No existing file is changed. The attached patch is based on repository commit `12f7745a8963901f321d8c9ede8825a94501459b`. No commit, push, pull request, or public repository write has been made. Applying it requires explicit user approval.
