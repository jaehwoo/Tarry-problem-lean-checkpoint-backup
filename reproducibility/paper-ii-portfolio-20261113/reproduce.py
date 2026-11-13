#!/usr/bin/env python3
"""Rebuild and audit the 13 November 2026 Paper II verification portfolio."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import sys
import zipfile

from process_watchdog import OUTER_SECONDS, WALL_SECONDS, run


HERE = Path(__file__).resolve().parent
LIMITS = ["-j1", "-DmaxHeartbeats=200000", "-DmaxRecDepth=512"]
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PROJECT_MODULE = re.compile(r"PaperILean\.[A-Za-z][A-Za-z0-9]*")
IMPORT = re.compile(r"^import (\S+)", re.MULTILINE)
NO_PROOF_BYPASS = re.compile(
    r"\b(sorry|admit|native_decide|axiom|unsafe|partial)\b"
    r"|^\s*set_option\s+(maxHeartbeats|maxRecDepth)\b",
    re.MULTILINE,
)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def module_path(module, suffix):
    return Path(module.replace(".", "/") + suffix)


def extract_sources(source_root, manifest, proof_modules):
    archive = HERE / "project-sources.zip"
    require(sha(archive) == manifest["project_sources_sha256"], "Project source archive hash mismatch")
    order, rows = manifest["module_order"], manifest["sources"]
    require(len(order) == len(set(order)) == len(rows) == 34 and set(order) == set(rows),
            "Expected exactly 34 distinct, ordered project modules")
    require(set(proof_modules) <= set(order), "Proof module missing from the source manifest")
    paths = {}
    for name in order:
        require(PROJECT_MODULE.fullmatch(name), f"Invalid module name: {name}")
        expected = module_path(name, ".lean").as_posix()
        require(rows[name]["path"] == expected, f"Unexpected source path: {name}")
        paths[expected] = name
    completed = set()
    with zipfile.ZipFile(archive) as bundle:
        members = bundle.infolist()
        require(len(members) == len(paths) and {item.filename for item in members} == set(paths),
                "Unexpected, duplicate, or missing ZIP members")
        for item in members:
            require(not item.is_dir() and stat.S_IFMT(item.external_attr >> 16) in {0, stat.S_IFREG},
                    f"Nonregular ZIP entry: {item.filename}")
        for module in order:
            record = rows[module]
            raw = bundle.read(record["path"])
            require(hashlib.sha256(raw).hexdigest() == record["sha256"], f"Source hash mismatch: {module}")
            source = raw.decode("utf-8")
            imports = IMPORT.findall(source)
            require(imports == record["imports"], f"Source imports differ from manifest: {module}")
            project_imports = {name for name in imports if name.startswith("PaperILean.")}
            require(project_imports <= completed, f"Project imports out of order or missing: {module}")
            if module in proof_modules:
                active = re.sub(r"/-(?:.|\n)*?-/", "", source)
                active = re.sub(r"--[^\n]*", "", active)
                require(not NO_PROOF_BYPASS.search(active), f"Unexpected proof construct: {module}")
            path = source_root / record["path"]
            path.write_bytes(raw)
            completed.add(module)
    combined = (HERE / "PaperIIReproduction.lean").read_bytes()
    require(hashlib.sha256(combined).hexdigest() == manifest["root_module_sha256"],
            "Combined import source hash mismatch")
    imports = IMPORT.findall(combined.decode("utf-8"))
    require(len(imports) == len(order) and set(imports) == set(order), "Combined import scope mismatch")
    (source_root / "PaperIIReproduction.lean").write_bytes(combined)
    return order


def verify_inventory(evidence, baseline):
    inventory = read_json(evidence / "Compiled_Kind_Inventory.json")
    require(inventory["status"] == "PASS_READ_ONLY_INVENTORY", "Compiled inventory failed")
    require(inventory["all_safe_payloads_exclude_unsafe"] and inventory["payloads_include_recursor_rule_rhs"],
            "Compiled inventory omitted a safety check")
    rows = inventory["constants"]
    require(len(rows) == len({r["name"] for r in rows}) == inventory["constant_count"] == 386,
            "Unexpected compiled declaration count or duplicate")
    require(not any(row["isPartial"] for row in rows), "Unexpected partial declaration")
    math = [row for row in rows if not row["isUnsafe"]]
    runtime = {row["name"]: row for row in rows if row["isUnsafe"]}
    require(len(math) == inventory["safe_count"] == 274 and len(runtime) == inventory["unsafe_count"] == 112,
            "Unexpected mathematical/runtime split")
    require(all(row["body_hash"] and row["kind"] in {"definition", "theorem", "opaque"} for row in math),
            "Unexpected mathematical declaration requiring structural replay")
    require(all(not row["unsafe_references"] and not (runtime.keys() & set(row["payload_references"]))
                for row in math), "Mathematical declaration references compiler runtime")
    require({row["name"]: [row["kind"], row["type_hash"], row["body_hash"]] for row in math}
            == baseline["safe_kind_type_body"], "Mathematical declaration signatures differ from the audited baseline")
    require(runtime.keys() == baseline["reviewed_runtime"].keys(), "Unexpected compiler-runtime name set")
    blocks = re.split(rb"(?m)(?=^NAME )", (evidence / "Unsafe_Compiled_Payloads.txt").read_bytes())
    payloads = {}
    for block in filter(None, blocks):
        name = block.splitlines()[0].removeprefix(b"NAME ").decode()
        require(name not in payloads, f"Duplicate runtime payload: {name}")
        payloads[name] = hashlib.sha256(block).hexdigest()
    require(payloads.keys() == runtime.keys(), "Incomplete compiler-runtime payload dump")
    for name, row in runtime.items():
        reference = baseline["reviewed_runtime"][name]
        require(row == reference["inventory"] and payloads[name] == reference["payload_sha256"],
                f"Runtime payload differs from independent review: {name}")
    return math, runtime


def run_audits(execute, lean, out, search_paths, constants):
    template = (HERE / "Audit.lean").read_text(encoding="utf-8")
    preamble, block = template.split("run_cmd do\n", 1)
    selected = 'let some selected ← liftIO (IO.getEnv "AFFINE_AUDIT_NAMES") | throwError "missing selected names"'
    output = 'let some output ← liftIO (IO.getEnv "AFFINE_AUDIT_OUTPUT") | throwError "missing output path"'
    require(block.count(selected) == block.count(output) == 1, "Invalid audit template")
    for offset in range(0, len(constants), 15):
        batch = constants[offset:offset + 15]
        program = preamble
        for index, row in enumerate(batch, offset):
            selected_literal = json.dumps(row["name"], ensure_ascii=False)
            program += "run_cmd do\n" + block.replace(selected, "let selected := " + selected_literal).replace(
                output, f'let output := "evidence/decl-{index}"')
        audit = out / f"Audit_{offset}.lean"
        audit.write_text(program, encoding="utf-8")
        execute(f"audit-{offset}", [lean, *LIMITS, "-t0", audit], out, search_paths)
        for index, row in enumerate(batch, offset):
            stem = out / "evidence" / f"decl-{index}"
            fields = stem.with_suffix(".hashes").read_text(encoding="utf-8").strip().split("; ")
            require(fields[:3] == [row["name"], "type_hash=" + row["type_hash"], "body_hash=" + row["body_hash"]]
                    and len(fields) == 4, f"Incomplete kernel receipt: {row['name']}")
            match = re.fullmatch(r"axioms=#\[(.*)\]", fields[3])
            require(match is not None and set(filter(None, match.group(1).split(", "))) <= STANDARD_AXIOMS,
                    f"Unapproved axioms: {row['name']}")
            require(stem.with_suffix(".progress").read_text(encoding="utf-8").splitlines()
                    == ["AUDIT START", "BEGIN " + row["name"], "CHECKED " + row["name"] + "; " + fields[3]],
                    f"Incomplete audit progress: {row['name']}")


def fresh_lake_build(execute, lake, out, upstream, sources, direct, modules, proof_modules, core_lib):
    fresh = out / "fresh"
    dependency = out / "lake-dependencies"
    fresh_lib = fresh / ".lake/build/lib/lean"
    dependency_lib = dependency / ".lake/build/lib/lean"
    (fresh / "PaperILean").mkdir(parents=True)
    (fresh_lib / "PaperILean").mkdir(parents=True)
    dependency_lib.mkdir(parents=True)
    (dependency_lib / "PaperILean").symlink_to(fresh_lib / "PaperILean", target_is_directory=True)
    for module in modules:
        if module in proof_modules:
            relative = module_path(module, ".lean")
            shutil.copyfile(sources / relative, fresh / relative)
        else:
            for suffix in (".olean", ".ilean"):
                relative = module_path(module, suffix)
                (fresh_lib / relative).symlink_to(direct / relative)
    for folder in (fresh, dependency):
        shutil.copyfile(HERE / "lean-toolchain", folder / "lean-toolchain")
    (dependency / "lakefile.toml").write_text('name = "TarryScopedDependencies"\n', encoding="utf-8")
    (fresh / "lakefile.toml").write_text(
        'name = "TarryFreshPaperII"\n'
        f'moreLeanArgs = {json.dumps(LIMITS)}\n'
        '[[require]]\nname = "TarryScopedDependencies"\npath = "../lake-dependencies"\n'
        f'[[lean_lib]]\nname = "PaperILean"\nroots = {json.dumps(proof_modules)}\n',
        encoding="utf-8",
    )
    for lib in upstream:
        if lib == core_lib or not lib.is_dir():
            continue
        for namespace in lib.iterdir():
            if not namespace.is_dir() and namespace.suffix not in {".olean", ".ilean"}:
                continue
            destination = dependency_lib / namespace.name
            require(not destination.exists(), f"Conflicting dependency namespace: {namespace.name}")
            destination.symlink_to(namespace, target_is_directory=namespace.is_dir())
    execute("lake-update", [lake, "update"], fresh, upstream)
    products = {}
    for module in proof_modules:
        execute("lake-" + module.split(".")[-1], [lake, "build", f"+{module}:leanArts"], fresh, upstream)
        for suffix in (".olean", ".ilean"):
            relative = module_path(module, suffix)
            digest = sha(fresh_lib / relative)
            require(digest == sha(direct / relative), f"Direct and fresh Lake products differ: {relative}")
            products[relative.as_posix()] = digest
    return products


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib", type=Path, required=True, help="Pinned Mathlib checkout with prepared caches")
    parser.add_argument("--output", type=Path, required=True, help="New directory for logs and build products")
    parser.add_argument("--lean", type=Path, help="Lean executable, with matching lake beside it")
    args = parser.parse_args()
    mathlib = args.mathlib.resolve(strict=True)
    out = args.output.resolve()
    candidate = args.lean or shutil.which("lean")
    require(candidate, "Lean was not found; install Lean 4.19.0 or pass --lean")
    lean = Path(candidate).absolute()
    lake = lean.with_name("lake")
    require(lean.is_file() and lake.is_file(), "Lean and matching Lake executables are required")
    require(not out.exists(), f"Output directory already exists: {out}")
    (out / "evidence").mkdir(parents=True)
    shutil.copyfile(HERE / "lean-toolchain", out / "lean-toolchain")
    sources, direct = out / "sources", out / "direct"
    for path in (sources, direct):
        (path / "PaperILean").mkdir(parents=True)
    baseline = read_json(HERE / "AuditBaseline.json")
    manifest = read_json(HERE / "source-manifest.json")
    proof_modules = baseline["proof_modules"]
    require(len(set(proof_modules)) == len(proof_modules) == 5, "Expected five proof modules")
    require({m: manifest["sources"][m]["sha256"] for m in proof_modules} == baseline["reference_sources"],
            "Proof source hashes differ from the audit baseline")
    modules = extract_sources(sources, manifest, proof_modules)
    pins = manifest["dependency_pins"]
    require(len(pins) == 9 and "mathlib" in pins, "Expected the nine dependency revisions")
    env = os.environ.copy()
    env["PATH"] = str(lean.parent) + os.pathsep + env.get("PATH", "")
    env["LEAN_NUM_THREADS"] = "1"
    for variable in ("LEAN_PATH", "LEAN_SRC_PATH", "LD_PRELOAD", "DYLD_INSERT_LIBRARIES"):
        env.pop(variable, None)
    receipts = []

    def execute(label, command, cwd, search_paths=None):
        effective = env.copy()
        if search_paths is not None:
            effective["LEAN_PATH"] = os.pathsep.join(map(str, search_paths))
        result = run(list(map(str, command)), cwd=cwd, env=effective, text=True, capture_output=True)
        log = out / (label + ".log")
        log.write_text(result.stdout + result.stderr, encoding="utf-8")
        receipts.append({"step": label, "exit_code": result.returncode,
                         "timed_out": result.timed_out, "seconds": round(result.seconds, 3),
                         "log_sha256": sha(log)})
        write_json(out / "commands.json", receipts)
        print(f"{label}: {result.returncode}", flush=True)
        if result.returncode:
            print(log.read_text(encoding="utf-8"), file=sys.stderr)
            raise SystemExit(result.returncode)
        return result.stdout.strip()

    version = execute("lean-version", [lean, "--version"], out)
    require("version 4.19.0," in version and "commit " + manifest["compiler_revision"] in version,
            f"Unexpected Lean compiler: {version}")
    core_lib = Path(execute("lean-libdir", [lean, "--print-libdir"], out)).resolve()
    for name, pin in pins.items():
        checkout = mathlib if name == "mathlib" else mathlib / ".lake/packages" / name
        actual = execute(f"pin-{name}", ["git", "rev-parse", "HEAD"], checkout)
        require(actual == pin, f"Pinned revision mismatch: {name}")
        modified = execute(f"tracked-status-{name}", ["git", "status", "--porcelain", "--untracked-files=no"], checkout)
        require(not modified, f"Modified tracked dependency source: {name}")
    raw_path = execute("lake-env", [lake, "env", "printenv", "LEAN_PATH"], mathlib)
    upstream = [(mathlib / name).resolve() for name in raw_path.split(os.pathsep) if name]
    import_roots = (HERE / "mathlib-imports.txt").read_text(encoding="utf-8").splitlines()
    expected_roots = sorted({name for row in manifest["sources"].values()
                             for name in row["imports"] if name.startswith("Mathlib.")})
    require(import_roots == expected_roots and bool(import_roots), "Mathlib import inventory mismatch")
    missing = [name for name in import_roots
               if not any((path / module_path(name, ".olean")).is_file() for path in upstream)]
    require(not missing, "Pinned Mathlib cache is missing: " + ", ".join(missing))
    require(not any((path / "PaperILean").exists() for path in upstream), "Unexpected cached project modules")
    search_paths = [direct, *upstream]
    for module in modules:
        relative = module_path(module, ".lean")
        execute("direct-" + relative.stem,
                [lean, *LIMITS, f"--root={sources}", "-o", direct / relative.with_suffix(".olean"),
                 "-i", direct / relative.with_suffix(".ilean"), sources / relative],
                sources, search_paths)
    products = fresh_lake_build(execute, lake, out, upstream, sources, direct, modules, proof_modules, core_lib)
    execute("combined-34-imports", [lean, *LIMITS, "-t0", sources / "PaperIIReproduction.lean"], out, search_paths)
    kinds = out / "AuditKinds.lean"
    shutil.copyfile(HERE / kinds.name, kinds)
    execute("compiled-kind-inventory", [lean, *LIMITS, "-t0", kinds], out, search_paths)
    math, runtime = verify_inventory(out / "evidence", baseline)
    run_audits(execute, lean, out, search_paths, math)
    require(all(sha(sources / row["path"]) == row["sha256"] for row in manifest["sources"].values()),
            "Project source changed during verification")
    write_json(out / "Verification.json", {
        "status": "PASS",
        "lean": version,
        "dependency_pins": pins,
        "source_modules_rebuilt": len(modules),
        "fresh_lake_proof_modules": proof_modules,
        "direct_and_lake_products_sha256": products,
        "scoped_import_count": len(modules),
        "full_historical_import_union_rechecked": False,
        "mathematical_declarations_kernel_checked": len(math),
        "compiler_runtime_entries_matched_to_independent_review": len(runtime),
        "compiler_runtime_references_in_math": 0,
        "compiled_inventory_sha256": sha(out / "evidence/Compiled_Kind_Inventory.json"),
        "runtime_payloads_sha256": sha(out / "evidence/Unsafe_Compiled_Payloads.txt"),
        "axiom_whitelist": sorted(STANDARD_AXIOMS),
        "lean_limits": {"maxHeartbeats": 200000, "maxRecDepth": 512, "workers": 1},
        "watchdog_seconds": {"wall": WALL_SECONDS, "cleanup_ends_by": OUTER_SECONDS},
    })
    print(f"PASS: {out / 'Verification.json'}", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, ValueError, zipfile.BadZipFile) as exc:
        raise SystemExit(f"FAIL: {exc}") from exc
