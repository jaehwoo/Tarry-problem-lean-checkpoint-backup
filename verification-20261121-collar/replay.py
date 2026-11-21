"""Build each revision source in a fresh directory and audit its proof dependencies."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time


PACKAGE = Path(__file__).resolve().parent


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def lake_paths():
    def query(*args):
        return subprocess.check_output(["lake", "env", *args], cwd=PACKAGE, text=True).strip()

    prefix = Path(query("lean", "--print-prefix"))
    binary = prefix / "bin" / ("lean.exe" if os.name == "nt" else "lean")
    libraries = query(sys.executable, "-c", "import os; print(os.environ['LEAN_PATH'])")
    return binary, libraries


def verify_manifest(directory, name):
    files = json.loads((directory / name).read_text())
    for rel, expected in files.items():
        if digest(directory / rel) != expected:
            raise ValueError(f"SHA-256 mismatch in {rel}")
    return files


def run():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, help="New empty directory for build and audit evidence")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--lean", type=Path, help="Exact pinned binary for an existing mathlib installation")
    parser.add_argument("--mathlib-paths", help="Upstream library paths only, separated by the OS path separator")
    args = parser.parse_args()
    if args.jobs < 1 or (args.lean is None) != (args.mathlib_paths is None):
        parser.error("Use a positive job count and supply both override options together.")
    if args.lean is None:
        lean, libraries = lake_paths()
    else:
        lean, libraries = args.lean.resolve(), args.mathlib_paths
    upstream = [str((PACKAGE / path).resolve()) for path in libraries.split(os.pathsep) if path]
    if any((Path(path) / name).exists() for name in ("Revision", "PaperILean") for path in upstream):
        parser.error("The upstream search path contains project objects. Supply only upstream mathlib libraries.")
    out = args.out.resolve() if args.out else Path(tempfile.mkdtemp(prefix="tarry-collar-"))
    out.mkdir(parents=True, exist_ok=True)
    if any(out.iterdir()):
        parser.error(f"Output directory must be empty: {out}")
    evidence = out / "evidence"
    evidence.mkdir()
    build = out / "build"
    (build / "Revision").mkdir(parents=True)
    sources = verify_manifest(PACKAGE, "sources.sha256.json")
    baseline = verify_manifest(PACKAGE / "baseline", "SHA256SUMS.json")
    version = subprocess.check_output([str(lean), "--version"], text=True).strip()
    if "version 4.19.0," not in version or "commit 6caaee842e94" not in version:
        raise RuntimeError(f"Expected pinned Lean 4.19.0. Found {version}")
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([str(build), str(PACKAGE / "baseline"), *upstream])
    env["LEAN_NUM_THREADS"] = "1"
    flags = [str(lean), "--root=" + str(PACKAGE), "-t0", "-j1", "-DmaxHeartbeats=200000", "-DmaxRecDepth=512"]
    files = {".".join(Path(rel).with_suffix("").parts): PACKAGE / rel
             for rel in sources if rel.startswith("Revision") and rel.endswith(".lean")}
    dependencies = {name: set(re.findall(r"^import (Revision(?:\.\w+)*)\s*$", path.read_text(), re.M))
                    for name, path in files.items()}
    if any(dep not in files for deps in dependencies.values() for dep in deps):
        raise RuntimeError("Missing revision import")
    for path in files.values():
        if re.search(r"\b(sorry|admit|axiom|native_decide|ofReduceBool|reduceBool)\b", path.read_text()):
            raise RuntimeError(f"Unexpected placeholder or native proof primitive in {path.name}")

    def execute(name, source, output=None):
        command = flags + (["-o", str(output)] if output else []) + [str(source)]
        started = time.monotonic()
        log = evidence / (name + ".log")
        with log.open("w") as stream:
            result = subprocess.run(command, env=env, cwd=out, stdout=stream, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f"{name} exited {result.returncode}\n{log.read_text()[-3000:]}")
        return {"module": name, "command": command, "seconds": round(time.monotonic() - started, 3),
                "object_sha256": digest(output) if output else None}

    start = time.monotonic()
    print(f"{version}\n{len(baseline)} inherited hashes verified. Starting a fresh build in {out}.", flush=True)
    records, finished, running = [], set(), {}
    remaining = set(files)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while remaining or running:
            ready = sorted(name for name in remaining if dependencies[name] <= finished)
            for name in ready[:args.jobs - len(running)]:
                target = build.joinpath(*name.split(".")).with_suffix(".olean")
                running[pool.submit(execute, name, files[name], target)] = name
                remaining.remove(name)
            if not running:
                raise RuntimeError("Cycle in revision imports")
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                name = running.pop(future)
                records.append(future.result())
                finished.add(name)
                print(f"Compiled {name}", flush=True)
    records.append(execute("audit", PACKAGE / "Audit.lean"))
    summary = (evidence / "closure-summary.txt").read_text()
    if "PASS:" not in (evidence / "audit.log").read_text():
        raise RuntimeError("The declaration audit did not finish")
    loaded = (evidence / "loaded-project-modules.txt").read_text().splitlines()
    imported = {n.replace(".", "/") + ".olean" for n in loaded if n.startswith("PaperILean.")}
    if set(baseline) != imported:
        raise RuntimeError("The inherited manifest and the actual imported project modules differ")
    receipt = {"compiler": version, "baseline_count": len(baseline), "baseline_manifest_sha256":
               digest(PACKAGE / "baseline/SHA256SUMS.json"), "source_manifest_sha256":
               digest(PACKAGE / "sources.sha256.json"), "elapsed_seconds": round(time.monotonic() - start, 3),
               "builds": records, "upstream_search_paths": upstream}
    (evidence / "build.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(summary + f"Complete evidence in {evidence}")


if __name__ == "__main__":
    run()
