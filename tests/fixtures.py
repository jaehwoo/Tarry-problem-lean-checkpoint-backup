"""Synthetic data only. The Lean snippet and example logs are not execution claims."""
import hashlib
import json
from pathlib import Path
import subprocess


def create_fixture(root):
    root = Path(root)
    project = root / "project"
    project.mkdir(parents=True)
    files = {
        "project/lean-toolchain": "leanprover/lean4:v4.19.0\n",
        "project/lake-manifest.json": json.dumps({"version": "1.1.0", "packages": [
            {"name": "mathlib", "rev": "c44e0c8ee63ca166450922a373c7409c5d26b00b"}]}),
        "project/lakefile.lean": 'import Lake\nopen Lake DSL\npackage «BackupFixture»\nlean_lib Fixture\n',
        "project/Fixture.lean": "-- Synthetic backup fixture; not compiled in these tests.\ntheorem fixture : 2 + 2 = 4 := by decide\n",
        "project/.gitignore": "ignored.bin\n",
        "project/.gitattributes": "*.lean text eol=crlf filter=do-not-run\n",
        "project/run.sh": "#!/bin/sh\nexit 0\n",
        "manuscript/paper.tex": "\\documentclass{article}\n\\begin{document}\nSynthetic source: $2+2=4$.\n\\end{document}\n",
        "reports/correspondence.json": json.dumps({"synthetic": True, "claims": [
            {"manuscript": "example", "lean": "fixture", "dependencies": ["Nat"], "compiled": False}]}),
        "logs/build.log": "SYNTHETIC: no Lean build was executed.\n",
        "logs/axioms.log": "SYNTHETIC: no #print axioms command was executed.\n",
        "checklist.json": json.dumps({"synthetic": True, "checkpoints": [], "main_theorem": "not verified"}),
    }
    for name, content in files.items():
        p = root / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
    (project / "ignored.bin").write_bytes(b"\x00\x01\xff\r\n")
    (project / "space 한글.txt").write_bytes(b"exact\r\nbytes\n")
    (project / "empty.bin").write_bytes(b"")
    (project / "empty-directory").mkdir()
    (project / "run.sh").chmod(0o755)
    subprocess.run(["git", "init", "--template=", str(project)], check=True, capture_output=True)
    # Include a marker in original Git metadata so tests detect unintended mutations.
    (project / ".git" / "DO_NOT_CHANGE").write_text("original source git metadata\n")
    config = {"schema": 1, "inputs": [
        {"name": "project", "role": "project", "path": str(project),
         "required": ["Fixture.lean", "lean-toolchain", "lake-manifest.json", "lakefile.lean"]},
        {"name": "manuscript", "role": "manuscript", "path": str(root / "manuscript" / "paper.tex"),
         "expected_sha256": hashlib.sha256((root / "manuscript" / "paper.tex").read_bytes()).hexdigest()},
        {"name": "correspondence", "role": "correspondence", "path": str(root / "reports" / "correspondence.json")},
        {"name": "verification", "role": "verification", "path": str(root / "logs"),
         "required": ["build.log", "axioms.log"]},
        {"name": "checklist", "role": "checklist", "path": str(root / "checklist.json")},
    ]}
    return config


def bytes_inventory(root):
    return {p.relative_to(root).as_posix(): (hashlib.sha256(p.read_bytes()).hexdigest(), p.stat().st_mode)
            for p in sorted(root.rglob("*")) if p.is_file() and not p.is_symlink()}
