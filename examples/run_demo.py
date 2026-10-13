#!/usr/bin/env python3
"""Produce a repeatable offline demonstration and retain its actual execution evidence."""
import argparse
import contextlib
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "tests"))
import lean_backup as b
from fixtures import bytes_inventory, create_fixture


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.absolute()
    output.mkdir(mode=0o700, parents=False, exist_ok=False)
    source, vault = output / "synthetic-source", output / "vault.git"
    config = create_fixture(source)
    config_path = output / "config.json"
    config_path.write_bytes(b.encoded(config))
    before = bytes_inventory(source)
    commands = []

    def run(*args):
        argv = [sys.executable, str(ROOT / "lean_backup.py"), *map(str, args)]
        r = subprocess.run(argv, capture_output=True, text=True)
        commands.append({"argv": argv, "exit_code": r.returncode, "stdout": r.stdout, "stderr": r.stderr})
        (output / "commands.json").write_bytes(b.encoded(commands))
        if r.returncode:
            raise RuntimeError(f"Demo command failed: {argv}; see commands.json")
        return json.loads(r.stdout)

    run("init", "--config", config_path, "--vault", vault)
    first = run("checkpoint", "--vault", vault, "--id", 1)
    assert before == bytes_inventory(source)
    (source / "project/Fixture.lean").write_text("-- Second synthetic fixture version; not compiled.\ntheorem fixture : 3 = 3 := rfl\n")
    (source / "reports/correspondence.json").write_bytes(b.encoded({"synthetic": True, "version": 2, "compiled": False}))
    (source / "logs/build.log").write_text("SYNTHETIC version 2. No Lean command was executed.\n")
    (source / "checklist.json").write_bytes(b.encoded({"synthetic": True, "checkpoints": [1, 2]}))
    version_two = bytes_inventory(source)
    second = run("checkpoint", "--vault", vault, "--id", 2)
    assert version_two == bytes_inventory(source)
    first_restore = run("restore", "--vault", vault, "--id", 1, "--destination", output / "restored-v1")
    second_restore = run("restore", "--vault", vault, "--id", 2, "--destination", output / "restored-v2")
    run("verify", "--vault", vault)
    run("list", "--vault", vault)

    # The production CLI supports only private GitHub. Replace just the identity
    # and URL provider in this offline harness; real Git transport is exercised.
    remote = output / "simulated-remote.git"
    b.new_git(remote)
    identity = {"github_repository": "synthetic/private-demo", "repository_id": 1, "private": True}
    ctl = b.control(vault)
    ctl["remote"] = identity
    b.atomic_json(vault / "backup-control.json", ctl)
    with patch.object(b, "remote_url", return_value=str(remote)), patch.object(b, "github_identity", return_value=identity):
        transport = b.sync(vault)
        assert transport["status"] == "REMOTE_VERIFIED"
        recovered = b.recover(identity["github_repository"], output / "recovered-vault.git", second["commit"])
        assert recovered["status"] == "REMOTE_RECOVERY_VERIFIED"
    remote_restore = run("restore", "--vault", output / "recovered-vault.git", "--id", 1,
                         "--destination", output / "restored-from-simulated-remote")
    assert version_two == bytes_inventory(source)
    summary = {"synthetic_only": True, "actual_github_transfer": False, "lean_compilation_executed": False,
               "run_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
               "git_version": subprocess.check_output(["git", "--version"], text=True).strip(),
               "python_version": sys.version, "first_checkpoint": first, "second_checkpoint": second,
               "first_restore": first_restore, "second_restore": second_restore,
               "local_transport_simulation": transport, "local_transport_recovery": recovered,
               "remote_fixture_restore": remote_restore, "original_fixture_unchanged_by_tool": True,
               "source_tool_sha256": hashlib.sha256((ROOT / "lean_backup.py").read_bytes()).hexdigest()}
    (output / "demo-result.json").write_bytes(b.encoded(summary))
    print(json.dumps({"status": "OFFLINE_DEMO_PASSED", "output": str(output),
                      "checkpoint_commits": [first["commit"], second["commit"]],
                      "github_transfer": False, "source_unchanged_by_tool": True}, indent=2))


if __name__ == "__main__":
    main()
