#!/usr/bin/env python3
"""Check the original Lake lock and all nine checked-out dependency revisions."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess

PACKAGE = Path(__file__).resolve().parents[1]
LOCK_SHA256 = "3be44af9233041c64d66893ee72eed54fc6ab6bf9672711848eaed875e5aeb61"
PINS_SHA256 = "128860386f89571c3a5be57bfeb36762f52e04ec5efce30c680130f1e91fbc2c"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packages-dir", type=Path, default=PACKAGE / ".lake/packages")
    parser.add_argument("--receipt", required=True, type=Path)
    args = parser.parse_args()
    for name, expected in [("lake-manifest.json", LOCK_SHA256), ("toolchain.json", PINS_SHA256)]:
        if sha256((PACKAGE / name).read_bytes()).hexdigest() != expected:
            raise ValueError(f"Published dependency pins changed: {name}")
    pins = json.loads((PACKAGE / "toolchain.json").read_text())["dependency_pins"]
    locked = {p["name"]: p["rev"] for p in json.loads((PACKAGE / "lake-manifest.json").read_text())["packages"]}
    if locked != pins:
        raise ValueError("Lockfile and published dependency pins disagree")
    checked = {}
    for name, expected in sorted(pins.items()):
        repo = args.packages_dir / name
        actual = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()
        if actual != expected:
            raise ValueError(f"Wrong dependency commit: {name}: {actual}")
        subprocess.run(["git", "-C", str(repo), "diff", "--quiet", "HEAD", "--"], check=True)
        checked[name] = actual
    result = {"lock_sha256": LOCK_SHA256, "dependency_commits": checked,
              "tracked_sources_unmodified": True}
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    args.receipt.write_text(json.dumps(result, indent=2) + "\n")
    print(f"PASS: lockfile and {len(checked)} clean dependency checkouts match the published pins")


if __name__ == "__main__":
    main()
