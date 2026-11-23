#!/usr/bin/env python3
"""Compare revision fingerprints and axiom output; record upstream closure drift."""
import argparse
from pathlib import Path
import json

PACKAGE = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    fresh, original = args.out / "evidence", PACKAGE / "evidence"
    for name in ("kernel-bodies.tsv", "loaded-project-modules.txt"):
        if sorted((fresh / name).read_text().splitlines()) != sorted((original / name).read_text().splitlines()):
            raise ValueError(f"Fresh audit differs from the historical record: {name}")
    receipt = json.loads((fresh / "build.json").read_text())
    if receipt["baseline_count"] != 1879 or len(receipt["builds"]) != 23:
        raise ValueError("Expected 22 compiled revision modules including root, and one audit")
    def summary(directory):
        return dict(line.split(" = ", 1) for line in (directory / "closure-summary.txt").read_text().splitlines())
    current, historical = summary(fresh), summary(original)
    for key in ("public entries", "rechecked revision bodies", "allowed axioms encountered"):
        if current[key] != historical[key]:
            raise ValueError(f"Fresh audit differs from the historical record: {key}")
    scanned = int(current["transitive declarations scanned"])
    log = (fresh / "audit.log").read_text()
    expected = f"PASS: 34 public entries, 92 revision bodies, {scanned} transitive mathematical declarations"
    if scanned < 92 or expected not in log:
        raise ValueError("Missing successful audit output")
    # Cached upstream theorem proof bodies can differ without changing their statements.
    # Compare all original per-entry axiom reports, while leaving the Lean audit intact.
    def axiom_lines(text):
        return sorted(line for line in text.splitlines() if " -> [" in line or "depends on axioms:" in line)
    if len(axiom_lines(log)) != 68 or axiom_lines(log) != axiom_lines((original / "audit.log").read_text()):
        raise ValueError("Per-entry axiom reports differ from the historical record")
    result = {"public_entries": 34, "revision_bodies": 92, "revision_fingerprints_match": True,
              "project_modules_match": True, "per_entry_axiom_reports_match": True,
              "historical_transitive_declarations": int(historical["transitive declarations scanned"]),
              "fresh_transitive_declarations": scanned}
    (fresh / "comparison.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"PASS: 34 entries, 92 revision fingerprints, project modules and all axiom reports agree; "
          f"transitive scan {scanned} (historical {result['historical_transitive_declarations']})")


if __name__ == "__main__":
    main()
