"""Integration checks for archive restoration and audit comparison."""
import argparse
import importlib.util
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

PACKAGE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("prepare_baseline", PACKAGE / "scripts/prepare_baseline.py")
prepare = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prepare)


class ReproductionChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="collar-reproduction-tests-")
        cls.package = Path(cls.temp.name) / "package"
        shutil.copytree(PACKAGE, cls.package, ignore=shutil.ignore_patterns(".lake", "PaperILean", "run-results", "__pycache__", "replay-run"))

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_01_restore_all_objects(self):
        result = prepare.restore(self.package, self.archive)
        self.assertEqual(result["object_count"], 1879)
        self.assertEqual(result["mode"], "restored-from-original-archive")
        self.assertEqual(len(list((self.package / "baseline/PaperILean").rglob("*.olean"))), 1879)

    def test_02_repeated_verification(self):
        self.assertEqual(prepare.restore(self.package, self.archive)["mode"], "verified-existing")

    def test_03_wrong_archive(self):
        wrong = Path(self.temp.name) / "wrong.zip"
        wrong.write_bytes(b"wrong archive")
        with self.assertRaisesRegex(ValueError, "archive SHA-256 mismatch"):
            prepare.restore(self.package, wrong)

    def test_04_changed_source(self):
        path = self.package / "Revision.lean"
        old = path.read_bytes()
        try:
            path.write_bytes(old + b"\n-- changed\n")
            with self.assertRaisesRegex(ValueError, "Published source differs"):
                prepare.restore(self.package, self.archive)
        finally:
            path.write_bytes(old)

    def test_05_changed_manifest(self):
        path = self.package / "baseline/SHA256SUMS.json"
        old = path.read_bytes()
        try:
            path.write_bytes(b"{}\n")
            with self.assertRaisesRegex(ValueError, "manifest differs"):
                prepare.restore(self.package, self.archive)
        finally:
            path.write_bytes(old)

    def test_06_conflicting_object(self):
        path = next((self.package / "baseline/PaperILean").glob("*.olean"))
        old = path.read_bytes()
        try:
            path.write_bytes(b"changed")
            with self.assertRaisesRegex(ValueError, "Existing inherited object differs"):
                prepare.restore(self.package, self.archive)
        finally:
            path.write_bytes(old)

    def test_07_comparison_rejects_changed_audit(self):
        out = Path(self.temp.name) / "audit-check"
        shutil.copytree(PACKAGE / "evidence", out / "evidence")
        path = out / "evidence/closure-summary.txt"
        path.write_text(path.read_text().replace("public entries = 34", "public entries = 33"))
        result = subprocess.run([sys.executable, str(PACKAGE / "scripts/check_results.py"), "--out", str(out)], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Fresh audit differs", result.stderr)

    def test_08_comparison_records_upstream_scan_difference(self):
        out = Path(self.temp.name) / "changed-scan"
        shutil.copytree(PACKAGE / "evidence", out / "evidence")
        for name in ("closure-summary.txt", "audit.log"):
            path = out / "evidence" / name
            path.write_text(path.read_text().replace("57733", "57715"))
        result = subprocess.run([sys.executable, str(PACKAGE / "scripts/check_results.py"), "--out", str(out)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("historical 57733", result.stdout)
        self.assertIn('"fresh_transitive_declarations": 57715', (out / "evidence/comparison.json").read_text())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", required=True, type=Path)
    args, remaining = parser.parse_known_args()
    ReproductionChecks.archive = args.archive.resolve()
    unittest.main(argv=[sys.argv[0], *remaining], verbosity=2)
