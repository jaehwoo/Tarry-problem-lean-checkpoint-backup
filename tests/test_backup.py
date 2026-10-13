import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import lean_backup as b
from fixtures import bytes_inventory, create_fixture


class BackupTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.source = self.base / "source"
        self.config = create_fixture(self.source)
        self.vault = self.base / "vault.git"
        b.init_vault(self.config, self.vault)

    def snap(self, n=1, **kwargs):
        return b.checkpoint(self.vault, n, **kwargs)

    def verified(self):
        return b.verify_vault(b.Git(self.vault), b.control(self.vault))

    def test_two_versions_and_exact_restore_without_source_changes(self):
        initial = bytes_inventory(self.source)
        first = self.snap()
        self.assertEqual(initial, bytes_inventory(self.source))
        (self.source / "project/Fixture.lean").write_text("-- second synthetic version\n")
        (self.source / "logs/build.log").write_text("SYNTHETIC revision 2, not a build\n")
        second_state = bytes_inventory(self.source)
        second = self.snap(2)
        checked = self.verified()
        for n in (1, 2):
            dest = self.base / f"restore-{n}"
            result = b.restore_from(b.Git(self.vault), checked, n, dest)
            self.assertEqual(result["status"], "RESTORE_VERIFIED")
            inv = checked["manifests"][n][1]["inventory"]
            restored = bytes_inventory(dest / "payload")
            self.assertEqual(set(restored), set(inv["files"]))
            for p, info in inv["files"].items():
                self.assertEqual(restored[p][0], info["sha256"])
                self.assertEqual((dest / "payload" / p).stat().st_mode & 0o777, info["mode"])
            self.assertTrue((dest / "payload/project/empty-directory").is_dir())
            self.assertFalse((dest / "payload/project/.git").exists())
        self.assertEqual(second_state, bytes_inventory(self.source))
        self.assertNotEqual(first["commit"], second["commit"])
        self.assertFalse(first["remote_verified"])
        self.assertIn("project/ignored.bin", checked["manifests"][1][1]["inventory"]["files"])

    def test_restore_does_not_require_sources_to_survive(self):
        self.snap()
        os.rename(self.source, self.base / "removed-source")
        checked = self.verified()
        result = b.restore_from(b.Git(self.vault), checked, 1, self.base / "restored")
        self.assertEqual(result["status"], "RESTORE_VERIFIED")

    def test_duplicate_id_cannot_overwrite(self):
        self.snap()
        before = b.Git(self.vault).refs()
        with self.assertRaises(b.BackupError):
            self.snap()
        self.assertEqual(before, b.Git(self.vault).refs())

    def test_numbering_gap_is_explicit(self):
        self.snap(16)
        with self.assertRaises(b.BackupError):
            self.snap(71)
        self.snap(71, allow_gap=True)
        result = b.summary(self.verified())
        self.assertEqual(result["sequence_gaps"], [[17, 70]])
        self.assertEqual(result["missing_before_first"], [1, 15])

    def test_manuscript_hash_and_immutable_baseline(self):
        self.snap()
        original_refs = b.Git(self.vault).refs()
        (self.source / "manuscript/paper.tex").write_text("altered manuscript\n")
        with self.assertRaisesRegex(b.BackupError, "hash mismatch"):
            self.snap(2)
        self.assertEqual(original_refs, b.Git(self.vault).refs())

    def test_first_snapshot_pin_mismatch_is_rejected(self):
        (self.source / "manuscript/paper.tex").write_text("wrong initial manuscript\n")
        with self.assertRaises(b.BackupError):
            self.snap()
        self.assertEqual(b.Git(self.vault).refs(), {})

    def test_manuscript_immutable_even_without_initial_hash(self):
        config = json.loads(json.dumps(self.config))
        config["inputs"][1].pop("expected_sha256")
        other = self.base / "unanchored.git"
        b.init_vault(config, other)
        b.checkpoint(other, 1)
        (self.source / "manuscript/paper.tex").write_text("altered\n")
        with self.assertRaisesRegex(b.BackupError, "manuscript changed"):
            b.checkpoint(other, 2)

    def test_missing_axioms_log_and_pinned_file_block_backup(self):
        for rel in ("logs/axioms.log", "project/lean-toolchain", "project/lake-manifest.json"):
            path = self.source / rel
            raw = path.read_bytes()
            path.unlink()
            with self.assertRaises(b.BackupError):
                self.snap()
            path.write_bytes(raw)
            self.assertEqual(b.Git(self.vault).refs(), {})

    def test_empty_evidence_is_rejected(self):
        (self.source / "logs/build.log").unlink()
        (self.source / "logs/axioms.log").unlink()
        with self.assertRaises(b.BackupError):
            self.snap()

    def test_symlink_and_fifo_are_rejected(self):
        path = self.source / "project/unsafe"
        path.symlink_to(self.source / "manuscript/paper.tex")
        with self.assertRaises(b.BackupError):
            self.snap()
        path.unlink()
        os.mkfifo(path)
        with self.assertRaises(b.BackupError):
            self.snap()

    def test_destination_overlap_and_existing_restore_are_rejected(self):
        with self.assertRaises(b.BackupError):
            b.init_vault(self.config, self.source / "project/backup.git")
        self.snap()
        checked = self.verified()
        for path in (self.source / "project/new", self.source / "project", self.vault / "restore", self.source.parent):
            with self.assertRaises(b.BackupError):
                b.restore_from(b.Git(self.vault), checked, 1, path)
        path = self.base / "existing"
        path.mkdir()
        (path / "marker").write_text("do not erase")
        with self.assertRaises(b.BackupError):
            b.restore_from(b.Git(self.vault), checked, 1, path)
        self.assertEqual((path / "marker").read_text(), "do not erase")

    def test_active_source_change_aborts_before_refs(self):
        real_scan = b.scan
        count = 0
        def changing(policy, stage=None):
            nonlocal count
            count += 1
            if count == 2:
                (self.source / "project/Fixture.lean").write_text("changed during snapshot\n")
            return real_scan(policy, stage)
        with patch.object(b, "scan", changing):
            with self.assertRaisesRegex(b.BackupError, "Source changed"):
                self.snap()
        self.assertEqual(b.Git(self.vault).refs(), {})

    def test_missing_and_corrupted_git_object_fail(self):
        self.snap()
        checked = self.verified()
        oid = checked["manifests"][1][2]["payload/project/Fixture.lean"][1]
        object_path = self.vault / "objects" / oid[:2] / oid[2:]
        raw = object_path.read_bytes()
        object_path.unlink()
        with self.assertRaises(b.BackupError):
            self.verified()
        object_path.write_bytes(b"corrupted object")
        with self.assertRaises(b.BackupError):
            self.verified()
        object_path.write_bytes(raw)
        self.verified()

    def test_valid_git_tree_with_wrong_manifest_hash_fails(self):
        self.snap()
        checked = self.verified()
        old, m, entries = checked["manifests"][1]
        git = b.Git(self.vault)
        entries["payload/project/Fixture.lean"] = ("100644", git.blob(b"tampered bytes\n"))
        tree = b.make_tree(git, entries)
        new = git.text("commit-tree", tree, data=b"simulate accidental mismatch\n")
        git.run("update-ref", TIP := b.TIP, new, old)
        git.run("update-ref", b.tag(1), new, old)
        # fsck alone passes, but the independent SHA-256 manifest must fail.
        b.check_repo(git)
        with self.assertRaisesRegex(b.BackupError, "SHA-256"):
            self.verified()

    def test_missing_checkpoint_ref_is_detected(self):
        self.snap()
        b.Git(self.vault).run("update-ref", "-d", b.tag(1))
        with self.assertRaisesRegex(b.BackupError, "ref missing"):
            self.verified()

    def test_catalog_corruption_is_detected(self):
        self.snap()
        checked = self.verified()
        old, _, entries = checked["manifests"][1]
        git = b.Git(self.vault)
        entries["catalog.json"] = ("100644", git.blob(b'{"schema":1,"records":[]}\n'))
        new = git.text("commit-tree", b.make_tree(git, entries), data=b"bad catalog\n")
        git.run("update-ref", b.TIP, new, old)
        git.run("update-ref", b.tag(1), new, old)
        with self.assertRaisesRegex(b.BackupError, "Catalog"):
            self.verified()

    def test_lock_conflict_does_not_publish(self):
        with b.lock(self.vault):
            with self.assertRaisesRegex(b.BackupError, "lock"):
                self.snap()

    def test_explicit_exclusion_is_recorded(self):
        other = self.base / "exclude.git"
        config = json.loads(json.dumps(self.config))
        config["inputs"][0]["exclude"] = ["cache"]
        (self.source / "project/cache").mkdir()
        (self.source / "project/cache/generated").write_text("cache")
        b.init_vault(config, other)
        b.checkpoint(other, 1)
        inv = b.verify_all(b.Git(other))["manifests"][1][1]["inventory"]
        self.assertIn({"input": "project", "path": "cache", "reason": "explicit exclusion"}, inv["omitted"])
        self.assertNotIn("project/cache/generated", inv["files"])
        config["inputs"][0]["exclude"] = ["lean-toolchain"]
        with self.assertRaises(b.BackupError):
            b.policy_check(config)

    def test_lfs_pointer_and_size_limit_fail_closed(self):
        path = self.source / "project/large.dat"
        path.write_bytes(b"version https://git-lfs.github.com/spec/v1\noid sha256:" + b"0" * 64 + b"\nsize 12\n")
        with self.assertRaisesRegex(b.BackupError, "LFS pointer"):
            self.snap()
        path.unlink()
        policy = b.control(self.vault)["policy"]
        policy["max_file_bytes"] = 1
        with self.assertRaisesRegex(b.BackupError, "limit"):
            b.scan(policy)

    def test_global_git_rewrite_filters_and_gitattributes_do_not_change_bytes(self):
        cfg = self.base / "global.gitconfig"
        cfg.write_text('[core]\n autocrlf = true\n[filter "do-not-run"]\n clean = false\n required = true\n')
        with patch.dict(os.environ, {"GIT_CONFIG_GLOBAL": str(cfg)}):
            self.snap()
            checked = self.verified()
            info = checked["manifests"][1][1]["inventory"]["files"]["project/Fixture.lean"]
            self.assertEqual(info["sha256"], b.digest((self.source / "project/Fixture.lean").read_bytes()))

    def test_local_url_redirect_configuration_is_rejected(self):
        self.snap()
        b.Git(self.vault).run("config", "url.https://example.invalid/.insteadOf", "https://github.com/")
        with self.assertRaisesRegex(b.BackupError, "configuration"):
            self.verified()

    def test_empty_vault_is_not_reported_as_a_checkpoint(self):
        self.assertEqual(b.summary(self.verified())["status"], "EMPTY_NO_CHECKPOINT")

    def test_deleted_all_refs_and_rollback_cannot_erase_confirmed_history(self):
        self.snap()
        self.snap(2)
        git = b.Git(self.vault)
        first = git.oid(b.tag(1))
        git.run("update-ref", "-d", b.tag(2))
        git.run("update-ref", b.TIP, first)
        with self.assertRaisesRegex(b.BackupError, "Previously verified"):
            self.verified()
        with self.assertRaises(b.BackupError):
            self.snap(3)
        git.run("update-ref", "-d", b.tag(1))
        git.run("update-ref", "-d", b.TIP)
        with self.assertRaisesRegex(b.BackupError, "Previously verified"):
            self.verified()

    def test_atomic_ref_conflict_does_not_advance_branch(self):
        self.snap()
        old = b.Git(self.vault).oid(b.TIP)
        real_run = b.Git.run
        def conflicting(git, *args, **kwargs):
            if args[:2] == ("update-ref", "--stdin"):
                real_run(git, "update-ref", b.tag(2), old)
            return real_run(git, *args, **kwargs)
        with patch.object(b.Git, "run", conflicting):
            with self.assertRaises(b.BackupError):
                self.snap(2)
        self.assertEqual(b.Git(self.vault).oid(b.TIP), old)

    def test_missing_evidence_role_is_rejected(self):
        bad = json.loads(json.dumps(self.config))
        bad["inputs"] = [item for item in bad["inputs"] if item["role"] != "correspondence"]
        with self.assertRaisesRegex(b.BackupError, "Missing input roles"):
            b.policy_check(bad)


class RemoteTests(BackupTests):
    # Avoid inheriting/repeating the local suite.
    __test__ = False
    def local_remote(self):
        remote = self.base / "remote.git"
        b.new_git(remote)
        return remote

    def remote_config(self):
        c = b.control(self.vault)
        c["remote"] = {"github_repository": "fixture/private", "repository_id": 123}
        b.atomic_json(self.vault / "backup-control.json", c)
        return c["remote"]

    def test_remote_roundtrip_and_recovery_use_fresh_objects(self):
        self.snap()
        self.snap(2)
        remote = self.local_remote()
        self.remote_config()
        # Local bare Git exercises real push/fetch/fsck/restore. GitHub privacy is simulated only.
        identity = {"github_repository": "fixture/private", "repository_id": 123, "private": True}
        with patch.object(b, "remote_url", return_value=str(remote)), patch.object(b, "github_identity", return_value=identity):
            result = b.sync(self.vault)
            self.assertEqual(result["status"], "REMOTE_VERIFIED")
            self.assertTrue(result["remote"]["fresh_restore_verified"])
            recovered = self.base / "recovered.git"
            output = b.recover("fixture/private", recovered, expected_commit=result["commit"])
            self.assertEqual(output["status"], "REMOTE_RECOVERY_VERIFIED")
            self.assertEqual(b.Git(recovered).refs(), b.Git(self.vault).refs())
            self.assertFalse((recovered / "objects/info/alternates").exists())
            with self.assertRaisesRegex(b.BackupError, "Trusted receipt"):
                b.recover("fixture/private", self.base / "wrong.git", expected_commit="0" * 40)

    def test_public_or_unavailable_privacy_never_attempts_git_transfer(self):
        self.snap()
        self.remote_config()
        with patch.object(b, "private_remote", side_effect=b.BackupError("Remote must be PRIVATE")), patch.object(b, "remote_refs") as refs:
            result = b.sync(self.vault)
        refs.assert_not_called()
        self.assertFalse(result["remote_verified"])
        self.assertEqual(result["status"], "LOCAL_VERIFIED_REMOTE_UNCONFIRMED")

    def test_github_visibility_and_repository_id_are_verified(self):
        samples = [
            {"private": False, "visibility": "public", "full_name": "fixture/private", "id": 123},
            {"private": True, "visibility": "internal", "full_name": "fixture/private", "id": 123},
            {"private": True, "visibility": "private", "full_name": "fixture/other", "id": 123},
            {"private": True, "visibility": "private", "full_name": "fixture/private", "id": 999},
        ]
        for sample in samples:
            response = subprocess.CompletedProcess([], 0, json.dumps(sample).encode(), b"")
            with patch.object(b.subprocess, "run", return_value=response):
                with self.assertRaises(b.BackupError):
                    b.github_identity("fixture/private", 123)
        with patch.object(b.subprocess, "run", side_effect=FileNotFoundError):
            with self.assertRaises(b.BackupError):
                b.github_identity("fixture/private")

    def test_push_failure_preserves_local_checkpoint_and_exit_three(self):
        self.remote_config()
        identity = {"private": True}
        with patch.object(b, "private_remote", return_value=identity), patch.object(b, "remote_url", return_value=str(self.base / "absent.git")):
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                code = b.main(["checkpoint", "--vault", str(self.vault), "--id", "1"])
        self.assertEqual(code, 3)
        self.assertEqual(json.loads(output.getvalue())["status"], "LOCAL_VERIFIED_REMOTE_UNCONFIRMED")
        self.assertEqual(len(self.verified()["records"]), 1)

    def test_real_git_receive_rejection_is_not_reported_as_saved(self):
        # A non-bare destination rejects updating its checked-out branch, even though
        # ls-remote works. This exercises a real nonzero git push, without the network.
        remote = self.base / "rejecting-worktree"
        subprocess.run(["git", "init", "--template=", "-b", "checkpoints", str(remote)],
                       check=True, capture_output=True)
        self.remote_config()
        with patch.object(b, "private_remote", return_value={"private": True}), patch.object(b, "remote_url", return_value=str(remote)):
            result = self.snap()
        self.assertEqual(result["status"], "LOCAL_VERIFIED_REMOTE_UNCONFIRMED")
        self.assertIn("Git push failed", result["error"])
        self.assertEqual(len(self.verified()["records"]), 1)
        self.assertEqual(b.Git(remote / ".git").refs(), {})

    def test_successful_push_exit_without_remote_data_does_not_count(self):
        self.snap()
        remote = self.local_remote()
        self.remote_config()
        original = b.Git.run
        def fake_push(git, *args, **kwargs):
            if args[0] == "push":
                return subprocess.CompletedProcess([], 0, b"Everything up-to-date\n", b"")
            return original(git, *args, **kwargs)
        with patch.object(b, "private_remote", return_value={"private": True}), patch.object(b, "remote_url", return_value=str(remote)), patch.object(b.Git, "run", fake_push):
            result = b.sync(self.vault)
        self.assertFalse(result["remote_verified"])
        self.assertIn("refs were not confirmed", result["error"])

    def test_remote_ref_mismatch_is_never_force_pushed(self):
        self.snap()
        self.snap(2)
        remote = self.local_remote()
        self.remote_config()
        with patch.object(b, "private_remote", return_value={"private": True}), patch.object(b, "remote_url", return_value=str(remote)):
            self.assertEqual(b.sync(self.vault)["status"], "REMOTE_VERIFIED")
            rg = b.Git(remote)
            rg.run("update-ref", b.tag(1), rg.oid(b.tag(2)))
            before = rg.refs()
            result = b.sync(self.vault)
        self.assertFalse(result["remote_verified"])
        self.assertEqual(before, rg.refs())

    def test_readback_failure_and_privacy_change_do_not_count_as_success(self):
        self.snap()
        remote = self.local_remote()
        self.remote_config()
        with patch.object(b, "private_remote", return_value={"private": True}), patch.object(b, "remote_url", return_value=str(remote)), patch.object(b, "fetch_fresh", side_effect=b.BackupError("readback failed")):
            first = b.sync(self.vault)
        self.assertFalse(first["remote_verified"])
        self.assertIn("readback failed", first["error"])
        with patch.object(b, "private_remote", side_effect=[{"private": True}, b.BackupError("now public")]), patch.object(b, "remote_url", return_value=str(remote)):
            second = b.sync(self.vault)
        self.assertFalse(second["remote_verified"])
        self.assertIn("now public", second["error"])


# unittest discovers inherited methods too; select each test once, explicitly.
def load_tests(loader, tests, pattern):
    local = loader.loadTestsFromTestCase(BackupTests)
    remote = unittest.TestSuite(RemoteTests(name) for name in RemoteTests.__dict__ if name.startswith("test_"))
    return unittest.TestSuite([local, remote])


if __name__ == "__main__":
    unittest.main(verbosity=2)
