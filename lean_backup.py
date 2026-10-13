#!/usr/bin/env python3
"""Read-only source snapshots into a separate, verified bare Git repository.

Python 3.11+, Git 2.40+, POSIX. No third-party Python dependencies.
This preserves evidence; it does not certify that a Lean proof is correct.
"""
from __future__ import annotations

import argparse
import contextlib
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import uuid

SCHEMA = 1
TIP = "refs/heads/checkpoints"
TAG_PREFIX = "refs/tags/checkpoint-"
ROLES = {"project", "manuscript", "correspondence", "verification", "checklist"}
MAX_FILE = 95 * 1024 * 1024
ZERO = "0" * 40


class BackupError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise BackupError(message)


def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def relative(value):
    require(isinstance(value, str) and bool(value), "Empty or invalid relative path")
    require(not value.startswith("/") and "\\" not in value, f"Unsafe path: {value!r}")
    require(all(p not in ("", ".", "..", ".git") for p in value.split("/")),
            f"Unsafe path: {value!r}")
    require(not any(ord(c) < 32 or ord(c) == 127 for c in value), "Control character in path")
    try:
        value.encode("utf-8", errors="strict")
    except UnicodeError as exc:
        raise BackupError("Non-UTF-8 filename is unsupported") from exc
    return value


def absolute(value):
    # Deliberately do not resolve away symlinks before checking them.
    return Path(os.path.abspath(os.path.expanduser(str(value))))


def no_symlinks(path):
    path = absolute(path)
    for p in [*reversed(path.parents), path]:
        if p.is_symlink():
            raise BackupError(f"Symlink path is unsupported: {p}")
    return path


def overlaps(a, b):
    return a == b or a in b.parents or b in a.parents


def sync_dir(path):
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def atomic_json(path, obj):
    fd, name = tempfile.mkstemp(prefix=".write-", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as out:
            out.write(encoded(obj))
            out.flush()
            os.fsync(out.fileno())
        os.replace(name, path)
        sync_dir(path.parent)
    finally:
        if os.path.exists(name):
            os.unlink(name)


def policy_check(raw):
    require(isinstance(raw, dict) and raw.get("schema") == SCHEMA, "Unsupported configuration schema")
    require(set(raw) <= {"schema", "inputs", "max_file_bytes"}, "Unknown configuration key")
    inputs = raw.get("inputs")
    require(isinstance(inputs, list) and bool(inputs), "inputs must be a nonempty list")
    seen, roles = set(), set()
    policy = {"schema": SCHEMA, "max_file_bytes": raw.get("max_file_bytes", MAX_FILE), "inputs": []}
    require(type(policy["max_file_bytes"]) is int and 0 < policy["max_file_bytes"] <= MAX_FILE,
            "max_file_bytes must be positive and at most 95 MiB")
    for item in inputs:
        require(isinstance(item, dict) and set(item) <=
                {"name", "path", "role", "exclude", "required", "expected_sha256"}, "Invalid input keys")
        name = item.get("name")
        require(isinstance(name, str) and re.fullmatch(r"[A-Za-z][A-Za-z0-9_.-]*", name), "Invalid input name")
        require(name not in seen, f"Duplicate input name: {name}")
        seen.add(name)
        role = item.get("role")
        require(role in ROLES, f"Invalid role for {name}")
        roles.add(role)
        require(isinstance(item.get("path"), str) and bool(item["path"]), "Missing input path")
        exclusions, required = item.get("exclude", []), item.get("required", [])
        require(isinstance(exclusions, list) and isinstance(required, list), "exclude/required must be lists")
        for p in exclusions + required:
            relative(p)
        require(not (role == "manuscript" and exclusions), "Cannot exclude parts of a manuscript input")
        for p in required:
            require(not any(p == e or p.startswith(e + "/") for e in exclusions), f"Required path excluded: {p}")
        expected = item.get("expected_sha256")
        require(expected is None or (isinstance(expected, str) and re.fullmatch(r"[0-9a-f]{64}", expected)),
                "expected_sha256 must be a lowercase SHA-256 digest")
        policy["inputs"].append({"name": name, "path": str(absolute(item["path"])), "role": role,
                                  "exclude": sorted(set(exclusions)), "required": sorted(set(required)),
                                  "expected_sha256": expected})
    require(roles == ROLES, f"Missing input roles: {sorted(ROLES - roles)}")
    return policy


def detached(path, policy):
    path = no_symlinks(path)
    for item in policy["inputs"]:
        source = no_symlinks(item["path"])
        require(not overlaps(path, source), f"Destination overlaps source: {path}")
    return path


def environment():
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
               GIT_TERMINAL_PROMPT="0", GIT_OPTIONAL_LOCKS="0", GIT_NO_REPLACE_OBJECTS="1",
               GIT_AUTHOR_NAME="Lean Checkpoint Backup", GIT_AUTHOR_EMAIL="backup@localhost",
               GIT_COMMITTER_NAME="Lean Checkpoint Backup", GIT_COMMITTER_EMAIL="backup@localhost")
    return env


class Git:
    def __init__(self, path):
        self.path = absolute(path)
        self.commands = []

    def run(self, *args, data=None, check=True, timeout=120, extra_env=None):
        cmd = ["git", "-c", "core.hooksPath=" + os.devnull, "-c", "core.attributesFile=" + os.devnull,
               "-c", "core.autocrlf=false", "-c", "core.fsync=committed", "-c", "gc.auto=0",
               "-c", "maintenance.auto=false", "-c", "protocol.allow=never",
               "-c", "protocol.https.allow=always", "-c", "protocol.file.allow=always",
               "-c", "credential.helper=", "-c", "credential.helper=!gh auth git-credential",
               "--git-dir=" + str(self.path), *map(str, args)]
        env = environment()
        if extra_env:
            env.update(extra_env)
        start = now()
        try:
            result = subprocess.run(cmd, input=data, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                    env=env, timeout=timeout)
        except subprocess.TimeoutExpired as exc:
            self.commands.append({"argv": cmd, "started_at": start, "timeout": timeout})
            raise BackupError(f"Git {args[0]} timed out; no success is certified") from exc
        self.commands.append({"argv": cmd, "started_at": start, "exit_code": result.returncode})
        if check and result.returncode:
            raise BackupError(f"Git {args[0]} failed (exit {result.returncode}): " +
                              result.stderr.decode(errors="replace")[:1200])
        return result

    def text(self, *args, **kwargs):
        return self.run(*args, **kwargs).stdout.decode().strip()

    def oid(self, ref):
        r = self.run("rev-parse", "--verify", ref, check=False)
        return r.stdout.decode().strip() if r.returncode == 0 else None

    def blob(self, data):
        return self.text("hash-object", "-w", "--no-filters", "--stdin", data=data)

    def refs(self):
        result = {}
        for line in self.text("for-each-ref", "--format=%(refname) %(objectname)").splitlines():
            name, oid = line.split(" ")
            result[name] = oid
        return result


def new_git(path):
    require(not path.exists(), f"Destination already exists: {path}")
    path.mkdir(mode=0o700, parents=False)
    git = Git(path)
    git.run("init", "--bare", "--object-format=sha1", "--template=", str(path))
    git.run("symbolic-ref", "HEAD", TIP)
    return git


@contextlib.contextmanager
def lock(vault):
    with (vault / "backup.lock").open("a+b") as handle:
        try:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise BackupError("Another operation holds the vault lock; nothing was overwritten") from exc
        yield


def control(vault):
    vault = no_symlinks(vault)
    require(vault.is_dir(), "Vault does not exist")
    require((vault / "backup-control.json").is_file(), "Not a managed backup vault")
    c = json.loads((vault / "backup-control.json").read_bytes())
    require(c.get("schema") == SCHEMA, "Unsupported vault schema")
    require(c["policy"] == policy_check(c["policy"]), "Invalid stored policy")
    detached(vault, c["policy"])
    return c


def init_vault(config, vault):
    policy = policy_check(config)
    vault = detached(absolute(vault), policy)
    require(vault.parent.is_dir(), "Create the vault's parent directory first")
    # Check sources before creating any managed repository.
    for item in policy["inputs"]:
        require(no_symlinks(item["path"]).exists(), f"Source is missing: {item['name']}")
    new_git(vault)
    atomic_json(vault / "backup-control.json", {"schema": SCHEMA, "policy": policy, "remote": None,
                                                "last_verified_commit": None})
    return {"status": "INITIALIZED_NO_CHECKPOINT", "vault": str(vault), "remote": None}


def fingerprint(st):
    return [st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns, stat.S_IMODE(st.st_mode)]


def scan(policy, stage=None):
    """Read files with O_NOFOLLOW and directory descriptors; never write inputs."""
    files, directories, stamps, omitted = {}, {}, {}, []

    def put(rootfd, name, key, path_for_message):
        relative(key)
        before = os.stat(name, dir_fd=rootfd, follow_symlinks=False)
        require(stat.S_ISREG(before.st_mode), f"Not a regular file: {path_for_message}")
        require(before.st_size <= policy["max_file_bytes"], f"File exceeds configured Git limit: {key}")
        require(not stat.S_IMODE(before.st_mode) & 0o7000, f"Special permission bits unsupported: {key}")
        fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=rootfd)
        out = None
        try:
            require(fingerprint(os.fstat(fd)) == fingerprint(before), f"Source changed while opening: {key}")
            if stage:
                target = stage / key
                target.parent.mkdir(parents=True, exist_ok=True)
                out = target.open("xb")
            h, size, prefix = hashlib.sha256(), 0, b""
            with os.fdopen(fd, "rb", closefd=False) as src:
                while chunk := src.read(1024 * 1024):
                    size += len(chunk)
                    require(size <= policy["max_file_bytes"], f"Growing or oversized file: {key}")
                    if not prefix:
                        prefix = chunk[:128]
                    h.update(chunk)
                    if out:
                        out.write(chunk)
            require(fingerprint(os.fstat(fd)) == fingerprint(before) and size == before.st_size,
                    f"Source changed while reading: {key}")
            require(not prefix.startswith(b"version https://git-lfs.github.com/spec/v1\n"),
                    f"LFS pointer is not a complete file: {key}; materialize it before backup")
            files[key] = {"sha256": h.hexdigest(), "bytes": size, "mode": stat.S_IMODE(before.st_mode)}
            stamps[key] = fingerprint(before)
        finally:
            os.close(fd)
            if out:
                out.close()

    for item in policy["inputs"]:
        source = no_symlinks(item["path"])
        require(source.exists(), f"Missing input: {item['name']}")
        mount, excluded = item["name"], item["exclude"]
        before_count = len(files)
        if source.is_file():
            require(not item["required"] and not excluded, f"File input has directory-only settings: {mount}")
            pfd = os.open(source.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
            try:
                put(pfd, source.name, mount, source)
            finally:
                os.close(pfd)
            if item["expected_sha256"]:
                require(files[mount]["sha256"] == item["expected_sha256"], f"Authoritative hash mismatch: {mount}")
        else:
            require(source.is_dir() and not item["expected_sha256"], f"Invalid directory input: {mount}")
            for root, dirs, names, fd in os.fwalk(source, follow_symlinks=False):
                rel = Path(root).relative_to(source).as_posix()
                key = mount if rel == "." else mount + "/" + rel
                relative(key)
                ds = os.fstat(fd)
                directories[key] = stat.S_IMODE(ds.st_mode) & 0o777
                stamps[key + "/"] = fingerprint(ds)
                for name in sorted(dirs + names):
                    p = name if rel == "." else rel + "/" + name
                    reason = "git metadata" if name == ".git" else (
                        "explicit exclusion" if any(p == e or p.startswith(e + "/") for e in excluded) else None)
                    if reason:
                        omitted.append({"input": mount, "path": p, "reason": reason})
                        if name in dirs:
                            dirs.remove(name)
                        continue
                    relative(p)
                    st = os.stat(name, dir_fd=fd, follow_symlinks=False)
                    require(not stat.S_ISLNK(st.st_mode), f"Symlink input is unsupported: {key}/{name}")
                    if name not in dirs:
                        put(fd, name, key + "/" + name, str(Path(root) / name))
                dirs.sort()
            for p in item["required"]:
                require(mount + "/" + p in files, f"Required file missing or excluded: {mount}/{p}")
            if item["role"] == "project":
                require(mount + "/lean-toolchain" in files and mount + "/lake-manifest.json" in files,
                        "Project must include lean-toolchain and lake-manifest.json")
                require(any(k.startswith(mount + "/") and k.endswith(".lean") for k in files),
                        "Project contains no Lean source")
                require(any(mount + "/" + n in files for n in ("lakefile.lean", "lakefile.toml")),
                        "Project must include lakefile.lean or lakefile.toml")
        require(len(files) > before_count, f"Empty evidence input: {mount}")
        if item["role"] == "project":
            require(source.is_dir(), "Project input must be a directory")
    return {"files": dict(sorted(files.items())), "directories": dict(sorted(directories.items())),
            "omitted": sorted(omitted, key=lambda x: (x["input"], x["path"]))}, stamps


def manuscript_files(policy, inventory):
    mounts = [i["name"] for i in policy["inputs"] if i["role"] == "manuscript"]
    return {p: v for p, v in inventory["files"].items() if any(p == m or p.startswith(m + "/") for m in mounts)}


def make_tree(git, flat):
    tree = {}
    for path, (mode, oid) in flat.items():
        parts = relative(path).split("/")
        node = tree
        for part in parts[:-1]:
            node = node.setdefault(part, {})
            require(isinstance(node, dict), "Tree path conflict")
        require(parts[-1] not in node, "Duplicate tree path")
        node[parts[-1]] = (mode, oid)

    def write(node):
        records = []
        for name, value in node.items():
            if isinstance(value, dict):
                mode, kind, oid = "040000", "tree", write(value)
            else:
                mode, oid = value
                kind = "blob"
            records.append(f"{mode} {kind} {oid}\t{name}".encode() + b"\0")
        return git.text("mktree", "-z", data=b"".join(records))
    return write(tree)


def tree_files(git, commit):
    result = {}
    for row in git.run("ls-tree", "-rz", "--full-tree", commit).stdout.split(b"\0"):
        if row:
            meta, name = row.split(b"\t", 1)
            mode, kind, oid = meta.decode().split()
            path = relative(name.decode())
            require(kind == "blob" and mode in ("100644", "100755"), "Unsupported Git entry")
            result[path] = (mode, oid)
    return result


def read_blob(git, oid):
    require(re.fullmatch(r"[0-9a-f]{40}", oid), "Invalid object ID")
    return git.run("cat-file", "blob", oid).stdout


def tag(number):
    require(type(number) is int and 1 <= number <= 999999999, "Checkpoint ID must be 1..999999999")
    return TAG_PREFIX + f"{number:09d}"


def check_repo(git):
    no_symlinks(git.path / "config")
    allowed_config = {"core.repositoryformatversion", "core.filemode", "core.bare"}
    local_config = git.run("config", "--local", "--no-includes", "--null", "--list").stdout
    for entry in local_config.split(b"\0"):
        if entry:
            key = entry.split(b"\n", 1)[0].decode().lower()
            require(key in allowed_config, f"Unrecognized Git configuration in managed vault: {key}")
    require(git.text("rev-parse", "--is-bare-repository") == "true", "Vault must be bare")
    for name in ("shallow", "objects/info/alternates", "info/grafts"):
        require(not (git.path / name).exists(), f"Non-self-contained repository: {name}")
    git.run("fsck", "--full", "--strict", "--no-reflogs", timeout=600)


def verify_all(git, expected_policy=None):
    check_repo(git)
    refs = git.refs()
    head = refs.get(TIP)
    if head is None:
        require(not refs, "Checkpoint branch missing while other refs remain")
        return {"records": [], "manifests": {}, "refs": {}, "tip": None}
    history = git.text("rev-list", "--first-parent", "--reverse", head).splitlines()
    records, manifests, wanted_refs, hash_cache = [], {}, {}, {}
    previous, baseline, policy = None, None, expected_policy
    for oid in history:
        parents = git.text("rev-list", "--parents", "-n", "1", oid).split()[1:]
        require(parents == ([] if previous is None else [previous]), "Unexpected commit ancestry")
        entries = tree_files(git, oid)
        require({"manifest.json", "catalog.json"} <= set(entries), "Missing committed manifest/catalog")
        require(entries["manifest.json"][0] == entries["catalog.json"][0] == "100644", "Metadata mode mismatch")
        raw = read_blob(git, entries["manifest.json"][1])
        m = json.loads(raw)
        require(raw == encoded(m), "Noncanonical manifest serialization")
        require(m.get("schema") == SCHEMA, "Unknown manifest schema")
        require(m["policy"] == policy_check(m["policy"]), "Invalid manifest policy")
        if policy is None:
            policy = m["policy"]
        require(m["policy"] == policy, "Backup scope/policy changed inside history")
        num = m["checkpoint"]
        ref = tag(num)
        require(not records or num > records[-1]["checkpoint"], "Repeated or decreasing checkpoint ID")
        require(m["parent_commit"] == previous, "Manifest parent mismatch")
        inv = m["inventory"]
        require(isinstance(inv["files"], dict) and bool(inv["files"]), "Missing payload inventory")
        allowed = {"manifest.json", "catalog.json"} | {"payload/" + relative(p) for p in inv["files"]}
        require(set(entries) == allowed, "Git tree contains missing or unlisted files")
        for p, info in inv["files"].items():
            require(type(info["mode"]) is int and 0 <= info["mode"] <= 0o777, "Invalid file mode")
            mode, blob = entries["payload/" + p]
            require(mode == ("100755" if info["mode"] & 0o111 else "100644"), f"Mode mismatch: {p}")
            if blob not in hash_cache:
                content = read_blob(git, blob)
                hash_cache[blob] = (digest(content), len(content))
            require(hash_cache[blob] == (info["sha256"], info["bytes"]), f"SHA-256 or size mismatch: {p}")
        for p, mode in inv["directories"].items():
            relative(p)
            require(p not in inv["files"] and type(mode) is int and 0 <= mode <= 0o777, "Invalid directory entry")
        all_paths = set(inv["files"]) | set(inv["directories"])
        for p in all_paths:
            parent = PurePosixPath(p).parent.as_posix()
            require(parent == "." or parent in inv["directories"], f"Missing directory entry: {p}")
        for item in policy["inputs"]:
            mount = item["name"]
            require(any(p == mount or p.startswith(mount + "/") for p in inv["files"]), "Missing required input")
            for req in item["required"]:
                require(mount + "/" + req in inv["files"], "Missing required file in manifest")
        manuscripts = manuscript_files(policy, inv)
        if baseline is None:
            baseline = manuscripts
        require(manuscripts == baseline, "Manuscript differs from the first checkpoint")
        record = {"checkpoint": num, "parent_commit": previous, "manifest_sha256": digest(raw),
                  "created_at": m["created_at"]}
        records.append(record)
        require(json.loads(read_blob(git, entries["catalog.json"][1])) == {"schema": SCHEMA, "records": records},
                "Catalog is not the exact append-only checkpoint history")
        require(refs.get(ref) == oid, f"Checkpoint ref missing or changed: {ref}")
        wanted_refs[ref] = oid
        manifests[num] = (oid, m, entries)
        previous = oid
    wanted_refs[TIP] = head
    require(refs == wanted_refs, "Unexpected, missing or rewritten refs in the managed vault")
    return {"records": records, "manifests": manifests, "refs": refs, "tip": head}


def verify_vault(git, c):
    verified = verify_all(git, c["policy"])
    anchor = c.get("last_verified_commit")
    if anchor:
        require(anchor in {v[0] for v in verified["manifests"].values()},
                "Previously verified checkpoint is missing: repository rollback or lost refs")
    return verified


def receipt(git, result):
    directory = git.path / "receipts"
    directory.mkdir(mode=0o700, exist_ok=True)
    payload = {**result, "recorded_at": now(), "commands": git.commands}
    path = directory / (dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S") + "-" + uuid.uuid4().hex + ".json")
    atomic_json(path, payload)
    return {**result, "receipt": str(path)}


def checkpoint(vault, number, allow_gap=False):
    vault = absolute(vault)
    c = control(vault)
    tag(number)
    with lock(vault):
        c = control(vault)
        git, policy = Git(vault), c["policy"]
        verified = verify_vault(git, c)
        records = verified["records"]
        if records:
            previous_id = records[-1]["checkpoint"]
            require(number > previous_id, "Checkpoint IDs are immutable and must increase")
            require(number == previous_id + 1 or allow_gap, "Numbering gap; explicitly pass --allow-gap to record it")
        with tempfile.TemporaryDirectory(prefix=".snapshot-", dir=vault.parent) as td:
            stage = Path(td)
            inventory, stamps = scan(policy, stage)
            if records:
                baseline = verified["manifests"][records[0]["checkpoint"]][1]["inventory"]
                require(manuscript_files(policy, baseline) == manuscript_files(policy, inventory),
                        "Authoritative manuscript changed; checkpoint rejected")
            flat = {}
            for p, info in inventory["files"].items():
                oid = git.text("hash-object", "-w", "--no-filters", "--", stage / p)
                flat["payload/" + p] = ("100755" if info["mode"] & 0o111 else "100644", oid)
            manifest = {"schema": SCHEMA, "checkpoint": number, "created_at": now(),
                        "parent_commit": verified["tip"], "policy": policy, "inventory": inventory,
                        "proof_status": "Evidence preserved; no proof validation performed by this tool"}
            raw = encoded(manifest)
            record = {"checkpoint": number, "parent_commit": verified["tip"],
                      "manifest_sha256": digest(raw), "created_at": manifest["created_at"]}
            flat["manifest.json"] = ("100644", git.blob(raw))
            flat["catalog.json"] = ("100644", git.blob(encoded({"schema": SCHEMA, "records": records + [record]})))
            tree = make_tree(git, flat)
            parent_args = ["-p", verified["tip"]] if verified["tip"] else []
            commit = git.text("commit-tree", tree, *parent_args, data=f"Checkpoint {number}\n".encode())
            again, later_stamps = scan(policy)
            require((inventory, stamps) == (again, later_stamps), "Source changed during snapshot; nothing published")
            commands = (f"start\nupdate {TIP} {commit} {verified['tip'] or ZERO}\n"
                        f"create {tag(number)} {commit}\nprepare\ncommit\n")
            git.run("update-ref", "--stdin", data=commands.encode())
            checked = verify_all(git, policy)
            require(checked["tip"] == commit, "Post-commit verification mismatch")
            c["last_verified_commit"] = commit
            atomic_json(vault / "backup-control.json", c)
            result = {"status": "LOCAL_VERIFIED", "checkpoint": number, "commit": commit,
                      "manifest_sha256": digest(raw), "files": len(inventory["files"]),
                      "remote_verified": False}
            if c["remote"]:
                try:
                    remote_evidence = sync_core(git, c["remote"], checked)
                    result.update(status="REMOTE_VERIFIED", remote_verified=True, remote=remote_evidence)
                except (BackupError, OSError, ValueError) as exc:
                    result.update(status="LOCAL_VERIFIED_REMOTE_UNCONFIRMED", error=str(exc))
            return receipt(git, result)


def restore_from(git, verified, number, destination):
    require(number in verified["manifests"], "Checkpoint is not present in this repository")
    oid, m, entries = verified["manifests"][number]
    target = detached(absolute(destination), m["policy"])
    require(not overlaps(target, git.path), "Restore destination overlaps the vault")
    require(not target.exists() and target.parent.is_dir(), "Restore requires a new destination in an existing parent")
    inv = m["inventory"]
    with tempfile.TemporaryDirectory(prefix=".restore-", dir=target.parent) as td:
        stage = Path(td) / "payload"
        stage.mkdir(mode=0o700)
        for p in sorted(inv["directories"], key=lambda p: (p.count("/"), p)):
            (stage / relative(p)).mkdir(mode=0o700)
        for p, info in inv["files"].items():
            path = stage / relative(p)
            raw = read_blob(git, entries["payload/" + p][1])
            require(digest(raw) == info["sha256"] and len(raw) == info["bytes"], f"Restore hash failed: {p}")
            with path.open("xb") as out:
                out.write(raw)
                out.flush()
                os.fsync(out.fileno())
            require(digest(path.read_bytes()) == info["sha256"], f"Restored disk bytes differ: {p}")
            os.chmod(path, info["mode"])
        for p in sorted(inv["directories"], key=lambda p: (-p.count("/"), p)):
            sync_dir(stage / p)
            os.chmod(stage / p, inv["directories"][p])
        sync_dir(stage)
        # Reserve the destination atomically. Never rename over an existing path.
        target.mkdir(mode=0o700)
        try:
            os.rename(stage, target / "payload")
            atomic_json(target / "manifest.json", m)
            result = {"status": "RESTORE_VERIFIED", "checkpoint": number, "commit": oid,
                      "manifest_sha256": digest(encoded(m)), "files": len(inv["files"]),
                      "destination": str(target)}
            atomic_json(target / "RESTORE_RECEIPT.json", result)
            sync_dir(target)
            sync_dir(target.parent)
        except BaseException:
            # A partially installed result is not certified; retain it for inspection.
            raise
    return result


def github_identity(repository, expected_id=None):
    require(isinstance(repository, str) and re.fullmatch(r"[A-Za-z0-9_-]+/[A-Za-z0-9_.-]+", repository),
            "Use a GitHub OWNER/REPOSITORY name, not a URL or remote alias")
    try:
        r = subprocess.run(["gh", "api", "--hostname", "github.com", f"repos/{repository}"],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60, env=environment())
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise BackupError("Cannot check GitHub privacy; no transfer is permitted") from exc
    require(r.returncode == 0, "GitHub repository lookup failed; no transfer is permitted")
    obj = json.loads(r.stdout)
    require(obj.get("private") is True and obj.get("visibility") == "private", "Remote must be PRIVATE")
    require(str(obj.get("full_name", "")).lower() == repository.lower(), "GitHub identity mismatch")
    require(type(obj.get("id")) is int, "GitHub repository ID missing")
    require(expected_id is None or obj["id"] == expected_id, "GitHub repository was replaced or redirected")
    return {"github_repository": obj["full_name"], "repository_id": obj["id"],
            "privacy_checked_at": now(), "private": True}


def remote_url(remote):
    # A remote URL is derived only from a verified canonical GitHub identity.
    name = remote["github_repository"]
    require(re.fullmatch(r"[A-Za-z0-9_-]+/[A-Za-z0-9_.-]+", name), "Invalid remote identity")
    return f"https://github.com/{name}.git"


def private_remote(remote):
    return github_identity(remote["github_repository"], remote["repository_id"])


def remote_refs(git, url):
    result = {}
    for line in git.text("ls-remote", "--refs", url).splitlines():
        oid, ref = line.split("\t")
        require(re.fullmatch(r"[0-9a-f]{40}", oid), "Invalid remote object ID")
        result[ref] = oid
    return result


def fetch_fresh(git, url, expected, where):
    fresh = new_git(where)
    fresh.run("fetch", "--atomic", "--no-tags", url, f"{TIP}:{TIP}",
              f"{TAG_PREFIX}*:{TAG_PREFIX}*", timeout=600)
    checked = verify_all(fresh)
    require(checked["refs"] == expected, "Freshly fetched refs do not match the expected remote snapshot")
    return fresh, checked


def sync_core(git, remote, verified):
    require(bool(verified["records"]), "Nothing to sync")
    before_privacy = private_remote(remote)
    url, expected = remote_url(remote), verified["refs"]
    before = remote_refs(git, url)
    require(set(before) <= set(expected), "Remote has unrelated refs; use a dedicated empty backup repository")
    for ref, oid in before.items():
        if ref == TIP:
            require(oid in {v[0] for v in verified["manifests"].values()}, "Remote has diverged; refusing overwrite")
        else:
            require(expected[ref] == oid, "Remote checkpoint tag differs; refusing overwrite")
    # Plain, atomic push: no force, no mirror, no deletion and no lease override.
    git.run("push", "--atomic", "--porcelain", url, *[f"{r}:{r}" for r in sorted(expected)], timeout=600)
    require(remote_refs(git, url) == expected, "Push returned but remote refs were not confirmed")
    with tempfile.TemporaryDirectory(prefix=".remote-readback-", dir=git.path.parent) as td:
        fresh, received = fetch_fresh(git, url, expected, Path(td) / "received.git")
        latest = verified["records"][-1]["checkpoint"]
        restore_result = restore_from(fresh, received, latest, Path(td) / "restored")
        # Includes the actual restore read commands, not only fetch verification.
        git.commands.extend(fresh.commands)
        require(restore_result["commit"] == verified["tip"], "Remote restore returned the wrong commit")
    require(remote_refs(git, url) == expected, "Remote changed during readback verification")
    after_privacy = private_remote(remote)
    return {"github_repository": remote["github_repository"], "repository_id": remote["repository_id"],
            "before_privacy": before_privacy, "after_privacy": after_privacy,
            "verified_at": now(), "commit": verified["tip"], "fresh_restore_verified": True}


def remote_set(vault, repository):
    c = control(vault)
    with lock(vault):
        c = control(vault)
        require(c["remote"] is None, "Remote already set; it cannot be silently repointed")
        identity = github_identity(repository)
        git = Git(vault)
        check_repo(git)
        require(not remote_refs(git, remote_url(identity)), "Initial remote must be empty and dedicated to this vault")
        c["remote"] = identity
        atomic_json(vault / "backup-control.json", c)
        return {"status": "REMOTE_CONFIGURED_NOT_UPLOADED", "remote_verified": False, "remote": identity}


def sync(vault):
    c = control(vault)
    require(c["remote"] is not None, "No private GitHub repository configured")
    with lock(vault):
        c = control(vault)
        require(c["remote"] is not None, "No private GitHub repository configured")
        git = Git(vault)
        checked = verify_vault(git, c)
        result = {"status": "LOCAL_VERIFIED_REMOTE_UNCONFIRMED", "commit": checked["tip"], "remote_verified": False}
        try:
            evidence = sync_core(git, c["remote"], checked)
            result.update(status="REMOTE_VERIFIED", remote_verified=True, remote=evidence)
        except (BackupError, OSError, ValueError) as exc:
            result["error"] = str(exc)
        return receipt(git, result)


def recover(repository, vault, expected_commit=None):
    vault = no_symlinks(vault)
    require(not vault.exists() and vault.parent.is_dir(), "Recovery requires a new vault path")
    identity = github_identity(repository)
    url = remote_url(identity)
    with tempfile.TemporaryDirectory(prefix=".recover-", dir=vault.parent) as td:
        scratch = new_git(Path(td) / "query.git")
        refs = remote_refs(scratch, url)
        require(TIP in refs, "Remote has no backup branch")
        require(expected_commit is None or refs[TIP] == expected_commit, "Trusted receipt commit mismatch")
        fresh, checked = fetch_fresh(scratch, url, refs, Path(td) / "vault.git")
        last = checked["records"][-1]["checkpoint"]
        policy = checked["manifests"][last][1]["policy"]
        detached(vault, policy)
        restore_from(fresh, checked, last, Path(td) / "trial-restore")
        require(remote_refs(scratch, url) == refs, "Remote changed during recovery")
        private_remote(identity)
        atomic_json(fresh.path / "backup-control.json", {"schema": SCHEMA, "policy": policy, "remote": identity,
                                                        "last_verified_commit": refs[TIP]})
        # Reserve a new destination; no original source or existing vault can be replaced.
        vault.mkdir(mode=0o700)
        for child in fresh.path.iterdir():
            os.rename(child, vault / child.name)
        sync_dir(vault)
        sync_dir(vault.parent)
    return {"status": "REMOTE_RECOVERY_VERIFIED", "commit": refs[TIP], "vault": str(vault),
            "checkpoint": last, "remote_verified": True}


def summary(verified):
    records = verified["records"]
    gaps = [[a["checkpoint"] + 1, b["checkpoint"] - 1] for a, b in zip(records, records[1:])
            if b["checkpoint"] > a["checkpoint"] + 1]
    return {"status": "LOCAL_VERIFIED" if records else "EMPTY_NO_CHECKPOINT", "remote_verified": False,
            "checkpoints": [{"id": r["checkpoint"], "commit": verified["manifests"][r["checkpoint"]][0],
                             "manifest_sha256": r["manifest_sha256"]} for r in records],
            "missing_before_first": [1, records[0]["checkpoint"] - 1] if records and records[0]["checkpoint"] > 1 else None,
            "sequence_gaps": gaps, "tip": verified["tip"]}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("init"); p.add_argument("--config", type=Path, required=True); p.add_argument("--vault", type=Path, required=True)
    p = sub.add_parser("checkpoint"); p.add_argument("--vault", type=Path, required=True); p.add_argument("--id", type=int, required=True); p.add_argument("--allow-gap", action="store_true")
    for name in ("verify", "list", "sync"):
        sub.add_parser(name).add_argument("--vault", type=Path, required=True)
    p = sub.add_parser("restore"); p.add_argument("--vault", type=Path, required=True); p.add_argument("--id", type=int, required=True); p.add_argument("--destination", type=Path, required=True)
    p = sub.add_parser("remote-set"); p.add_argument("--vault", type=Path, required=True); p.add_argument("--github", required=True)
    p = sub.add_parser("recover"); p.add_argument("--vault", type=Path, required=True); p.add_argument("--github", required=True); p.add_argument("--expect-commit")
    args = parser.parse_args(argv)
    try:
        if args.command == "init":
            result = init_vault(json.loads(args.config.read_bytes()), args.vault)
        elif args.command == "checkpoint":
            result = checkpoint(args.vault, args.id, args.allow_gap)
        elif args.command == "remote-set":
            result = remote_set(absolute(args.vault), args.github)
        elif args.command == "sync":
            result = sync(absolute(args.vault))
        elif args.command == "recover":
            result = recover(args.github, absolute(args.vault), args.expect_commit)
        else:
            vault = absolute(args.vault)
            c = control(vault)
            with lock(vault):
                c = control(vault)
                git = Git(vault)
                checked = verify_vault(git, c)
                result = (restore_from(git, checked, args.id, args.destination) if args.command == "restore"
                          else summary(checked))
                result = receipt(git, result)
        print(json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2))
        return 3 if result["status"] == "LOCAL_VERIFIED_REMOTE_UNCONFIRMED" else 0
    except (BackupError, OSError, ValueError, KeyError, TypeError, UnicodeError) as exc:
        print(json.dumps({"status": "FAILED", "remote_verified": False, "error": str(exc)}, ensure_ascii=False), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
