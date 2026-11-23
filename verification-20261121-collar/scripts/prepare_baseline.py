#!/usr/bin/env python3
"""Restore the published, hash-pinned inherited objects from the original ZIP."""
import argparse
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import shutil
import tempfile
import zipfile


ARCHIVE_SHA256 = "38986e227e918049298bb32b6090f6fccfcd3e9de1f47f10a3d48cc876fefe5c"
MANIFEST_SHA256 = "aa4f7a569cfb1e2e632b28734177a6cc8b14ede5e2120792b2fa0d4eeb567425"
SOURCES_SHA256 = "0a7f6fd8296dd19fd7be8e2cc2faef7996ba684323251988c7711dfae885518c"
PACKAGE = Path(__file__).resolve().parents[1]


def digest(path):
    with Path(path).open("rb") as stream:
        h = sha256()
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
        return h.hexdigest()


def restore(package, archive):
    package, archive = Path(package).resolve(), Path(archive).resolve()
    if digest(archive) != ARCHIVE_SHA256:
        raise ValueError("Replay archive SHA-256 mismatch; nothing extracted")
    manifest = package / "baseline/SHA256SUMS.json"
    if digest(manifest) != MANIFEST_SHA256:
        raise ValueError("Inherited manifest differs from the published checkpoint")
    source_manifest = package / "sources.sha256.json"
    if digest(source_manifest) != SOURCES_SHA256:
        raise ValueError("Source manifest differs from the published checkpoint")
    for name, expected in json.loads(source_manifest.read_text()).items():
        if digest(package / name) != expected:
            raise ValueError(f"Published source differs: {name}")
    objects = json.loads(manifest.read_text())
    if len(objects) != 1879:
        raise ValueError("Expected exactly 1,879 inherited objects")
    for name in objects:
        rel = PurePosixPath(name)
        if rel.is_absolute() or ".." in rel.parts or rel.parts[0] != "PaperILean" or rel.suffix != ".olean":
            raise ValueError(f"Invalid inherited path: {name}")
    destination = package / "baseline/PaperILean"
    if destination.exists():
        if destination.is_symlink():
            raise ValueError("Inherited destination must not be a symlink")
        for name, expected in objects.items():
            obj = package / "baseline" / name
            if obj.is_symlink() or digest(obj) != expected:
                raise ValueError(f"Existing inherited object differs: {name}")
        mode = "verified-existing"
    else:
        # Only named inherited objects are installed; sources and old evidence stay intact.
        with tempfile.TemporaryDirectory(prefix="restore-", dir=package / "baseline") as temp:
            staging = Path(temp)
            with zipfile.ZipFile(archive) as source:
                if len(source.namelist()) != len(set(source.namelist())):
                    raise ValueError("Duplicate archive entries")
                for name, expected in objects.items():
                    member = "baseline/" + name
                    info = source.getinfo(member)
                    if info.file_size > 128 * 1024 * 1024:
                        raise ValueError(f"Unexpected inherited object size: {name}")
                    target = staging / name
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with source.open(member) as src, target.open("wb") as dst:
                        shutil.copyfileobj(src, dst)
                    if digest(target) != expected:
                        raise ValueError(f"Inherited object SHA-256 mismatch: {name}")
            (staging / "PaperILean").rename(destination)
        mode = "restored-from-original-archive"
    return {"archive_sha256": ARCHIVE_SHA256, "baseline_manifest_sha256": MANIFEST_SHA256,
            "source_manifest_sha256": SOURCES_SHA256, "object_count": len(objects), "mode": mode,
            "scope": "Retained inherited objects, not a source rebuild of inherited theorems"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", required=True, type=Path)
    parser.add_argument("--package", type=Path, default=PACKAGE)
    parser.add_argument("--receipt", required=True, type=Path)
    args = parser.parse_args()
    receipt = restore(args.package, args.archive)
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    args.receipt.write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"PASS: {receipt['object_count']} inherited hashes; {receipt['mode']}")


if __name__ == "__main__":
    main()
