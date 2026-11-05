import hashlib
import json
import os
import tempfile
from pathlib import Path


def restore():
    directory = Path(__file__).resolve().parent
    manifest = json.loads((directory / "PARTS.json").read_text(encoding="utf-8"))
    destination = Path.cwd() / manifest["archive"]
    if destination.exists():
        raise SystemExit(f"Output already exists at {destination}")
    digest = hashlib.sha256()
    size = 0
    temporary_path = None
    try:
        with tempfile.NamedTemporaryFile(dir=destination.parent, delete=False) as output:
            temporary_path = Path(output.name)
            for part in manifest["parts"]:
                data = (directory / part["path"]).read_bytes()
                if len(data) != part["size_bytes"] or hashlib.sha256(data).hexdigest() != part["sha256"]:
                    raise ValueError(f"Invalid archive part {part['path']}")
                output.write(data)
                digest.update(data)
                size += len(data)
        if size != manifest["size_bytes"] or digest.hexdigest() != manifest["sha256"]:
            raise ValueError("The reconstructed ZIP does not match the archive checksum")
        os.replace(temporary_path, destination)
    finally:
        if temporary_path is not None:
            temporary_path.unlink(missing_ok=True)
    print(f"Verified SHA-256 {digest.hexdigest()} for {destination}")


if __name__ == "__main__":
    restore()
