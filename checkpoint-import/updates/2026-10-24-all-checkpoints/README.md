# All available Lean checkpoints: GitHub backup

**All 1,087 inventoried original files are backed up in the private repository.**
The inventory totals 50,541,139,865 bytes before deduplication/compression. All 94 batch
receipts and every recorded remote restore location passed the final catalog audit.
The 44 earlier release assets remain unchanged.

Files: [full original-file index](ALL_CHECKPOINTS_ORIGINALS.csv),
[restore catalog](ALL_CHECKPOINTS_STATE.json), [audit evidence](ALL_CHECKPOINTS_FINAL_REMOTE_AUDIT.json),
[numbered coverage](CHECKPOINT_COVERAGE.csv), and [saved reports and source files](.).

Each new container was downloaded and its original members checked before its batch
receipt was saved. The final audit freshly downloaded all 94 receipts and the original
inventory, checked SHA-256 hashes, exact inventory coverage, and remote asset digests.
Checkpoint 210 was freshly restored from GitHub and every original checked again from disk.
Earlier successful recovery tests for checkpoints 149 and 152 are preserved and matched
against this catalog. Both byte-distinct checkpoint-210 PDF versions remain preserved;
the earlier version also passed a fresh readback during this audit.

Checkpoints **72–75 remain unconfirmed** in the available history. Checkpoint **109 has
progress-only material**. The initial Pilot is counted as checkpoint 1; explicit iteration-124
filenames have an annotated alias. An original artifact is not necessarily a standalone
Lean project; use its own instructions to assemble incremental checkpoints.

**The manuscript and Lean source were not changed. No new Lean compilation or axiom audit
was performed. Mathematical verification remains incomplete.** The backup preserves the
existing correspondence reports, checklists, build evidence, and proof-status limitations.

The local working files became unavailable after the uploader exited. The final catalog
was reconstructed from the saved GitHub receipts. Original console logs that were not
already committed are unavailable; they have not been fabricated. The new recovery execution
is recorded at https://github.com/jaehwoo/lean-checkpoint-backup/actions/runs/40137426186. The earlier prepared `finalize_backup_catalog.py`
and `prepare_backup_publication.py` were not executed to completion; this report was produced
by `recover_and_verify_remote_backup.py` instead.

The earlier destination rejection and the tested stricter transfer route are documented
in `ENDPOINT_REVIEW_AND_SAFER_TRANSPORT.json`. Continuation permits only the designated
GitHub API/upload endpoints and credential-free redirects to the repository's GitHub
release-download CDN. Authentication files and credentials are excluded.

To restore original checkpoint-210 artifacts, install `zstandard==0.25.0`, authenticate
GitHub CLI to this private repository, and keep the restore script and strict transport together:

```sh
python3 restore_original_checkpoint_files.py --catalog ALL_CHECKPOINTS_STATE.json \
  --checkpoint 210 --assets downloaded-assets --destination restored-checkpoint-210 --download
```

Use `--all` instead of `--checkpoint 210` for all inventoried files; the destination must
not exist. Allow space for downloaded containers and the original bytes. This restores
original artifact files, not an automatically assembled or newly verified Lean project.
