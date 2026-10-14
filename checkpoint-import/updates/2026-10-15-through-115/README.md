# Paper I newer original archives: checkpoints 94-115

This additive import extends the existing private archive in `jaehwoo/lean-checkpoint-backup` (repository ID `1417233863`). The existing `checkpoint-import` records, earlier investigation, original manuscripts, Lean sources, and old Release attachments are not edited. The new Release remains a draft.

## Coverage and meaning

The new import contains complete original project packages for **94-108 and 110-115**, including two distinct checkpoint 112 packages and both the regular and Joint Selection checkpoint 113 packages. The import preserves 69 top-level original files (2,055,734,485 bytes), 23 distinct complete project packages across 21 checkpoint numbers, and original progress, checklist, build-evidence, report and delivery-verification archives. Nested originals are recorded by hash and exact extraction route.

Together with the earlier inventory, complete package coverage is **initial Pilot, 2-71, 76-108, and 110-115**. Pilot is the existing inventory's explicit number-1 convention. **72-75 remain unrecovered. No completed checkpoint 109 package was found.** Both observed 109 progress versions are preserved, including the earlier `267aa00f...` archive embedded in later packages and the current `0e1152d1...` archive. Progress is not relabeled as completed.

"Complete project package" refers to a checkpoint deliverable containing the project sources, pinned environment files, manuscripts, canonical checklist, correspondence report and recorded evidence. It does not mean that the manuscript's main theorem is fully proved. Checkpoint 115 explicitly excludes installed toolchain and cache binaries. This backup task does not recompile Lean or audit mathematical correctness.

## Source identity and versions

`sources.json`, `source_provenance.json` and `SOURCES.csv` record exact Library paths, stable file IDs, backing file IDs, returned version IDs, byte counts and SHA-256 hashes. A null version means that no numeric version was exposed; it is not a guessed version 0. Each download used the backing file ID from the resolved inventory. `CHECKPOINTS.csv` and `coverage.json` connect complete nested packages to their pinned ancestor and extraction route. Unlisted earlier Library versions were not enumerated or reconstructed.

The two hashes supplied in the task match exactly:

- `Paper_I_Lean_History_Checkpoint_104.zip`: `c47f4983fdb3462eb083e681ccb441cfabbb0b81310cc0b048492ec4095d4f39`.
- `Paper_I_Lean_Checkpoint_108.zip`: `63b6d283d8f5e57d0105d2e7da5e8b1db0908d14d81ac7b70243d683f64513a7` (reported version 87).

All 69 selected source archives were accessed successfully. `LOOKUP_SCOPE.json` describes the search boundary and remaining gaps. No existence claim is made about inaccessible or unlisted prior versions.

## Remote storage and restoration

The new private draft Release is named **Paper I newer checkpoints through 115 - private originals**, with intended tag `paper-i-checkpoints-through-115-20261015`. Its four `Paper_I_Newer_Originals_Part_*.zip` attachments are independent ZIP containers holding unchanged source archives. **Do not concatenate the Parts.** The fifth attachment, `Paper_I_Newer_Archive_Audit.json.gz`, contains the newly computed archive-member hashes. Git clone alone does not download Release attachments.

Download the five assets named in `assets.json` into one directory, retaining their filenames. From this import directory:

```bash
python3 restore.py verify --assets /backup/downloaded-assets
python3 restore.py restore --assets /backup/downloaded-assets --checkpoint 115 --destination /backup/restored-115-new
```

The destination must not already exist. The existing `checkpoint-import/restore.py` is reused byte-for-byte. It validates the attachment and original-source hashes, follows audited nested-archive routes, then reads each restored file from disk and checks its SHA-256. For 112 and 113, `coverage.json` retains both variants; the existing CLI selects its first recorded option, and the exact chosen hash appears in the restoration receipt. Use the source inventory to select the alternate original explicitly if needed.

The root `lean_backup.py` is retained unchanged. That tool creates a new operational checkpoint history in a separate initialized vault and empty private remote; importing historical originals into this existing archival repository uses its established Release-plus-catalog workflow instead of inventing replacement checkpoints.

## Verification evidence

`REMOTE_VERIFICATION.json`, `ASSET_VERIFY_RECEIPT.json`, and `RESTORE_VERIFY_RECEIPT.json` provide the actual remote-readback and restoration results when present. `ORIGINAL_MANIFEST_CHECK.json` records the exact match between all 1,785 checkpoint 115 archive members and its original delivery manifest. `SHA256SUMS` covers the five Release assets. `GIT_PAYLOAD_SHA256SUMS` covers the additive catalog payload.

Historical coverage through 93 is inherited from the preserved prior verification records, not represented as a fresh re-download of those seven large assets. Their current remote IDs, sizes and digests are compared with the pre-task inventory. All existing Git file paths and object hashes are checked unchanged after the additive commit.

Authoritative manuscript hashes in the complete newer packages remain:

- Main manuscript: `91c19e28f6e6a0733505ce066d6a42be9bfb6df1c8c31185849bc4b34b0ab914`.
- Supplement: `31b5340997aac383d037029596d1c52c88679cab366263b25ecda7d594aef312`.
