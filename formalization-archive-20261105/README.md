# Tarry Lean sources and verification reports

The 5 November 2026 archive contains 557 module sources from the fixed-a net snapshot, 3,898 distinct historical Lean source texts and 207 PDF verification reports. The ZIP contains a source provenance index. Commit [caf7bc7](https://github.com/jaehwoo/lean-checkpoint-backup/commit/caf7bc7653505dc266f84ab33b507606b7956df9) also contains the 557 module sources as plain files.

After cloning the repository or extracting its GitHub source ZIP, run the following command from this directory to reconstruct the original archive.

```sh
python3 restore_bundle.py
```

The script checks the SHA-256 of each part and of the reconstructed ZIP against [PARTS.json](PARTS.json). The original ZIP is named `Tarry_Lean_Sources_and_Verification_Reports_20261105.zip` and has SHA-256 `a69864cd762de424e18d50c13ae5e2583a26f1ffd1d13bc5b5733a15d6de24a6`.

## Later portfolio sources

The [portfolio supplement](portfolio/) includes five modules accepted in the later audited checkpoint on the same date. The two manuscript statements discharged there are weighted incidence (I3079–I3097) and projected packing (I3279–I3297). The former uses a measurable outer-hull majorant. The latter retains the manuscript's supplied normalized continuations and indexed relative-neighborhood packing hypotheses. The standalone quantitative implicit-function construction at I3299 is outside the accepted scope.

The supplement also preserves distinct audit, integration and intermediate source texts from the portfolio checkpoints. [SOURCE_PROVENANCE.json](portfolio/SOURCE_PROVENANCE.json) maps each file to its saved checkpoint members. The intermediate texts include proof attempts and carry no independent completion claim.

## Archive limits

This is a source-and-report archive. Compilation and manuscript correspondence are documented in the saved verification reports. The manuscript's main theorem remains incomplete, and historical checkpoints 72–75 remain unconfirmed. Two saved build-evidence ZIPs, PlanarTransport and PlanarWindow, had unreadable ZIP directories during source extraction.
