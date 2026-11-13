# Paper II Lean verification · 13 November 2026

Five complete Paper II statements passed fresh Lean 4.19.0 builds, independent review against the manuscript, and the full scoped declaration audit. Complete Lean verification of the main theorem remains pending.

| Statement | Manuscript statement | Manuscript proof | Lean source |
| --- | --- | --- | --- |
| Block-triangular degree lift | [II1567–II1569](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/blob/97daf4ede7c5e9870f03b2842381b9a373b8ea34/Complete_Affine_Jets_II.tex#L1567-L1569) | [II1570–II1576](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/blob/97daf4ede7c5e9870f03b2842381b9a373b8ea34/Complete_Affine_Jets_II.tex#L1570-L1576) | [PaperIIDegreeLift.lean](PaperILean/PaperIIDegreeLift.lean) |
| Quartic connection identity | [II2472–II2489](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/blob/97daf4ede7c5e9870f03b2842381b9a373b8ea34/Complete_Affine_Jets_II.tex#L2472-L2489) | [II2490–II2492](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/blob/97daf4ede7c5e9870f03b2842381b9a373b8ea34/Complete_Affine_Jets_II.tex#L2490-L2492) | [PaperIIQuarticConnection.lean](PaperILean/PaperIIQuarticConnection.lean) |
| A band interval in the coefficient map | [II4342–II4348](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/blob/97daf4ede7c5e9870f03b2842381b9a373b8ea34/Complete_Affine_Jets_II.tex#L4342-L4348) | [II4349–II4351](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/blob/97daf4ede7c5e9870f03b2842381b9a373b8ea34/Complete_Affine_Jets_II.tex#L4349-L4351) | [PaperIIVOutputBand.lean](PaperILean/PaperIIVOutputBand.lean) |
| An externally conditioned curved seed | [II4355–II4369](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/blob/97daf4ede7c5e9870f03b2842381b9a373b8ea34/Complete_Affine_Jets_II.tex#L4355-L4369) | [II4370–II4376](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/blob/97daf4ede7c5e9870f03b2842381b9a373b8ea34/Complete_Affine_Jets_II.tex#L4370-L4376) | [PaperIIPreparedCurvedSeed.lean](PaperILean/PaperIIPreparedCurvedSeed.lean) |
| Two quadratic charts cover every first slope | [II4659–II4669](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/blob/97daf4ede7c5e9870f03b2842381b9a373b8ea34/Complete_Affine_Jets_II.tex#L4659-L4669) | [II4670–II4672](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/blob/97daf4ede7c5e9870f03b2842381b9a373b8ea34/Complete_Affine_Jets_II.tex#L4670-L4672) | [PaperIITwoQuadraticCharts.lean](PaperILean/PaperIITwoQuadraticCharts.lean) |

The [verification report](verification-report.md) describes the exact scope and retained hypotheses.
The [verification summary](verification-summary.json) records the pinned dependency revisions, audit results, and file checksums.
The [audit evidence](audit/lean-4.19.0-audit-evidence.zip) includes source for the audit, declaration hash and axiom records, and independent reviews.

The [compiled products](compiled/lean-4.19.0-products.zip) contain the ten freshly matched proof outputs.
The [supporting sources](supporting-sources.zip) contain the 29 unchanged project modules they import transitively.
The [inherited products](compiled/lean-4.19.0-inherited-products.zip) contain their 29 Lean kernel objects and the 26 editor metadata files that match the saved hashes.
The new proof products were compiled against the Lean 4.19.0 Apple Silicon build and the pinned Mathlib revisions in the summary.
