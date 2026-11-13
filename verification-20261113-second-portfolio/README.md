# Paper I Lean verification · 13 November 2026

This checkpoint records three complete statements that passed fresh Lean 4.19.0 builds, independent review against the manuscript, and the full declaration audit. The [verification report](verification-report.pdf) describes the exact scope. Complete Lean verification and human verification of the main theorem remain pending.

| Statement | Paper I statement lines | Proof lines | Lean source |
| --- | --- | --- | --- |
| Parabolic collars | [I980–I993](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/blob/cc2c28164c36429d4083d4fe07144bb156ad26ed/Complete_Affine_Jets_I.tex#L980-L993) | [I994–I1018](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/blob/cc2c28164c36429d4083d4fe07144bb156ad26ed/Complete_Affine_Jets_I.tex#L994-L1018) | [ParabolicCollarSource.lean](PaperILean/ParabolicCollarSource.lean) |
| Derivative good points and curved strips | [I3202–I3218](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/blob/cc2c28164c36429d4083d4fe07144bb156ad26ed/Complete_Affine_Jets_I.tex#L3202-L3218) | [I3219–I3221](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/blob/cc2c28164c36429d4083d4fe07144bb156ad26ed/Complete_Affine_Jets_I.tex#L3219-L3221) | [GoodStripWhole.lean](PaperILean/GoodStripWhole.lean), [GoodStripPlanarClosure.lean](PaperILean/GoodStripPlanarClosure.lean) |
| Algebraic surface packing cutoff | [I3312–I3317](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/blob/cc2c28164c36429d4083d4fe07144bb156ad26ed/Complete_Affine_Jets_I.tex#L3312-L3317) | [I3318–I3340](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/blob/cc2c28164c36429d4083d4fe07144bb156ad26ed/Complete_Affine_Jets_I.tex#L3318-L3340) | [AffineAreaWhole.lean](PaperILean/AffineAreaWhole.lean) |

The [verification summary](verification-summary.json) lists the Lean endpoints, retained published theorem parameters, axiom prints, proof limits, and SHA-256 checksums. The combined integration check passed with 797 imports. The [compiled products](compiled/lean-4.19.0-products.zip) contain the 50 audited `.olean` and `.ilean` files for the 25 sources here. Recompiling requires the matching Paper I project dependencies and Mathlib revision recorded in the summary.

The width-band lemma I1113–I1138, exhaustive measurable assignment at I472, and same-`P` estimate at I773 remain open.
