# Paper I. Lean verification of the revised cap and collar argument

This package checks the revised parts of Lemmas 3.16–3.18 and Theorem 3.21 and their use in Proposition 6.4. The mathematical hypotheses in Paper I are retained. [Manuscript revision f960e06346bb](https://github.com/jaehwoo/3-dimensional-Tarry-s-problem/commit/f960e06346bb04825ba7096e0596f3cf5cef863d)

| Manuscript passage | Checked conclusion | Principal Lean declaration |
| --- | --- | --- |
| Lemma 3.16 | The exact-length horizontal seed covers all projected labels, its area has the required lower bound, and the short-family endpoints and scale tag are Borel. | `exact_geometric_cap`, `exact_seed_reaches`, `measurable_exact_short_family` |
| Lemma 3.17 | Either signed long-width hypothesis gives the horizontal bridge. In each original frame the joint point factor is bounded by a constant times the square of the scale, with a separate shear factor linear in the scale. | `signed_width_inputs`, `revised_centered_flux`, `positive_fraction_endpoint` |
| Lemma 3.18 | The selected cap or signed seed has the prescribed raw jets, original scalar and reciprocal-Jacobian estimates on a common physical good set. The centered first jet has the stated Euclidean operator-norm error. | `exact_phase_centered_cap_with_budget`, `revised_centered_flux`, `centered_first_jet` |
| Theorem 3.21, Step 2 | Every active short component receives its exact cap. The projected midpoint alone gives the signed lower bound. The assignment retains the actual seed and the original labels. | `short_corridor_span`, `revised_common_null_assignment`, `revised_assignment_from_rq` |
| Proposition 6.4 | The revised assignment supplies the input to the original coefficient-volume bound for every stated normal order and degree. | `revised_assigned_volume` |

`Correspondence.json` gives the full declaration names, manuscript line numbers, changed lines, and manuscript hashes. The [verification report](Paper_I_Collar_Lean_Verification.pdf) explains the assumptions and the two short-seed obstructions.


## Verification record

The fresh Linux build checked 34 public entries. The kernel rechecked 92 revision bodies and the dependency audit traversed 57,733 declarations. The axiom output contains only `propext`, `Classical.choice`, and `Quot.sound`. [Axiom output](evidence/audit.log) · [Build commands and hashes](evidence/build.json)

The public checkpoint contains the revised Lean sources, audit and dependency manifest. To replay, place the 1,879 matching inherited objects under `baseline/PaperILean/`, install the pinned mathlib dependencies with `lake exe cache get`, and run `python3 replay.py --out replay-run`. The accompanying full replay ZIP contains those inherited objects. Its SHA-256 is `38986e227e918049298bb32b6090f6fccfcd3e9de1f47f10a3d48cc876fefe5c`.

See [REPRODUCE.md](REPRODUCE.md) for the archive download, checksum-checked restoration, manual GitHub Actions workflow, and the exact distinction between recompiling this revision and rebuilding inherited proofs.
