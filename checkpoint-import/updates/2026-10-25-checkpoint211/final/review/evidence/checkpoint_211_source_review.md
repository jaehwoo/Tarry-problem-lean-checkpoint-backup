Checkpoint 211 completes a proper pure-quintic subcase. Verification of the manuscript and its main theorem remains incomplete.

The authoritative manuscript remains `manuscript/Complete_Affine_Jets_I_Introduction_Revision.tex`, with the accompanying fixed `manuscript/Complete_Affine_Jets_Supplement.tex`. Neither file was edited. The pinned source baseline also protects all inherited Lean modules. The integration root has only the new quintic-boundary import. The final environment gate checks these identities and all nine dependency revisions.

### Newly covered mathematics

Write `q = x-s*y*z+g*z^3` and let `N_n` be the original full coefficient norm squared of `q^n`. Here `g` is the cubic coefficient of the invariant, corresponding to `s*gamma/3` on this centered manuscript slice; it does not redefine the manuscript's `gamma`. For `s != 0`, every real `g` corresponds to that slice. The physical affine map, its constant term, and both tangential coefficients are zero in this subcase. General affine or mixed-curvature models are not covered by this batch.

The actual pure-quintic state has squared norm `N_5` and attained least unit translation energy `25*N_4*min(1,s^2)`. The proofs establish both the lower bound for every physical direction and attainment by a unit direction. They do not replace the complete energy by a single directional test. Scaling by any real `c` multiplies both squared quantities by `c^2`; nonzero `c` is required only where positivity, rank, or exclusion needs it.

For nonzero `g`, shrinking its absolute value strictly improves the norm-to-energy ratio. At `g=0`, that curve is constant, so a separate curve moves `|s|` toward 1. At `|s|=1`, the exact norm and energy are 252 and 1750, so their ratio is `18/125`, incompatible with the derived saturated ratio `A^4 >= 16`. The proof handles negative `s` by exact evenness identities, without assuming that a coordinate change preserves the original norm.

These are actual continuous coefficient-state curves in the fixed ambient space, with the original degree split: `10 <= k` when `g=0`, and `15 <= k` otherwise. The cap is preserved even when a scaled cubic coefficient becomes zero. No universal `15 <= k` hypothesis replaces the quadratic branch's cap. Rank four is obtained from the inherited classification converse.

For arbitrary natural `k,N`, real `B`, real `A >= 2`, nonzero `s,c`, the exact split cap, and the original all-direction `AugmentedTranslationStopped A` condition, `original_scaledCubicQuintic_not_mem_far_closure` excludes `(A,c*q^5,0)` from the actual bounded far-family closure. Norm saturation and ratio saturation are first derived from hypothetical closure membership using the already checked slack exclusions. They are not new premises of the exclusion theorem. The same-`A` curve lemma supplies the required normalization.

Finally `original_centered_far_closure_through_quintic_zero` retains the arbitrary profile constant through the exact representative `f(q)-C(f.coeff 0)`, the full-profile split degree cap, nonlinearity `2 <= f.natDegree`, `s != 0`, the original stop, and the actual closure condition. It derives `a_1=a_2=a_3=a_4=a_5=0` and `6 <= f.natDegree`. The pure-quintic reduction and the pure-state degree cap are conclusions of the inherited active-fifth-coefficient argument, not additional assumptions.

### Correspondence and original argument

The definitions correspond to Paper I lines 595–607 (original product coefficient norm and complete translation stop) and lines 699–737 (classified model, profile, exact degree split, and rank). The new identities and deformations are auxiliary application checks for the quantitative conditioning lemma at lines 625–638 as used in the compact-minimum paragraph at line 773. They are not literal intermediate statements in the manuscript and do not establish that whole paragraph. No original argument was abandoned or replaced. Previously recorded alternative-proof limitations, including the separate arc-length-square issue, remain in the inherited correspondence and checklist.

The closed-total-bounded-window condition at I625 is explicitly assumed in the manuscript. Its status as an assumption is not a manuscript error. The still-open task is to justify the needed application to the actual family and obtain the uniform bounded-window input. No new mathematical error was found in this batch. The earlier small-radius technical repair remains separate and unapplied: I1243, I1245, I1259, with downstream uses I1270, I1317–1323, I1326, I3217 and I3220; see `history/small_t_after147/SmallRadiusManuscriptCorrection.diff`. The authoritative text was not altered.

### Obstructions checked before selecting the proof

The exact-rational diagnostic command ran before the new Lean modules existed. It checked 121 complete Gram cases, 300 strict nonzero-cubic contractions, 24 zero-cubic shape moves, 363 scalar norm/energy cases, and three simultaneous-saturation scalar cases. Both signs, zero parameters, zero and negative scalars, the split degree caps, the `|s|=1` boundary, and the previous mixed-profile counterexample were included. The counterexample `f=X^2+X^8`, `s=g=1/100`, cubic scale `99/100` still blocks unqualified extension of cubic contraction to arbitrary mixed profiles. The scalar-saturation and affine-centering obstructions remain relevant.

The three polynomial cross-product factors have respectively 125, 25 and 25 positive-coefficient terms, with constants 9, 25 and 225. Lean proves the identities and positivity; the diagnostic program is not a proof assumption or proof certificate. An earlier exploratory attempt to import optional SymPy failed because that package was unavailable. The saved diagnostics use only the Python standard library and passed; no installation or assumption about SymPy was used.

### Execution and trust boundary

The actual compiled types of all 49 declarations, all six printed definition bodies, and all 49 literal axiom lists were reviewed against the new source and the fixed manuscript scope. Two copied prose annotations initially said fourth power; they were corrected to fifth power to match both the source and the actual compiled types. No Lean statement changed during that prose correction.

The unit compile and `Batch211AxiomAudit` execute the exact Lean 4.19.0 environment. The literal axiom output for every new declaration is `[propext, Classical.choice, Quot.sound]`. There are no new published-input contracts or conditional proof premises in these declarations. The inherited 18 external contracts and 451 conditional records remain unchanged; acceptance of a citation is still distinct from proving its application. The audit's executable metadata queries are not proof mechanisms. No native-evaluation proof mechanism is used.

The first unit compile succeeded while the integration-root import was being appended; its recorded global source-change flag is therefore false. It is retained as an earlier run, not used as the final source-binding gate. A second complete unit run passed with unchanged final sources. The compiler-recovery command's source-change flag likewise reflects proof files being written concurrently with recovery, not a completed proof gate. Final unit, audit, root-build and environment records must all pass with unchanged sources before the collector and checklist finalizer accept this batch. Minor unused-tactic lint warnings are retained in the actual logs; they are not proof failures.

The prior workspace was recovered from saved checkpoint 210. The compiler, dependency bundles, dependency cache and project overlay were hash-checked. The unchanged parent archive also preserves 427 inherited inactive transfer-copy files that were not kept expanded locally because of disk space. Their exact paths, sizes and hashes are recorded in `evidence/checkpoint_211_archived_inactive_copies.json`; final project packaging restores every parent member. Packaging and transfer checks are artifact-integrity checks, not additional Lean executions.

### Remaining work and next task

The centered case with coefficients 1 through 5 zero and degree at least 6 remains open. So do the general affine/mixed-curvature boundary case, the uniform bounded-window hypothesis, the all-parameter spectral threshold, the moved-root/implicit-graph application, polynomial radii and finite jets, own-centering, Borel labeling, covering, packing, and the complete main theorem. The exact inherited statements, Lean goal specifications, blocker categories and downstream conditional status are retained below and in the canonical checklist. The new subcase does not turn any of those broader items into a proved theorem.

Next, before choosing a further strategy, test the actual-norm comparison `36*N_5*N_n < n^2*N_6*N_(n-1)` for `n >= 7`. Check 7, 8, 9 and 10 separately, and investigate whether `N_6 >= N_1*N_5` combines with `n^2 > 108` for `n >= 11`. Retest signs, degenerate parameters, complete energies and the mixed-profile obstruction. Those comparisons and the separate pure-sixth exclusion are not asserted proved here.

Available prior-chat retrieval identified checkpoint 210 and its recorded pure-quintic task; the restored full correspondence, checklist and authoritative passages were read. This was not exhaustive access to every other chat. Previously completed checks were reused when their protected sources were unchanged. The full manuscript dependency record remains incomplete, and its counts are not completion percentages.

### Final gate result

The final unit compile, transitive axiom audit, root `lake build PaperILean`, and pinned-environment check all exited 0 with unchanged proof sources. The completed scope contains 43 theorem proofs and 6 definitions in 3 modules. Its kernel dependency closure contains 788 project declarations, with zero unexpanded nodes. All 49 literal axiom outputs contain exactly the permitted standard three axioms. The exact commands and their logs follow in the correspondence report.
