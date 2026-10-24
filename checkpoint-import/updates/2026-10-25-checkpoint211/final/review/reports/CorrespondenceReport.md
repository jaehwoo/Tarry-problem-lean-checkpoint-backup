# Paper I Lean correspondence report — checkpoint211

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

## Statement correspondence

### PaperI.originalHyperbolicQuinticNormSq

R0(a)=1+25*a^2+100*a^4+100*a^6+25*a^8+a^10, the actual g=0 fifth-power norm.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 10; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuinticYEnergy

Y0(a)=25*a^2+400*a^4+900*a^6+400*a^8+25*a^10, the g=0 transverse energy.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 11; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuinticXEnergy

X0(a)=25+400*a^2+900*a^4+400*a^6+25*a^8, the g=0 x energy.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 12; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_ratio_boundary_values

At a=0: (R0,Y0,X0)=(1,0,25). At a=1: (252,1750,1750). These identities include the degenerate boundary.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 14; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_norm_sq_pos

R0(a)>0 for every real a, including zero.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 20; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_y_energy_pos

Y0(a)>0 under a>0; the zero case is not included.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 24; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_x_energy_pos

X0(a)>0 for every real a.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 29; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_y_ratio_factor

Exact all-real cross-product factor (b^2-a^2)*P_y(a^2,b^2); P_y has 25 positive-coefficient terms and constant 25.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 33; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_x_ratio_factor

Exact all-real cross-product factor (a^2-b^2)*P_x(a^2,b^2); P_x has 25 positive-coefficient terms and constant 225.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 40; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_y_ratio_improves

Strict y-ratio comparison for0<a<b; positivity is proved before cancellation.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 47; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_x_ratio_improves

Strict x-ratio comparison for0<b<a; no branch choice is hidden.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 57; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_ratio_improvement_below

For0<a<1 and the explicit saturated y-ratio, arbitrarily nearby b>a below1 gives strict improvement. A is arbitrary here.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 67; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_ratio_improvement_above

For1<a and the explicit saturated x-ratio, arbitrarily nearby1<b<a gives strict improvement. A is arbitrary here.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 83; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_ratio_one_strict

For A>=2, R0(1)=252 is strictly less than A^4*1750. Simultaneous saturation at |s|=1 is excluded, without a new hypothesis.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 99; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_energy_factor

Exact Y0=a^2*X0 for every real a.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 108; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_min_below

If a^2<=1 the attained minimum is Y0; equality is retained.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 113; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_min_above

If1<=a^2 the attained minimum is X0; equality is retained.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 120; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_ratio_even

R0,X0,Y0 are even by polynomial identities; no coordinate-norm invariance is invoked.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 127; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_min_ratio_improvement_pos

Under A>=2, a>0 and explicit min-ratio saturation, frequent nearby nonzero shapes strictly improve the ratio; crossing a=1 is impossible.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 134; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalHyperbolicQuintic_min_ratio_improvement

The same frequent improvement for every nonzero real a; negative a follows from proved evenness and continuity of negation.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 156; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalCubicQuinticNormSq

The 21-term expansion of N_5 in s^2,g^2; a definition matched to the actual coefficient norm by originalCubicQuinticState_norm_sq.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 178; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalCubicQuinticMinEnergy

E(s,g)=25*N_4*min(1,s^2), with the full N_4 expansion. Actual all-direction lower bound and unit attainment are separately proved.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 181; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalCubicQuintic_norm_pos

R(s,g)>0 for all real s,g, including both zeros.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 184; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalCubicQuintic_energy_pos

E(s,g)>0 when s!=0, with g unrestricted.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 189; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalCubicQuintic_zero_data

At g=0 the new exact formulas coincide with R0 and min(X0,Y0), for all real s.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 193; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalCubicQuintic_g_ratio_factor

For all real s,g,h, R(s,g)E(s,h)-R(s,h)E(s,g)=min(1,s^2)*25*(g^2-h^2)*P(s^2,g^2,h^2). The 125-term factor has positive coefficients and constant 9; the identity is proved in Lean, not assumed from diagnostics.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 204; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalCubicQuintic_g_ratio_improves

For s!=0,h^2<g^2, strict normalized energy comparison; no sign restriction on g or h.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 213; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalCubicQuintic_g_ratio_improvement

For s,g nonzero and R=A^4E, arbitrarily nearby0<b<1 makes R(s,bg)<A^4E(s,bg). This is a pure-quintic result only.

Source: `PaperILean/OriginalCubicQuinticRatio.lean`, declaration line 224; SHA256 `eff5a04f695c06a0c4c05a21edd02fa35d4eda37ec7821f784fa928e07089f0b`.

### PaperI.originalCubicQuinticState

Actual original zero-physical state q^5. Retains the exact split cap (if g=0 then 2 else 3)*5<=k: 10 when g=0 and 15 otherwise.

Source: `PaperILean/OriginalCubicQuinticState.lean`, declaration line 10; SHA256 `c9181f27821745416e291d1cacd928786b46d6910f7f78634038211a1f05a672`.

### PaperI.originalCubicQuinticState_polynomial

The state polynomial is exactly(x-s*y*z+g*z^3)^5; all real signs and zero parameters are allowed within the cap.

Source: `PaperILean/OriginalCubicQuinticState.lean`, declaration line 15; SHA256 `c9181f27821745416e291d1cacd928786b46d6910f7f78634038211a1f05a672`.

### PaperI.originalCubicQuinticState_profile

Exact representation by f=X^5 with the original subtraction of the constant coefficient.

Source: `PaperILean/OriginalCubicQuinticState.lean`, declaration line 23; SHA256 `c9181f27821745416e291d1cacd928786b46d6910f7f78634038211a1f05a672`.

### PaperI.originalCubicQuinticState_rank

Rank four under s!=0, unrestricted g and exact ambient cap, from the checked classification converse.

Source: `PaperILean/OriginalCubicQuinticState.lean`, declaration line 30; SHA256 `c9181f27821745416e291d1cacd928786b46d6910f7f78634038211a1f05a672`.

### PaperI.originalCubicQuinticState_norm_sq

The squared augmented norm of the fifth-power state equals R(s,g) in the original unweighted norm; no constant term is discarded without its vanishing.

Source: `PaperILean/OriginalCubicQuinticState.lean`, declaration line 39; SHA256 `c9181f27821745416e291d1cacd928786b46d6910f7f78634038211a1f05a672`.

### PaperI.originalCubicQuinticState_x_energy

Actual x-translation energy is 25*N_4, including both signs and zero parameters.

Source: `PaperILean/OriginalCubicQuinticState.lean`, declaration line 50; SHA256 `c9181f27821745416e291d1cacd928786b46d6910f7f78634038211a1f05a672`.

### PaperI.originalCubicQuinticState_translation_lower

For every physical h, E(s,g)*||h||^2 bounds the complete augmented translation energy below; uses the proved full energy order.

Source: `PaperILean/OriginalCubicQuinticState.lean`, declaration line 58; SHA256 `c9181f27821745416e291d1cacd928786b46d6910f7f78634038211a1f05a672`.

### PaperI.originalCubicQuinticState_translation_attained

Some unit physical direction attains E(s,g); valid even when s=0 and the minimum is zero.

Source: `PaperILean/OriginalCubicQuinticState.lean`, declaration line 69; SHA256 `c9181f27821745416e291d1cacd928786b46d6910f7f78634038211a1f05a672`.

### PaperI.original_centered_quintic_expansion

Exact 21-term expansion of q^5 for all real s,g; used to prove actual coefficient-state continuity.

Source: `PaperILean/OriginalCubicQuinticState.lean`, declaration line 80; SHA256 `c9181f27821745416e291d1cacd928786b46d6910f7f78634038211a1f05a672`.

### PaperI.originalCubicQuinticState_continuous

For any continuous real functions s(t),g(t) and a pointwise valid fixed ambient cap, the actual state curve is continuous. The later curves supply this cap.

Source: `PaperILean/OriginalCubicQuinticState.lean`, declaration line 106; SHA256 `c9181f27821745416e291d1cacd928786b46d6910f7f78634038211a1f05a672`.

### PaperI.originalCubicQuintic_scaled_g_cap

For every real t, replacing g by t*g preserves the original cap; includes g=0 and degree drop at t=0.

Source: `PaperILean/OriginalCubicQuinticState.lean`, declaration line 123; SHA256 `c9181f27821745416e291d1cacd928786b46d6910f7f78634038211a1f05a672`.

### PaperI.original_scaledCubicQuintic_norm_sq

The squared original norm of c times the fifth-power state is c^2*R(s,g), including c=0.

Source: `PaperILean/OriginalCubicQuinticBoundary.lean`, declaration line 9; SHA256 `b93191d38761c550d835f723509d322d9fd05086aaa56d4364551a3500f5f747`.

### PaperI.original_scaledCubicQuintic_norm_pos

Positive actual norm for c!=0; no s or g nondegeneracy is needed here.

Source: `PaperILean/OriginalCubicQuinticBoundary.lean`, declaration line 15; SHA256 `b93191d38761c550d835f723509d322d9fd05086aaa56d4364551a3500f5f747`.

### PaperI.original_scaledCubicQuintic_translation_lower

The complete translation lower bound scales by c^2 for every h and every real c.

Source: `PaperILean/OriginalCubicQuinticBoundary.lean`, declaration line 22; SHA256 `b93191d38761c550d835f723509d322d9fd05086aaa56d4364551a3500f5f747`.

### PaperI.original_scaledCubicQuintic_translation_attained

A unit direction attains c^2E(s,g), including degenerate scalar c=0.

Source: `PaperILean/OriginalCubicQuinticBoundary.lean`, declaration line 31; SHA256 `b93191d38761c550d835f723509d322d9fd05086aaa56d4364551a3500f5f747`.

### PaperI.original_scaledCubicQuintic_far_closure_ratio

For s,c nonzero, original cap, A>=2 and original A-stop plus actual bounded far closure, derives norm=A and R=A^4E. Saturation is a conclusion, not an added premise of exclusion.

Source: `PaperILean/OriginalCubicQuinticBoundary.lean`, declaration line 40; SHA256 `b93191d38761c550d835f723509d322d9fd05086aaa56d4364551a3500f5f747`.

### PaperI.original_scaledCubicQuintic_not_mem_far_closure

Unconditional exclusion within the original pure-quintic branch for arbitrary k,N,B and A>=2: s,c nonzero, exact cap and A-stop suffice. Handles g!=0 by contraction and g=0 by |s| variation; same-A normalization is inherited and checked.

Source: `PaperILean/OriginalCubicQuinticBoundary.lean`, declaration line 75; SHA256 `b93191d38761c550d835f723509d322d9fd05086aaa56d4364551a3500f5f747`.

### PaperI.original_centered_quintic_state_eq

Any coefficient representative equal to C(c)*q^5 equals the constructed scaled zero-physical state. No nonzero premise or extra normalization.

Source: `PaperILean/OriginalCubicQuinticBoundary.lean`, declaration line 120; SHA256 `b93191d38761c550d835f723509d322d9fd05086aaa56d4364551a3500f5f747`.

### PaperI.original_centered_quintic_not_mem_far_closure

Actual-representative version of pure-quintic exclusion with exactly the displayed original hypotheses; no shape-existence or density assumption.

Source: `PaperILean/OriginalCubicQuinticBoundary.lean`, declaration line 134; SHA256 `b93191d38761c550d835f723509d322d9fd05086aaa56d4364551a3500f5f747`.

### PaperI.original_centered_far_closure_quintic_zero

Under the original centered-profile hypotheses hf>=2, exact full-profile degree cap, s!=0, A>=2 and full all-direction stop, a_5=0. The pure-quintic reduction and pure-state cap are derived, not added as hypotheses. The arbitrary profile constant is retained.

Source: `PaperILean/OriginalCubicQuinticBoundary.lean`, declaration line 144; SHA256 `b93191d38761c550d835f723509d322d9fd05086aaa56d4364551a3500f5f747`.

### PaperI.original_centered_far_closure_through_quintic_zero

Derives a_1=a_2=a_3=a_4=a_5=0 and natDegree(f)>=6 for the actual stopped centered far closure. Uses inherited through-quartic vanishing and new quintic exclusion. Does not exclude remaining degree>=6 profiles or prove uniform hwindow.

Source: `PaperILean/OriginalCubicQuinticBoundary.lean`, declaration line 156; SHA256 `b93191d38761c550d835f723509d322d9fd05086aaa56d4364551a3500f5f747`.

## Actual executed commands

Working directory: `/workspace/scratch/9e45cd855c91/resume211/work/PaperILean`.

1. `python3 tools/checkpoint211_pre_strategy.py`: exit 0; sources unchanged during command: True; `evidence/checkpoint_211_001_pre_strategy.log`; start UTC 2026-10-24T23:33:20.638936+00:00.

2. `python3 tools/checkpoint211_restore_environment.py runtime`: exit 0; sources unchanged during command: False; `evidence/checkpoint_211_002_restore_runtime.log`; start UTC 2026-10-24T23:33:23.684540+00:00.

3. `python3 tools/checkpoint211_restore_environment.py cache`: exit 0; sources unchanged during command: True; `evidence/checkpoint_211_003_restore_cache.log`; start UTC 2026-10-24T23:34:42.348894+00:00.

4. `python3 tools/checkpoint211_lean_unit.py OriginalCubicQuinticRatio OriginalCubicQuinticState OriginalCubicQuinticBoundary`: exit 0; sources unchanged during command: False; `evidence/checkpoint_211_004_final_units.log`; start UTC 2026-10-24T23:36:53.430940+00:00.

5. `python3 tools/checkpoint211_lean_unit.py OriginalCubicQuinticRatio OriginalCubicQuinticState OriginalCubicQuinticBoundary`: exit 0; sources unchanged during command: True; `evidence/checkpoint_211_005_final_units.log`; start UTC 2026-10-24T23:41:48.839621+00:00.

6. `python3 tools/checkpoint211_lean_unit.py Batch211AxiomAudit`: exit 0; sources unchanged during command: True; `evidence/checkpoint_211_006_final_axiom_audit.log`; start UTC 2026-10-24T23:47:07.904774+00:00.

7. `python3 tools/lean_command.py lake build PaperILean`: exit 0; sources unchanged during command: True; `evidence/checkpoint_211_007_root_integration.log`; start UTC 2026-10-24T23:48:05.508052+00:00.

8. `python3 tools/checkpoint211_environment.py`: exit 0; sources unchanged during command: True; `evidence/checkpoint_211_008_pinned_environment.log`; start UTC 2026-10-24T23:53:31.030512+00:00.

## Literal executed axiom outputs

```text
'PaperI.originalHyperbolicQuinticNormSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuinticYEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuinticXEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_ratio_boundary_values' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_norm_sq_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_y_energy_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_x_energy_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_y_ratio_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_x_ratio_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_y_ratio_improves' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_x_ratio_improves' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_ratio_improvement_below' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_ratio_improvement_above' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_ratio_one_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_energy_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_min_below' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_min_above' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_ratio_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_min_ratio_improvement_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalHyperbolicQuintic_min_ratio_improvement' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuinticNormSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuinticMinEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuintic_norm_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuintic_energy_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuintic_zero_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuintic_g_ratio_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuintic_g_ratio_improves' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuintic_g_ratio_improvement' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuinticState' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuinticState_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuinticState_profile' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuinticState_rank' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuinticState_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuinticState_x_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuinticState_translation_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuinticState_translation_attained' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.original_centered_quintic_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuinticState_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.originalCubicQuintic_scaled_g_cap' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.original_scaledCubicQuintic_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.original_scaledCubicQuintic_norm_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.original_scaledCubicQuintic_translation_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.original_scaledCubicQuintic_translation_attained' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.original_scaledCubicQuintic_far_closure_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.original_scaledCubicQuintic_not_mem_far_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.original_centered_quintic_state_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.original_centered_quintic_not_mem_far_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.original_centered_far_closure_quintic_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.original_centered_far_closure_through_quintic_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Actual compiled types

### PaperI.originalHyperbolicQuinticNormSq

```lean
PaperI.originalHyperbolicQuinticNormSq (a : ℝ) : ℝ
```

### PaperI.originalHyperbolicQuinticYEnergy

```lean
PaperI.originalHyperbolicQuinticYEnergy (a : ℝ) : ℝ
```

### PaperI.originalHyperbolicQuinticXEnergy

```lean
PaperI.originalHyperbolicQuinticXEnergy (a : ℝ) : ℝ
```

### PaperI.originalHyperbolicQuintic_ratio_boundary_values

```lean
PaperI.originalHyperbolicQuintic_ratio_boundary_values :
  PaperI.originalHyperbolicQuinticNormSq 0 = 1 ∧
    PaperI.originalHyperbolicQuinticYEnergy 0 = 0 ∧
      PaperI.originalHyperbolicQuinticXEnergy 0 = 25 ∧
        PaperI.originalHyperbolicQuinticNormSq 1 = 252 ∧
          PaperI.originalHyperbolicQuinticYEnergy 1 = 1750 ∧ PaperI.originalHyperbolicQuinticXEnergy 1 = 1750
```

### PaperI.originalHyperbolicQuintic_norm_sq_pos

```lean
PaperI.originalHyperbolicQuintic_norm_sq_pos (a : ℝ) : 0 < PaperI.originalHyperbolicQuinticNormSq a
```

### PaperI.originalHyperbolicQuintic_y_energy_pos

```lean
PaperI.originalHyperbolicQuintic_y_energy_pos {a : ℝ} (ha : 0 < a) : 0 < PaperI.originalHyperbolicQuinticYEnergy a
```

### PaperI.originalHyperbolicQuintic_x_energy_pos

```lean
PaperI.originalHyperbolicQuintic_x_energy_pos (a : ℝ) : 0 < PaperI.originalHyperbolicQuinticXEnergy a
```

### PaperI.originalHyperbolicQuintic_y_ratio_factor

```lean
PaperI.originalHyperbolicQuintic_y_ratio_factor (a b : ℝ) :
  PaperI.originalHyperbolicQuinticNormSq a * PaperI.originalHyperbolicQuinticYEnergy b -
      PaperI.originalHyperbolicQuinticNormSq b * PaperI.originalHyperbolicQuinticYEnergy a =
    (b ^ 2 - a ^ 2) *
      (25 + 400 * b ^ 2 + 900 * b ^ 4 + 400 * b ^ 6 + 25 * b ^ 8 + 400 * a ^ 2 + 8400 * a ^ 2 * b ^ 2 +
                                          20400 * a ^ 2 * b ^ 4 +
                                        9400 * a ^ 2 * b ^ 6 +
                                      600 * a ^ 2 * b ^ 8 +
                                    900 * a ^ 4 +
                                  20400 * a ^ 4 * b ^ 2 +
                                59400 * a ^ 4 * b ^ 4 +
                              30600 * a ^ 4 * b ^ 6 +
                            2100 * a ^ 4 * b ^ 8 +
                          400 * a ^ 6 +
                        9400 * a ^ 6 * b ^ 2 +
                      30600 * a ^ 6 * b ^ 4 +
                    19600 * a ^ 6 * b ^ 6 +
                  1600 * a ^ 6 * b ^ 8 +
                25 * a ^ 8 +
              600 * a ^ 8 * b ^ 2 +
            2100 * a ^ 8 * b ^ 4 +
          1600 * a ^ 8 * b ^ 6 +
        225 * a ^ 8 * b ^ 8)
```

### PaperI.originalHyperbolicQuintic_x_ratio_factor

```lean
PaperI.originalHyperbolicQuintic_x_ratio_factor (a b : ℝ) :
  PaperI.originalHyperbolicQuinticNormSq a * PaperI.originalHyperbolicQuinticXEnergy b -
      PaperI.originalHyperbolicQuinticNormSq b * PaperI.originalHyperbolicQuinticXEnergy a =
    (a ^ 2 - b ^ 2) *
      (225 + 1600 * b ^ 2 + 2100 * b ^ 4 + 600 * b ^ 6 + 25 * b ^ 8 + 1600 * a ^ 2 + 19600 * a ^ 2 * b ^ 2 +
                                          30600 * a ^ 2 * b ^ 4 +
                                        9400 * a ^ 2 * b ^ 6 +
                                      400 * a ^ 2 * b ^ 8 +
                                    2100 * a ^ 4 +
                                  30600 * a ^ 4 * b ^ 2 +
                                59400 * a ^ 4 * b ^ 4 +
                              20400 * a ^ 4 * b ^ 6 +
                            900 * a ^ 4 * b ^ 8 +
                          600 * a ^ 6 +
                        9400 * a ^ 6 * b ^ 2 +
                      20400 * a ^ 6 * b ^ 4 +
                    8400 * a ^ 6 * b ^ 6 +
                  400 * a ^ 6 * b ^ 8 +
                25 * a ^ 8 +
              400 * a ^ 8 * b ^ 2 +
            900 * a ^ 8 * b ^ 4 +
          400 * a ^ 8 * b ^ 6 +
        25 * a ^ 8 * b ^ 8)
```

### PaperI.originalHyperbolicQuintic_y_ratio_improves

```lean
PaperI.originalHyperbolicQuintic_y_ratio_improves {a b : ℝ} (ha : 0 < a) (hab : a < b) :
  PaperI.originalHyperbolicQuinticNormSq b * PaperI.originalHyperbolicQuinticYEnergy a <
    PaperI.originalHyperbolicQuinticNormSq a * PaperI.originalHyperbolicQuinticYEnergy b
```

### PaperI.originalHyperbolicQuintic_x_ratio_improves

```lean
PaperI.originalHyperbolicQuintic_x_ratio_improves {a b : ℝ} (hb : 0 < b) (hba : b < a) :
  PaperI.originalHyperbolicQuinticNormSq b * PaperI.originalHyperbolicQuinticXEnergy a <
    PaperI.originalHyperbolicQuinticNormSq a * PaperI.originalHyperbolicQuinticXEnergy b
```

### PaperI.originalHyperbolicQuintic_ratio_improvement_below

```lean
PaperI.originalHyperbolicQuintic_ratio_improvement_below {a A : ℝ} (ha : 0 < a) (ha1 : a < 1)
  (he : PaperI.originalHyperbolicQuinticNormSq a = A ^ 4 * PaperI.originalHyperbolicQuinticYEnergy a) :
  ∃ᶠ (b : ℝ) in nhds a,
    0 < b ∧ b < 1 ∧ PaperI.originalHyperbolicQuinticNormSq b < A ^ 4 * PaperI.originalHyperbolicQuinticYEnergy b
```

### PaperI.originalHyperbolicQuintic_ratio_improvement_above

```lean
PaperI.originalHyperbolicQuintic_ratio_improvement_above {a A : ℝ} (ha1 : 1 < a)
  (he : PaperI.originalHyperbolicQuinticNormSq a = A ^ 4 * PaperI.originalHyperbolicQuinticXEnergy a) :
  ∃ᶠ (b : ℝ) in nhds a,
    1 < b ∧ PaperI.originalHyperbolicQuinticNormSq b < A ^ 4 * PaperI.originalHyperbolicQuinticXEnergy b
```

### PaperI.originalHyperbolicQuintic_ratio_one_strict

```lean
PaperI.originalHyperbolicQuintic_ratio_one_strict {A : ℝ} (hA : 2 ≤ A) :
  PaperI.originalHyperbolicQuinticNormSq 1 < A ^ 4 * PaperI.originalHyperbolicQuinticYEnergy 1 ∧
    PaperI.originalHyperbolicQuinticNormSq 1 < A ^ 4 * PaperI.originalHyperbolicQuinticXEnergy 1
```

### PaperI.originalHyperbolicQuintic_energy_factor

```lean
PaperI.originalHyperbolicQuintic_energy_factor (a : ℝ) :
  PaperI.originalHyperbolicQuinticYEnergy a = a ^ 2 * PaperI.originalHyperbolicQuinticXEnergy a
```

### PaperI.originalHyperbolicQuintic_min_below

```lean
PaperI.originalHyperbolicQuintic_min_below {a : ℝ} (ha : a ^ 2 ≤ 1) :
  min (PaperI.originalHyperbolicQuinticXEnergy a) (PaperI.originalHyperbolicQuinticYEnergy a) =
    PaperI.originalHyperbolicQuinticYEnergy a
```

### PaperI.originalHyperbolicQuintic_min_above

```lean
PaperI.originalHyperbolicQuintic_min_above {a : ℝ} (ha : 1 ≤ a ^ 2) :
  min (PaperI.originalHyperbolicQuinticXEnergy a) (PaperI.originalHyperbolicQuinticYEnergy a) =
    PaperI.originalHyperbolicQuinticXEnergy a
```

### PaperI.originalHyperbolicQuintic_ratio_even

```lean
PaperI.originalHyperbolicQuintic_ratio_even (a : ℝ) :
  PaperI.originalHyperbolicQuinticNormSq (-a) = PaperI.originalHyperbolicQuinticNormSq a ∧
    PaperI.originalHyperbolicQuinticXEnergy (-a) = PaperI.originalHyperbolicQuinticXEnergy a ∧
      PaperI.originalHyperbolicQuinticYEnergy (-a) = PaperI.originalHyperbolicQuinticYEnergy a
```

### PaperI.originalHyperbolicQuintic_min_ratio_improvement_pos

```lean
PaperI.originalHyperbolicQuintic_min_ratio_improvement_pos {a A : ℝ} (hA : 2 ≤ A) (ha : 0 < a)
  (he :
    PaperI.originalHyperbolicQuinticNormSq a =
      A ^ 4 * min (PaperI.originalHyperbolicQuinticXEnergy a) (PaperI.originalHyperbolicQuinticYEnergy a)) :
  ∃ᶠ (b : ℝ) in nhds a,
    b ≠ 0 ∧
      PaperI.originalHyperbolicQuinticNormSq b <
        A ^ 4 * min (PaperI.originalHyperbolicQuinticXEnergy b) (PaperI.originalHyperbolicQuinticYEnergy b)
```

### PaperI.originalHyperbolicQuintic_min_ratio_improvement

```lean
PaperI.originalHyperbolicQuintic_min_ratio_improvement {a A : ℝ} (hA : 2 ≤ A) (ha : a ≠ 0)
  (he :
    PaperI.originalHyperbolicQuinticNormSq a =
      A ^ 4 * min (PaperI.originalHyperbolicQuinticXEnergy a) (PaperI.originalHyperbolicQuinticYEnergy a)) :
  ∃ᶠ (b : ℝ) in nhds a,
    b ≠ 0 ∧
      PaperI.originalHyperbolicQuinticNormSq b <
        A ^ 4 * min (PaperI.originalHyperbolicQuinticXEnergy b) (PaperI.originalHyperbolicQuinticYEnergy b)
```

### PaperI.originalCubicQuinticNormSq

```lean
PaperI.originalCubicQuinticNormSq (s g : ℝ) : ℝ
```

### PaperI.originalCubicQuinticMinEnergy

```lean
PaperI.originalCubicQuinticMinEnergy (s g : ℝ) : ℝ
```

### PaperI.originalCubicQuintic_norm_pos

```lean
PaperI.originalCubicQuintic_norm_pos (s g : ℝ) : 0 < PaperI.originalCubicQuinticNormSq s g
```

### PaperI.originalCubicQuintic_energy_pos

```lean
PaperI.originalCubicQuintic_energy_pos {s : ℝ} (hs : s ≠ 0) (g : ℝ) : 0 < PaperI.originalCubicQuinticMinEnergy s g
```

### PaperI.originalCubicQuintic_zero_data

```lean
PaperI.originalCubicQuintic_zero_data (s : ℝ) :
  PaperI.originalCubicQuinticNormSq s 0 = PaperI.originalHyperbolicQuinticNormSq s ∧
    PaperI.originalCubicQuinticMinEnergy s 0 =
      min (PaperI.originalHyperbolicQuinticXEnergy s) (PaperI.originalHyperbolicQuinticYEnergy s)
```

### PaperI.originalCubicQuintic_g_ratio_factor

```lean
PaperI.originalCubicQuintic_g_ratio_factor (s g h : ℝ) :
  PaperI.originalCubicQuinticNormSq s g * PaperI.originalCubicQuinticMinEnergy s h -
      PaperI.originalCubicQuinticNormSq s h * PaperI.originalCubicQuinticMinEnergy s g =
    min 1 (s ^ 2) * 25 * (g ^ 2 - h ^ 2) *
      (9 + 64 * h ^ 2 + 84 * h ^ 4 + 24 * h ^ 6 + 1 * h ^ 8 + 64 * g ^ 2 + 784 * g ^ 2 * h ^ 2 + 1224 * g ^ 2 * h ^ 4 +
                                                                                                                                                                                                                                                376 *
                                                                                                                                                                                                                                                    g ^
                                                                                                                                                                                                                                                      2 *
                                                                                                                                                                                                                                                  h ^
                                                                                                                                                                                                                                                    6 +
                                                                                                                                                                                                                                              16 *
                                                                                                                                                                                                                                                  g ^
                                                                                                                                                                                                                                                    2 *
                                                                                                                                                                                                                                                h ^
                                                                                                                                                                                                                                                  8 +
                                                                                                                                                                                                                                            84 *
                                                                                                                                                                                                                                              g ^
                                                                                                                                                                                                                                                4 +
                                                                                                                                                                                                                                          1224 *
                                                                                                                                                                                                                                              g ^
                                                                                                                                                                                                                                                4 *
                                                                                                                                                                                                                                            h ^
                                                                                                                                                                                                                                              2 +
                                                                                                                                                                                                                                        2376 *
                                                                                                                                                                                                                                            g ^
                                                                                                                                                                                                                                              4 *
                                                                                                                                                                                                                                          h ^
                                                                                                                                                                                                                                            4 +
                                                                                                                                                                                                                                      816 *
                                                                                                                                                                                                                                          g ^
                                                                                                                                                                                                                                            4 *
                                                                                                                                                                                                                                        h ^
                                                                                                                                                                                                                                          6 +
                                                                                                                                                                                                                                    36 *
                                                                                                                                                                                                                                        g ^
                                                                                                                                                                                                                                          4 *
                                                                                                                                                                                                                                      h ^
                                                                                                                                                                                                                                        8 +
                                                                                                                                                                                                                                  24 *
                                                                                                                                                                                                                                    g ^
                                                                                                                                                                                                                                      6 +
                                                                                                                                                                                                                                376 *
                                                                                                                                                                                                                                    g ^
                                                                                                                                                                                                                                      6 *
                                                                                                                                                                                                                                  h ^
                                                                                                                                                                                                                                    2 +
                                                                                                                                                                                                                              816 *
                                                                                                                                                                                                                                  g ^
                                                                                                                                                                                                                                    6 *
                                                                                                                                                                                                                                h ^
                                                                                                                                                                                                                                  4 +
                                                                                                                                                                                                                            336 *
                                                                                                                                                                                                                                g ^
                                                                                                                                                                                                                                  6 *
                                                                                                                                                                                                                              h ^
                                                                                                                                                                                                                                6 +
                                                                                                                                                                                                                          16 *
                                                                                                                                                                                                                              g ^
                                                                                                                                                                                                                                6 *
                                                                                                                                                                                                                            h ^
                                                                                                                                                                                                                              8 +
                                                                                                                                                                                                                        1 *
                                                                                                                                                                                                                          g ^
                                                                                                                                                                                                                            8 +
                                                                                                                                                                                                                      16 *
                                                                                                                                                                                                                          g ^
                                                                                                                                                                                                                            8 *
                                                                                                                                                                                                                        h ^
                                                                                                                                                                                                                          2 +
                                                                                                                                                                                                                    36 *
                                                                                                                                                                                                                        g ^
                                                                                                                                                                                                                          8 *
                                                                                                                                                                                                                      h ^
                                                                                                                                                                                                                        4 +
                                                                                                                                                                                                                  16 *
                                                                                                                                                                                                                      g ^
                                                                                                                                                                                                                        8 *
                                                                                                                                                                                                                    h ^
                                                                                                                                                                                                                      6 +
                                                                                                                                                                                                                1 *
                                                                                                                                                                                                                    g ^
                                                                                                                                                                                                                      8 *
                                                                                                                                                                                                                  h ^
                                                                                                                                                                                                                    8 +
                                                                                                                                                                                                              256 *
                                                                                                                                                                                                                s ^
                                                                                                                                                                                                                  2 +
                                                                                                                                                                                                            1456 *
                                                                                                                                                                                                                s ^
                                                                                                                                                                                                                  2 *
                                                                                                                                                                                                              h ^
                                                                                                                                                                                                                2 +
                                                                                                                                                                                                          1584 *
                                                                                                                                                                                                              s ^
                                                                                                                                                                                                                2 *
                                                                                                                                                                                                            h ^
                                                                                                                                                                                                              4 +
                                                                                                                                                                                                        400 *
                                                                                                                                                                                                            s ^
                                                                                                                                                                                                              2 *
                                                                                                                                                                                                          h ^
                                                                                                                                                                                                            6 +
                                                                                                                                                                                                      16 *
                                                                                                                                                                                                          s ^
                                                                                                                                                                                                            2 *
                                                                                                                                                                                                        h ^
                                                                                                                                                                                                          8 +
                                                                                                                                                                                                    1456 *
                                                                                                                                                                                                        s ^
                                                                                                                                                                                                          2 *
                                                                                                                                                                                                      g ^
                                                                                                                                                                                                        2 +
                                                                                                                                                                                                  12384 *
                                                                                                                                                                                                        s ^
                                                                                                                                                                                                          2 *
                                                                                                                                                                                                      g ^
                                                                                                                                                                                                        2 *
                                                                                                                                                                                                    h ^
                                                                                                                                                                                                      2 +
                                                                                                                                                                                                14400 *
                                                                                                                                                                                                      s ^
                                                                                                                                                                                                        2 *
                                                                                                                                                                                                    g ^
                                                                                                                                                                                                      2 *
                                                                                                                                                                                                  h ^
                                                                                                                                                                                                    4 +
                                                                                                                                                                                              3616 *
                                                                                                                                                                                                    s ^
                                                                                                                                                                                                      2 *
                                                                                                                                                                                                  g ^
                                                                                                                                                                                                    2 *
                                                                                                                                                                                                h ^
                                                                                                                                                                                                  6 +
                                                                                                                                                                                            144 *
                                                                                                                                                                                                  s ^
                                                                                                                                                                                                    2 *
                                                                                                                                                                                                g ^
                                                                                                                                                                                                  2 *
                                                                                                                                                                                              h ^
                                                                                                                                                                                                8 +
                                                                                                                                                                                          1584 *
                                                                                                                                                                                              s ^
                                                                                                                                                                                                2 *
                                                                                                                                                                                            g ^
                                                                                                                                                                                              4 +
                                                                                                                                                                                        14400 *
                                                                                                                                                                                              s ^
                                                                                                                                                                                                2 *
                                                                                                                                                                                            g ^
                                                                                                                                                                                              4 *
                                                                                                                                                                                          h ^
                                                                                                                                                                                            2 +
                                                                                                                                                                                      16416 *
                                                                                                                                                                                            s ^
                                                                                                                                                                                              2 *
                                                                                                                                                                                          g ^
                                                                                                                                                                                            4 *
                                                                                                                                                                                        h ^
                                                                                                                                                                                          4 +
                                                                                                                                                                                    3744 *
                                                                                                                                                                                          s ^
                                                                                                                                                                                            2 *
                                                                                                                                                                                        g ^
                                                                                                                                                                                          4 *
                                                                                                                                                                                      h ^
                                                                                                                                                                                        6 +
                                                                                                                                                                                  144 *
                                                                                                                                                                                        s ^
                                                                                                                                                                                          2 *
                                                                                                                                                                                      g ^
                                                                                                                                                                                        4 *
                                                                                                                                                                                    h ^
                                                                                                                                                                                      8 +
                                                                                                                                                                                400 *
                                                                                                                                                                                    s ^
                                                                                                                                                                                      2 *
                                                                                                                                                                                  g ^
                                                                                                                                                                                    6 +
                                                                                                                                                                              3616 *
                                                                                                                                                                                    s ^
                                                                                                                                                                                      2 *
                                                                                                                                                                                  g ^
                                                                                                                                                                                    6 *
                                                                                                                                                                                h ^
                                                                                                                                                                                  2 +
                                                                                                                                                                            3744 *
                                                                                                                                                                                  s ^
                                                                                                                                                                                    2 *
                                                                                                                                                                                g ^
                                                                                                                                                                                  6 *
                                                                                                                                                                              h ^
                                                                                                                                                                                4 +
                                                                                                                                                                          544 *
                                                                                                                                                                                s ^
                                                                                                                                                                                  2 *
                                                                                                                                                                              g ^
                                                                                                                                                                                6 *
                                                                                                                                                                            h ^
                                                                                                                                                                              6 +
                                                                                                                                                                        16 *
                                                                                                                                                                              s ^
                                                                                                                                                                                2 *
                                                                                                                                                                            g ^
                                                                                                                                                                              6 *
                                                                                                                                                                          h ^
                                                                                                                                                                            8 +
                                                                                                                                                                      16 *
                                                                                                                                                                          s ^
                                                                                                                                                                            2 *
                                                                                                                                                                        g ^
                                                                                                                                                                          8 +
                                                                                                                                                                    144 *
                                                                                                                                                                          s ^
                                                                                                                                                                            2 *
                                                                                                                                                                        g ^
                                                                                                                                                                          8 *
                                                                                                                                                                      h ^
                                                                                                                                                                        2 +
                                                                                                                                                                  144 *
                                                                                                                                                                        s ^
                                                                                                                                                                          2 *
                                                                                                                                                                      g ^
                                                                                                                                                                        8 *
                                                                                                                                                                    h ^
                                                                                                                                                                      4 +
                                                                                                                                                                16 *
                                                                                                                                                                      s ^
                                                                                                                                                                        2 *
                                                                                                                                                                    g ^
                                                                                                                                                                      8 *
                                                                                                                                                                  h ^
                                                                                                                                                                    6 +
                                                                                                                                                              2856 *
                                                                                                                                                                s ^
                                                                                                                                                                  4 +
                                                                                                                                                            11664 *
                                                                                                                                                                s ^
                                                                                                                                                                  4 *
                                                                                                                                                              h ^
                                                                                                                                                                2 +
                                                                                                                                                          8100 *
                                                                                                                                                              s ^
                                                                                                                                                                4 *
                                                                                                                                                            h ^
                                                                                                                                                              4 +
                                                                                                                                                        1200 *
                                                                                                                                                            s ^
                                                                                                                                                              4 *
                                                                                                                                                          h ^
                                                                                                                                                            6 +
                                                                                                                                                      36 *
                                                                                                                                                          s ^
                                                                                                                                                            4 *
                                                                                                                                                        h ^
                                                                                                                                                          8 +
                                                                                                                                                    11664 *
                                                                                                                                                        s ^
                                                                                                                                                          4 *
                                                                                                                                                      g ^
                                                                                                                                                        2 +
                                                                                                                                                  75600 *
                                                                                                                                                        s ^
                                                                                                                                                          4 *
                                                                                                                                                      g ^
                                                                                                                                                        2 *
                                                                                                                                                    h ^
                                                                                                                                                      2 +
                                                                                                                                                54000 *
                                                                                                                                                      s ^
                                                                                                                                                        4 *
                                                                                                                                                    g ^
                                                                                                                                                      2 *
                                                                                                                                                  h ^
                                                                                                                                                    4 +
                                                                                                                                              6336 *
                                                                                                                                                    s ^
                                                                                                                                                      4 *
                                                                                                                                                  g ^
                                                                                                                                                    2 *
                                                                                                                                                h ^
                                                                                                                                                  6 +
                                                                                                                                            144 *
                                                                                                                                                  s ^
                                                                                                                                                    4 *
                                                                                                                                                g ^
                                                                                                                                                  2 *
                                                                                                                                              h ^
                                                                                                                                                8 +
                                                                                                                                          8100 *
                                                                                                                                              s ^
                                                                                                                                                4 *
                                                                                                                                            g ^
                                                                                                                                              4 +
                                                                                                                                        54000 *
                                                                                                                                              s ^
                                                                                                                                                4 *
                                                                                                                                            g ^
                                                                                                                                              4 *
                                                                                                                                          h ^
                                                                                                                                            2 +
                                                                                                                                      42336 *
                                                                                                                                            s ^
                                                                                                                                              4 *
                                                                                                                                          g ^
                                                                                                                                            4 *
                                                                                                                                        h ^
                                                                                                                                          4 +
                                                                                                                                    3744 *
                                                                                                                                          s ^
                                                                                                                                            4 *
                                                                                                                                        g ^
                                                                                                                                          4 *
                                                                                                                                      h ^
                                                                                                                                        6 +
                                                                                                                                  36 *
                                                                                                                                        s ^
                                                                                                                                          4 *
                                                                                                                                      g ^
                                                                                                                                        4 *
                                                                                                                                    h ^
                                                                                                                                      8 +
                                                                                                                                1200 *
                                                                                                                                    s ^
                                                                                                                                      4 *
                                                                                                                                  g ^
                                                                                                                                    6 +
                                                                                                                              6336 *
                                                                                                                                    s ^
                                                                                                                                      4 *
                                                                                                                                  g ^
                                                                                                                                    6 *
                                                                                                                                h ^
                                                                                                                                  2 +
                                                                                                                            3744 *
                                                                                                                                  s ^
                                                                                                                                    4 *
                                                                                                                                g ^
                                                                                                                                  6 *
                                                                                                                              h ^
                                                                                                                                4 +
                                                                                                                          336 *
                                                                                                                                s ^
                                                                                                                                  4 *
                                                                                                                              g ^
                                                                                                                                6 *
                                                                                                                            h ^
                                                                                                                              6 +
                                                                                                                        36 *
                                                                                                                            s ^
                                                                                                                              4 *
                                                                                                                          g ^
                                                                                                                            8 +
                                                                                                                      144 *
                                                                                                                            s ^
                                                                                                                              4 *
                                                                                                                          g ^
                                                                                                                            8 *
                                                                                                                        h ^
                                                                                                                          2 +
                                                                                                                    36 *
                                                                                                                          s ^
                                                                                                                            4 *
                                                                                                                        g ^
                                                                                                                          8 *
                                                                                                                      h ^
                                                                                                                        4 +
                                                                                                                  9984 *
                                                                                                                    s ^
                                                                                                                      6 +
                                                                                                                29600 *
                                                                                                                    s ^
                                                                                                                      6 *
                                                                                                                  h ^
                                                                                                                    2 +
                                                                                                              14400 *
                                                                                                                  s ^
                                                                                                                    6 *
                                                                                                                h ^ 4 +
                                                                                                            1200 *
                                                                                                                s ^ 6 *
                                                                                                              h ^ 6 +
                                                                                                          16 * s ^ 6 *
                                                                                                            h ^ 8 +
                                                                                                        29600 * s ^ 6 *
                                                                                                          g ^ 2 +
                                                                                                      118400 * s ^ 6 *
                                                                                                          g ^ 2 *
                                                                                                        h ^ 2 +
                                                                                                    54000 * s ^ 6 *
                                                                                                        g ^ 2 *
                                                                                                      h ^ 4 +
                                                                                                  3616 * s ^ 6 * g ^ 2 *
                                                                                                    h ^ 6 +
                                                                                                16 * s ^ 6 * g ^ 2 *
                                                                                                  h ^ 8 +
                                                                                              14400 * s ^ 6 * g ^ 4 +
                                                                                            54000 * s ^ 6 * g ^ 4 *
                                                                                              h ^ 2 +
                                                                                          16416 * s ^ 6 * g ^ 4 *
                                                                                            h ^ 4 +
                                                                                        816 * s ^ 6 * g ^ 4 * h ^ 6 +
                                                                                      1200 * s ^ 6 * g ^ 6 +
                                                                                    3616 * s ^ 6 * g ^ 6 * h ^ 2 +
                                                                                  816 * s ^ 6 * g ^ 6 * h ^ 4 +
                                                                                16 * s ^ 6 * g ^ 8 +
                                                                              16 * s ^ 6 * g ^ 8 * h ^ 2 +
                                                                            15650 * s ^ 8 +
                                                                          29600 * s ^ 8 * h ^ 2 +
                                                                        8100 * s ^ 8 * h ^ 4 +
                                                                      400 * s ^ 8 * h ^ 6 +
                                                                    1 * s ^ 8 * h ^ 8 +
                                                                  29600 * s ^ 8 * g ^ 2 +
                                                                75600 * s ^ 8 * g ^ 2 * h ^ 2 +
                                                              14400 * s ^ 8 * g ^ 2 * h ^ 4 +
                                                            376 * s ^ 8 * g ^ 2 * h ^ 6 +
                                                          8100 * s ^ 8 * g ^ 4 +
                                                        14400 * s ^ 8 * g ^ 4 * h ^ 2 +
                                                      2376 * s ^ 8 * g ^ 4 * h ^ 4 +
                                                    400 * s ^ 8 * g ^ 6 +
                                                  376 * s ^ 8 * g ^ 6 * h ^ 2 +
                                                1 * s ^ 8 * g ^ 8 +
                                              9984 * s ^ 10 +
                                            11664 * s ^ 10 * h ^ 2 +
                                          1584 * s ^ 10 * h ^ 4 +
                                        24 * s ^ 10 * h ^ 6 +
                                      11664 * s ^ 10 * g ^ 2 +
                                    12384 * s ^ 10 * g ^ 2 * h ^ 2 +
                                  1224 * s ^ 10 * g ^ 2 * h ^ 4 +
                                1584 * s ^ 10 * g ^ 4 +
                              1224 * s ^ 10 * g ^ 4 * h ^ 2 +
                            24 * s ^ 10 * g ^ 6 +
                          2856 * s ^ 12 +
                        1456 * s ^ 12 * h ^ 2 +
                      84 * s ^ 12 * h ^ 4 +
                    1456 * s ^ 12 * g ^ 2 +
                  784 * s ^ 12 * g ^ 2 * h ^ 2 +
                84 * s ^ 12 * g ^ 4 +
              256 * s ^ 14 +
            64 * s ^ 14 * h ^ 2 +
          64 * s ^ 14 * g ^ 2 +
        9 * s ^ 16)
```

### PaperI.originalCubicQuintic_g_ratio_improves

```lean
PaperI.originalCubicQuintic_g_ratio_improves {s g h : ℝ} (hs : s ≠ 0) (hh : h ^ 2 < g ^ 2) :
  PaperI.originalCubicQuinticNormSq s h * PaperI.originalCubicQuinticMinEnergy s g <
    PaperI.originalCubicQuinticNormSq s g * PaperI.originalCubicQuinticMinEnergy s h
```

### PaperI.originalCubicQuintic_g_ratio_improvement

```lean
PaperI.originalCubicQuintic_g_ratio_improvement {s g A : ℝ} (hs : s ≠ 0) (hg : g ≠ 0)
  (he : PaperI.originalCubicQuinticNormSq s g = A ^ 4 * PaperI.originalCubicQuinticMinEnergy s g) :
  ∃ᶠ (b : ℝ) in nhds 1,
    0 < b ∧ b < 1 ∧ PaperI.originalCubicQuinticNormSq s (b * g) < A ^ 4 * PaperI.originalCubicQuinticMinEnergy s (b * g)
```

### PaperI.originalCubicQuinticState

```lean
PaperI.originalCubicQuinticState (k : ℕ) (s g : ℝ) (hk : (if g = 0 then 2 else 3) * 5 ≤ k) : PaperI.AugmentedState k
```

### PaperI.originalCubicQuinticState_polynomial

```lean
PaperI.originalCubicQuinticState_polynomial (k : ℕ) (s g : ℝ) (hk : (if g = 0 then 2 else 3) * 5 ≤ k) :
  PaperI.coefficientPolynomial (PaperI.originalCubicQuinticState k s g hk).1 =
    PaperI.originalCenteredCubicInvariant s g ^ 5
```

### PaperI.originalCubicQuinticState_profile

```lean
PaperI.originalCubicQuinticState_profile (k : ℕ) (s g : ℝ) (hk : (if g = 0 then 2 else 3) * 5 ≤ k) :
  PaperI.coefficientPolynomial (PaperI.originalCubicQuinticState k s g hk).1 =
    Polynomial.eval₂ MvPolynomial.C (PaperI.originalCenteredCubicInvariant s g) (Polynomial.X ^ 5) -
      MvPolynomial.C ((Polynomial.X ^ 5).coeff 0)
```

### PaperI.originalCubicQuinticState_rank

```lean
PaperI.originalCubicQuinticState_rank (k : ℕ) {s : ℝ} (hs : s ≠ 0) (g : ℝ) (hk : (if g = 0 then 2 else 3) * 5 ≤ k) :
  (PaperI.augmentedOrbitMatrix k (PaperI.originalCubicQuinticState k s g hk)).rank = 4
```

### PaperI.originalCubicQuinticState_norm_sq

```lean
PaperI.originalCubicQuinticState_norm_sq (k : ℕ) (s g : ℝ) (hk : (if g = 0 then 2 else 3) * 5 ≤ k) :
  PaperI.augmentedStateNorm (PaperI.originalCubicQuinticState k s g hk) ^ 2 = PaperI.originalCubicQuinticNormSq s g
```

### PaperI.originalCubicQuinticState_x_energy

```lean
PaperI.originalCubicQuinticState_x_energy (k : ℕ) (s g : ℝ) (hk : (if g = 0 then 2 else 3) * 5 ≤ k) :
  PaperI.coefficientEuclideanNorm
        ((PaperI.directionalCoefficientMap k (Pi.single 0 1)) (PaperI.originalCubicQuinticState k s g hk).1) ^
      2 =
    25 *
      (1 + 16 * g ^ 2 + 36 * g ^ 4 + 16 * g ^ 6 + g ^ 8 + 16 * s ^ 2 + 144 * s ^ 2 * g ^ 2 + 144 * s ^ 2 * g ^ 4 +
                    16 * s ^ 2 * g ^ 6 +
                  36 * s ^ 4 +
                144 * s ^ 4 * g ^ 2 +
              36 * s ^ 4 * g ^ 4 +
            16 * s ^ 6 +
          16 * s ^ 6 * g ^ 2 +
        s ^ 8)
```

### PaperI.originalCubicQuinticState_translation_lower

```lean
PaperI.originalCubicQuinticState_translation_lower (k : ℕ) (s g : ℝ) (hk : (if g = 0 then 2 else 3) * 5 ≤ k)
  (h : PaperI.PhysicalSpace) :
  PaperI.originalCubicQuinticMinEnergy s g * PaperI.physicalEuclideanNorm h ^ 2 ≤
    PaperI.augmentedStateNorm
        ((PaperI.augmentedOrbitDifferential k (PaperI.originalCubicQuinticState k s g hk))
          (PaperI.upperAffineTranslationCoordinates h)) ^
      2
```

### PaperI.originalCubicQuinticState_translation_attained

```lean
PaperI.originalCubicQuinticState_translation_attained (k : ℕ) (s g : ℝ) (hk : (if g = 0 then 2 else 3) * 5 ≤ k) :
  ∃ (h : PaperI.PhysicalSpace),
    PaperI.physicalEuclideanNorm h = 1 ∧
      PaperI.augmentedStateNorm
            ((PaperI.augmentedOrbitDifferential k (PaperI.originalCubicQuinticState k s g hk))
              (PaperI.upperAffineTranslationCoordinates h)) ^
          2 =
        PaperI.originalCubicQuinticMinEnergy s g
```

### PaperI.original_centered_quintic_expansion

```lean
PaperI.original_centered_quintic_expansion (s g : ℝ) :
  PaperI.originalCenteredCubicInvariant s g ^ 5 =
    MvPolynomial.X 0 ^ 5 + MvPolynomial.C (5 * g) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 2 ^ 3) +
                                          MvPolynomial.C (10 * g ^ 2) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 2 ^ 6) +
                                        MvPolynomial.C (10 * g ^ 3) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 ^ 9) +
                                      MvPolynomial.C (5 * g ^ 4) * (MvPolynomial.X 0 * MvPolynomial.X 2 ^ 12) +
                                    MvPolynomial.C (g ^ 5) * MvPolynomial.X 2 ^ 15 -
                                  MvPolynomial.C (5 * s) *
                                    (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 * MvPolynomial.X 2) -
                                MvPolynomial.C (20 * s * g) *
                                  (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 4) -
                              MvPolynomial.C (30 * s * g ^ 2) *
                                (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 7) -
                            MvPolynomial.C (20 * s * g ^ 3) *
                              (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 10) -
                          MvPolynomial.C (5 * s * g ^ 4) * (MvPolynomial.X 1 * MvPolynomial.X 2 ^ 13) +
                        MvPolynomial.C (10 * s ^ 2) *
                          (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 ^ 2) +
                      MvPolynomial.C (30 * s ^ 2 * g) *
                        (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 ^ 5) +
                    MvPolynomial.C (30 * s ^ 2 * g ^ 2) *
                      (MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 ^ 8) +
                  MvPolynomial.C (10 * s ^ 2 * g ^ 3) * (MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 ^ 11) -
                MvPolynomial.C (10 * s ^ 3) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 3 * MvPolynomial.X 2 ^ 3) -
              MvPolynomial.C (20 * s ^ 3 * g) * (MvPolynomial.X 0 * MvPolynomial.X 1 ^ 3 * MvPolynomial.X 2 ^ 6) -
            MvPolynomial.C (10 * s ^ 3 * g ^ 2) * (MvPolynomial.X 1 ^ 3 * MvPolynomial.X 2 ^ 9) +
          MvPolynomial.C (5 * s ^ 4) * (MvPolynomial.X 0 * MvPolynomial.X 1 ^ 4 * MvPolynomial.X 2 ^ 4) +
        MvPolynomial.C (5 * s ^ 4 * g) * (MvPolynomial.X 1 ^ 4 * MvPolynomial.X 2 ^ 7) -
      MvPolynomial.C (s ^ 5) * (MvPolynomial.X 1 ^ 5 * MvPolynomial.X 2 ^ 5)
```

### PaperI.originalCubicQuinticState_continuous

```lean
PaperI.originalCubicQuinticState_continuous (k : ℕ) (s g : ℝ → ℝ) (hs : Continuous s) (hg : Continuous g)
  (hk : ∀ (t : ℝ), (if g t = 0 then 2 else 3) * 5 ≤ k) :
  Continuous fun (t : ℝ) => PaperI.originalCubicQuinticState k (s t) (g t) ⋯
```

### PaperI.originalCubicQuintic_scaled_g_cap

```lean
PaperI.originalCubicQuintic_scaled_g_cap {k : ℕ} (g : ℝ) (hk : (if g = 0 then 2 else 3) * 5 ≤ k) (t : ℝ) :
  (if t * g = 0 then 2 else 3) * 5 ≤ k
```

### PaperI.original_scaledCubicQuintic_norm_sq

```lean
PaperI.original_scaledCubicQuintic_norm_sq (k : ℕ) (s g c : ℝ) (hk : (if g = 0 then 2 else 3) * 5 ≤ k) :
  PaperI.augmentedStateNorm (c • PaperI.originalCubicQuinticState k s g hk) ^ 2 =
    c ^ 2 * PaperI.originalCubicQuinticNormSq s g
```

### PaperI.original_scaledCubicQuintic_norm_pos

```lean
PaperI.original_scaledCubicQuintic_norm_pos (k : ℕ) (s g c : ℝ) (hk : (if g = 0 then 2 else 3) * 5 ≤ k) (hc : c ≠ 0) :
  0 < PaperI.augmentedStateNorm (c • PaperI.originalCubicQuinticState k s g hk)
```

### PaperI.original_scaledCubicQuintic_translation_lower

```lean
PaperI.original_scaledCubicQuintic_translation_lower (k : ℕ) (s g c : ℝ) (hk : (if g = 0 then 2 else 3) * 5 ≤ k)
  (h : PaperI.PhysicalSpace) :
  c ^ 2 * PaperI.originalCubicQuinticMinEnergy s g * PaperI.physicalEuclideanNorm h ^ 2 ≤
    PaperI.augmentedStateNorm
        ((PaperI.augmentedOrbitDifferential k (c • PaperI.originalCubicQuinticState k s g hk))
          (PaperI.upperAffineTranslationCoordinates h)) ^
      2
```

### PaperI.original_scaledCubicQuintic_translation_attained

```lean
PaperI.original_scaledCubicQuintic_translation_attained (k : ℕ) (s g c : ℝ) (hk : (if g = 0 then 2 else 3) * 5 ≤ k) :
  ∃ (h : PaperI.PhysicalSpace),
    PaperI.physicalEuclideanNorm h = 1 ∧
      PaperI.augmentedStateNorm
            ((PaperI.augmentedOrbitDifferential k (c • PaperI.originalCubicQuinticState k s g hk))
              (PaperI.upperAffineTranslationCoordinates h)) ^
          2 =
        c ^ 2 * PaperI.originalCubicQuinticMinEnergy s g
```

### PaperI.original_scaledCubicQuintic_far_closure_ratio

```lean
PaperI.original_scaledCubicQuintic_far_closure_ratio {k N : ℕ} {A B s : ℝ} (hs : s ≠ 0) (g c : ℝ) (hc : c ≠ 0)
  (hk : (if g = 0 then 2 else 3) * 5 ≤ k) (hA : 2 ≤ A)
  (ht : PaperI.AugmentedTranslationStopped A (c • PaperI.originalCubicQuinticState k s g hk))
  (hcl : (A, c • PaperI.originalCubicQuinticState k s g hk) ∈ closure (PaperI.originalFarBoundedFamily k N B)) :
  PaperI.augmentedStateNorm (c • PaperI.originalCubicQuinticState k s g hk) = A ∧
    PaperI.originalCubicQuinticNormSq s g = A ^ 4 * PaperI.originalCubicQuinticMinEnergy s g
```

### PaperI.original_scaledCubicQuintic_not_mem_far_closure

```lean
PaperI.original_scaledCubicQuintic_not_mem_far_closure {k N : ℕ} {A B s : ℝ} (hs : s ≠ 0) (g c : ℝ) (hc : c ≠ 0)
  (hk : (if g = 0 then 2 else 3) * 5 ≤ k) (hA : 2 ≤ A)
  (ht : PaperI.AugmentedTranslationStopped A (c • PaperI.originalCubicQuinticState k s g hk)) :
  (A, c • PaperI.originalCubicQuinticState k s g hk) ∉ closure (PaperI.originalFarBoundedFamily k N B)
```

### PaperI.original_centered_quintic_state_eq

```lean
PaperI.original_centered_quintic_state_eq {k : ℕ} (F : PaperI.CoefficientSpace k) (s g c : ℝ)
  (hk : (if g = 0 then 2 else 3) * 5 ≤ k)
  (hF : PaperI.coefficientPolynomial F = MvPolynomial.C c * PaperI.originalCenteredCubicInvariant s g ^ 5) :
  (F, 0) = c • PaperI.originalCubicQuinticState k s g hk
```

### PaperI.original_centered_quintic_not_mem_far_closure

```lean
PaperI.original_centered_quintic_not_mem_far_closure {k N : ℕ} (F : PaperI.CoefficientSpace k) {s : ℝ} (hs : s ≠ 0)
  (g c : ℝ) (hc : c ≠ 0) (hk : (if g = 0 then 2 else 3) * 5 ≤ k)
  (hF : PaperI.coefficientPolynomial F = MvPolynomial.C c * PaperI.originalCenteredCubicInvariant s g ^ 5) {A B : ℝ}
  (hA : 2 ≤ A) (ht : PaperI.AugmentedTranslationStopped A (F, 0)) :
  (A, F, 0) ∉ closure (PaperI.originalFarBoundedFamily k N B)
```

### PaperI.original_centered_far_closure_quintic_zero

```lean
PaperI.original_centered_far_closure_quintic_zero {k N : ℕ} (F : PaperI.CoefficientSpace k) {s : ℝ} (hs : s ≠ 0) (g : ℝ)
  (f : Polynomial ℝ) (hf : 2 ≤ f.natDegree) (hcap : (if g = 0 then 2 else 3) * f.natDegree ≤ k)
  (hF :
    PaperI.coefficientPolynomial F =
      Polynomial.eval₂ MvPolynomial.C (PaperI.originalCenteredCubicInvariant s g) f - MvPolynomial.C (f.coeff 0))
  {A B : ℝ} (hA : 2 ≤ A) (ht : PaperI.AugmentedTranslationStopped A (F, 0))
  (hcl : (A, F, 0) ∈ closure (PaperI.originalFarBoundedFamily k N B)) : f.coeff 5 = 0
```

### PaperI.original_centered_far_closure_through_quintic_zero

```lean
PaperI.original_centered_far_closure_through_quintic_zero {k N : ℕ} (F : PaperI.CoefficientSpace k) {s : ℝ} (hs : s ≠ 0)
  (g : ℝ) (f : Polynomial ℝ) (hf : 2 ≤ f.natDegree) (hcap : (if g = 0 then 2 else 3) * f.natDegree ≤ k)
  (hF :
    PaperI.coefficientPolynomial F =
      Polynomial.eval₂ MvPolynomial.C (PaperI.originalCenteredCubicInvariant s g) f - MvPolynomial.C (f.coeff 0))
  {A B : ℝ} (hA : 2 ≤ A) (ht : PaperI.AugmentedTranslationStopped A (F, 0))
  (hcl : (A, F, 0) ∈ closure (PaperI.originalFarBoundedFamily k N B)) :
  f.coeff 1 = 0 ∧ f.coeff 2 = 0 ∧ f.coeff 3 = 0 ∧ f.coeff 4 = 0 ∧ f.coeff 5 = 0 ∧ 6 ≤ f.natDegree
```

## Exact remaining prerequisites

### ARG:original_Gauss_cut_continuation_162

Location: I1319-I1321/I1323. Category: Implementation difficulty: quantitative full-parent margin, cut continuation and geometric assignment assembly.

Status: Open manuscript application; previously verified scopes and complete augmented transport preserved.

For every relevant artificial cut portion sufficiently near the inner admissible set, obtain the prescribed conditioned radius and continue each original branch through that portion inside the outer full-parent admissible margin. Retain D(D-1) distinct branches, fixed-format bounded-slope arcs, endpoint squares, conditioned transverse widths and a common Borel cut/label assignment before anchors. Prove cut-rule compatibility for the overlapping chart cover. The original body and normalized third-derivative identities hold on a qualitative ambient neighborhood; uniform conditioned and full-parent admissible neighborhoods remain unproved.

Obstruction: Classification(i)-(iii), canonical parameter/profile/root bounds, exact-model centering and complete same-frame augmented transport are available. These do not supply the actual stopped-parent model choice, perturbed graph or original label/domain/packing witnesses.

Next: At I766-I781, supply the actual stopped parent and selected nearby exact rank-four model with complete augmented proximity, use the now-proved same-frame transport, and instantiate the quantitative implicit-function argument for the perturbed phase at its moved root. Preserve the polynomial radius and prescribed finite-order derivative bounds before choosing its own centering frame; do not assume that the exact-model root also zeros the perturbed phase.

### ARG:original_Gauss_same_chart_body_bounds_160

Location: I1289/I1295-I1305. Category: Implementation/application difficulty: complete-parent admissibility, original model-box/error buffer and path/atlas gluing; no mathematical gap established.

Status: Partial: exact graph and inverse-power tail verified; all-P bounded-window application and downstream geometry open.

Prove for each fixed k,N: forall B:real, exists b>0, forall P in[2,B], b<=originalRankEntryMinimum k N P. Equivalently bound sigma5 below by one b on all actual same-window far states in that parameter interval. Fixed-P positivity, a finite first-order graph and the newly proved tail do not supply this input. The perturbed parent's moved root/graph, polynomial radius and finite-order jets, own centering, original Borel labels, relative-unit cover, packing and downstream geometric/main-theorem applications remain unresolved.

Preserved parent193 application specification (its graph/tail subparts are superseded by the progress above): Fixed-P complete model proximity is now available. Supply the uniform inverse-power spectral threshold, the actual quadratic-model branch specialization and remaining application inputs: perturbed normal-root/graph construction and its own centering; selected-label anchor/domain and179 normalized quadratic data; higher correction jets/body/coframe; full-parent coefficient/physical/RQ/translation/normal-equality/model-distance margins; buffers, gluing, cuts, comparisons and original packing. Classification, exact-model roots and same-frame augmented transport remain verified. Algebraic-component and nonquadratic null-model applications remain separately open.

Obstruction: Fixed-P positivity and the exact semialgebraic graph are now checked, as is the inverse-power tail. None implies bounded-window positivity. The universal distance-from-the-varying-zero-fiber condition is not known jointly closed. The generic changing-zero-fiber diagnostic warns against that inference; finite exact tests of actual rank-four branches found no counterexample and prove no general assertion. Approach to a stop boundary from smaller P remains to be analyzed. No actual manuscript error established.

Next: Test/prove bounded-parameter separation for the actual same-P rank-four fibers, particularly approach to a stop boundary from smaller P. Do not infer joint closedness from compact fibers or silently enlarge the model window. If an actual error is established, inspect I623/I625-I638/I773 and downstream I781/I875/I897-I903/I1305 before proposing a separate minimal repair. Once this premise is proved, apply the checked all-P implication and instantiate the perturbed-parent IFT at its moved root.

### ARG:original_Gauss_actual_comparisons_packing_160

Location: I1319-I1323/I2343. Category: Unformalized manuscript application and implementation; not unavailable execution.

Status: Open manuscript application; previously verified scopes and complete augmented transport preserved.

For the same selected chart, component, strip and original label frames a_j, construct b_j=lift(assigned_point_j)=a_j*n_j with |n_j0| and |n_j5| <=P^c0 uniformly. Identify the actual complete candidate set, retain full-parent admissibility and both Hessian signs, prove intrinsic-square packing, and discharge the158 hpack/hcomponent/hrounded and initial-comparison inputs for the common Borel assignment.

Obstruction: Classification(i)-(iii), canonical parameter/profile/root bounds, exact-model centering and complete same-frame augmented transport are available. These do not supply the actual stopped-parent model choice, perturbed graph or original label/domain/packing witnesses.

Next: At I766-I781, supply the actual stopped parent and selected nearby exact rank-four model with complete augmented proximity, use the now-proved same-frame transport, and instantiate the quantitative implicit-function argument for the perturbed phase at its moved root. Preserve the polynomial radius and prescribed finite-order derivative bounds before choosing its own centering frame; do not assume that the exact-model root also zeros the perturbed phase.

### ARG:original_Gauss_algebraic_component_clause_160

Location: I1283, sentence following the cited root bound. Category: Missing algebraic-dimension formulation/application infrastructure; no demonstrated mathematical gap.

Status: Open manuscript application; previously verified scopes and complete augmented transport preserved.

Express the manuscript's positive-dimensional common-component statement in an explicit algebraic-component/dimension interface and prove that such a component cannot contain a common zero with nonzero Jacobian determinant. Record the chosen real or complex algebraic-component meaning. The already verified real local-isolation theorem remains available.

Obstruction: Real local isolation at a nonzero Jacobian determinant is already proved. The manuscript algebraic-component/dimension statement still needs a precise real or complex component interface and its application; augmented transport does not discharge it.

Next: Specify the manuscript algebraic-component/dimension interface and connect positive-dimensional membership to the existing local-isolation theorem, retaining the intended base field.

### ARG:original_Gauss_model_perturbation_170

Location: I1305, Gauss application of I875/I897-I903. Category: Implementation/manuscript-application difficulty; no new mathematical gap or unavailable execution established..

Status: Partial: exact graph and inverse-power tail verified; all-P bounded-window application and downstream geometry open.

Prove for each fixed k,N: forall B:real, exists b>0, forall P in[2,B], b<=originalRankEntryMinimum k N P. Equivalently bound sigma5 below by one b on all actual same-window far states in that parameter interval. Fixed-P positivity, a finite first-order graph and the newly proved tail do not supply this input. The perturbed parent's moved root/graph, polynomial radius and finite-order jets, own centering, original Borel labels, relative-unit cover, packing and downstream geometric/main-theorem applications remain unresolved.

Preserved parent193 application specification (its graph/tail subparts are superseded by the progress above): Fixed-P complete model proximity is now available. Supply the uniform inverse-power spectral threshold, the actual quadratic-model branch specialization and remaining application inputs: perturbed normal-root/graph construction and its own centering; selected-label anchor/domain and179 normalized quadratic data; higher correction jets/body/coframe; full-parent coefficient/physical/RQ/translation/normal-equality/model-distance margins; buffers, gluing, cuts, comparisons and original packing. Classification, exact-model roots and same-frame augmented transport remain verified. Algebraic-component and nonquadratic null-model applications remain separately open.

Obstruction: Fixed-P positivity and the exact semialgebraic graph are now checked, as is the inverse-power tail. None implies bounded-window positivity. The universal distance-from-the-varying-zero-fiber condition is not known jointly closed. The generic changing-zero-fiber diagnostic warns against that inference; finite exact tests of actual rank-four branches found no counterexample and prove no general assertion. Approach to a stop boundary from smaller P remains to be analyzed. No actual manuscript error established.

Next: Test/prove bounded-parameter separation for the actual same-P rank-four fibers, particularly approach to a stop boundary from smaller P. Do not infer joint closedness from compact fibers or silently enlarge the model window. If an actual error is established, inspect I623/I625-I638/I773 and downstream I781/I875/I897-I903/I1305 before proposing a separate minimal repair. Once this premise is proved, apply the checked all-P implication and instantiate the perturbed-parent IFT at its moved root.

### ARG:original_Gauss_full_parent_admissibility_170

Location: I845-I859/I903/I1305. Category: Implementation/manuscript-application difficulty; no new mathematical gap or unavailable execution established..

Status: Partial: exact graph and inverse-power tail verified; all-P bounded-window application and downstream geometry open.

Prove for each fixed k,N: forall B:real, exists b>0, forall P in[2,B], b<=originalRankEntryMinimum k N P. Equivalently bound sigma5 below by one b on all actual same-window far states in that parameter interval. Fixed-P positivity, a finite first-order graph and the newly proved tail do not supply this input. The perturbed parent's moved root/graph, polynomial radius and finite-order jets, own centering, original Borel labels, relative-unit cover, packing and downstream geometric/main-theorem applications remain unresolved.

Preserved parent193 application specification (its graph/tail subparts are superseded by the progress above): Fixed-P complete model proximity is now available. Supply the uniform inverse-power spectral threshold, the actual quadratic-model branch specialization and remaining application inputs: perturbed normal-root/graph construction and its own centering; selected-label anchor/domain and179 normalized quadratic data; higher correction jets/body/coframe; full-parent coefficient/physical/RQ/translation/normal-equality/model-distance margins; buffers, gluing, cuts, comparisons and original packing. Classification, exact-model roots and same-frame augmented transport remain verified. Algebraic-component and nonquadratic null-model applications remain separately open.

Obstruction: Fixed-P positivity and the exact semialgebraic graph are now checked, as is the inverse-power tail. None implies bounded-window positivity. The universal distance-from-the-varying-zero-fiber condition is not known jointly closed. The generic changing-zero-fiber diagnostic warns against that inference; finite exact tests of actual rank-four branches found no counterexample and prove no general assertion. Approach to a stop boundary from smaller P remains to be analyzed. No actual manuscript error established.

Next: Test/prove bounded-parameter separation for the actual same-P rank-four fibers, particularly approach to a stop boundary from smaller P. Do not infer joint closedness from compact fibers or silently enlarge the model window. If an actual error is established, inspect I623/I625-I638/I773 and downstream I781/I875/I897-I903/I1305 before proposing a separate minimal repair. Once this premise is proved, apply the checked all-P implication and instantiate the perturbed-parent IFT at its moved root.

### ARG:original_profile_polynomial_bound_180

Location: I695-I729; I773-I781. Category: Implementation/manuscript-application difficulty; no new mathematical gap, missing execution or disproved statement established..

Status: Partial original argument:211 excludes pure quintics and derives vanishing of coefficients1 through5 for centered far-closure profiles. Degree>=6 profiles, general boundary cases, hwindow and the main theorem remain unresolved.

Prove for each fixed k,N: forall B:real, exists b>0, forall P in[2,B], b<=originalRankEntryMinimum k N P. Equivalently bound sigma5 below by one b on all actual same-window far states in that parameter interval. Fixed-P positivity, a finite first-order graph and the newly proved tail do not supply this input. The perturbed parent's moved root/graph, polynomial radius and finite-order jets, own centering, original Borel labels, relative-unit cover, packing and downstream geometric/main-theorem applications remain unresolved.

Preserved parent193 application specification (its graph/tail subparts are superseded by the progress above): I773 still requires the uniform inverse-power fifth-singular-value threshold: for every fixed k and L>=1, one C_L>0 before every P>=2 and stopped parent. Fixed-P separation alone is not this result. The bounded-parameter positivity premise for the actual distance-separated family and its fixed-format minimum graph must be supplied to the existing conditioning theorem; rank-four fibers may be empty. I781 still requires a moved root and graph of the perturbed parent with radius>=P^(-C) and finite-order derivative bounds<=P^C, its own centering shears, first-permissible order/root/branch Borel labels, finite relative-unit covering and original-label packing. Other Gauss/full-parent/component/nonquadratic null-model and main-theorem applications remain open.

Current remaining portion: 
Checkpoint211 remaining centered case: for every natural k,N, real B,A>=2,s!=0,g, original coefficient representative F=f(x-s*y*z+g*z^3)-C(a_0), original full-profile cap (if g=0 then2else3)*natDegree(f)<=k and complete all-direction A-stop, exclude (A,(F,0)) from closure(originalFarBoundedFamily k N B) when a_1=a_2=a_3=a_4=a_5=0 and natDegree(f)>=6. All higher coefficients and inherited active-index balance are retained. General affine/mixed-curvature states are separate. Uniform hwindow still requires, for each fixed k,N,B, one b>0 with b<=originalRankEntryMinimum k N P for every real P in[2,B].

Inherited exact goal specification, not a completed proof:

```lean
Prose specification: uniform I773 threshold as in ARG:original_uniform_rank_entry_threshold_193; then a root and graph for the actual perturbed parent with radius>=P^(-C), every fixed finite-order derivative<=P^C, its own normal translation/shears, original Borel labelled cover and packing. The exact model sheet of the193 theorem is not this parent sheet.
```

Obstruction: The pure-quintic obstruction has been discharged by actual coefficient-state deformations and complete translation-energy bounds. Comparisons and shape exclusion for arbitrary profiles supported in degrees>=6 are still unproved. The scalar simultaneous-saturation and affine-centering obstructions, and the explicit mixed-profile contraction counterexample, still prevent unqualified extension. No actual-family counterexample to hwindow has been established. I625 explicitly assumes closed total bounded windows; that assumption is not itself a flaw.

Next: Before a further proof strategy, test the sixth-versus-higher comparison 36*N_5*N_n < n^2*N_6*N_(n-1) for n>=7, using the actual original norms. Check n=7,8,9,10 separately and the possible N_6>=N_1*N_5 plus n>=11 bound n^2>108. Include zero parameters, both signs, all-direction energies and the saved mixed-profile counterexample. If proved, apply inherited active-index balance to isolate an active sixth coefficient; a pure-sixth exclusion remains a separate task. None of these new comparisons is asserted proved here.

### ARG:original_uniform_rank_entry_threshold_193

Location: I773, sentence invoking Lemma geo:conditioning; downstream I766-I781 and Gauss model applications. Category: Implementation/applicability difficulty: bounded-window conditioning remains unformalized; graph and large-P threshold are proved. No mathematical gap established; execution available..

Status: Partial original argument:211 excludes pure quintics and derives vanishing of coefficients1 through5 for centered far-closure profiles. Degree>=6 profiles, general boundary cases, hwindow and the main theorem remain unresolved.

All-P uniform threshold remains open solely at its bounded-window conditioning input: For every fixed k,N:natural, forall B:real, exists b:real, 0<b and forall P:real, 2<=P -> P<=B -> b<=PaperI.originalRankEntryMinimum k N P. Equivalently (by the new checked iff), the same b bounds sigma5(S) below for every stopped S at each P in[2,B] with forall same-P stopped rank-four T, P^(-N)<=augmentedStateNorm(S-T). The graph and large-P threshold are now proved. The checked all-P implication requires this hwindow explicitly.

Current remaining portion: 
Checkpoint211 remaining centered case: for every natural k,N, real B,A>=2,s!=0,g, original coefficient representative F=f(x-s*y*z+g*z^3)-C(a_0), original full-profile cap (if g=0 then2else3)*natDegree(f)<=k and complete all-direction A-stop, exclude (A,(F,0)) from closure(originalFarBoundedFamily k N B) when a_1=a_2=a_3=a_4=a_5=0 and natDegree(f)>=6. All higher coefficients and inherited active-index balance are retained. General affine/mixed-curvature states are separate. Uniform hwindow still requires, for each fixed k,N,B, one b>0 with b<=originalRankEntryMinimum k N P for every real P in[2,B].

Inherited exact goal specification, not a completed proof:

```lean
hwindow : ∀ B : ℝ, ∃ b : ℝ, 0 < b ∧ ∀ P : ℝ, 2 ≤ P → P ≤ B → b ≤ PaperI.originalRankEntryMinimum k N P
```

Obstruction: The pure-quintic obstruction has been discharged by actual coefficient-state deformations and complete translation-energy bounds. Comparisons and shape exclusion for arbitrary profiles supported in degrees>=6 are still unproved. The scalar simultaneous-saturation and affine-centering obstructions, and the explicit mixed-profile contraction counterexample, still prevent unqualified extension. No actual-family counterexample to hwindow has been established. I625 explicitly assumes closed total bounded windows; that assumption is not itself a flaw.

Next: Before a further proof strategy, test the sixth-versus-higher comparison 36*N_5*N_n < n^2*N_6*N_(n-1) for n>=7, using the actual original norms. Check n=7,8,9,10 separately and the possible N_6>=N_1*N_5 plus n>=11 bound n^2>108. Include zero parameters, both signs, all-direction energies and the saved mixed-profile counterexample. If proved, apply inherited active-index balance to isolate an active sixth coefficient; a pure-sixth exclusion remains a separate task. None of these new comparisons is asserted proved here.

### ARG:original_rank_entry_bounded_window_194

Location: I625-I638 applicability at I773; downstream I781/I875/I897-I903/I1305. Category: Implementation/applicability difficulty: actual bounded-window lower estimate unformalized; no mathematical gap established..

Status: Partial original argument:211 excludes pure quintics and derives vanishing of coefficients1 through5 for centered far-closure profiles. Degree>=6 profiles, general boundary cases, hwindow and the main theorem remain unresolved.

For every fixed k,N:natural, forall B:real, exists b:real, 0<b and forall P:real, 2<=P -> P<=B -> b<=PaperI.originalRankEntryMinimum k N P. Equivalently (by the new checked iff), the same b bounds sigma5(S) below for every stopped S at each P in[2,B] with forall same-P stopped rank-four T, P^(-N)<=augmentedStateNorm(S-T).

Current remaining portion: 
Checkpoint211 remaining centered case: for every natural k,N, real B,A>=2,s!=0,g, original coefficient representative F=f(x-s*y*z+g*z^3)-C(a_0), original full-profile cap (if g=0 then2else3)*natDegree(f)<=k and complete all-direction A-stop, exclude (A,(F,0)) from closure(originalFarBoundedFamily k N B) when a_1=a_2=a_3=a_4=a_5=0 and natDegree(f)>=6. All higher coefficients and inherited active-index balance are retained. General affine/mixed-curvature states are separate. Uniform hwindow still requires, for each fixed k,N,B, one b>0 with b<=originalRankEntryMinimum k N P for every real P in[2,B].

Inherited exact goal specification, not a completed proof:

```lean
hwindow : ∀ B : ℝ, ∃ b : ℝ, 0 < b ∧ ∀ P : ℝ, 2 ≤ P → P ≤ B → b ≤ PaperI.originalRankEntryMinimum k N P
```

Obstruction: The pure-quintic obstruction has been discharged by actual coefficient-state deformations and complete translation-energy bounds. Comparisons and shape exclusion for arbitrary profiles supported in degrees>=6 are still unproved. The scalar simultaneous-saturation and affine-centering obstructions, and the explicit mixed-profile contraction counterexample, still prevent unqualified extension. No actual-family counterexample to hwindow has been established. I625 explicitly assumes closed total bounded windows; that assumption is not itself a flaw.

Next: Before a further proof strategy, test the sixth-versus-higher comparison 36*N_5*N_n < n^2*N_6*N_(n-1) for n>=7, using the actual original norms. Check n=7,8,9,10 separately and the possible N_6>=N_1*N_5 plus n>=11 bound n^2>108. Include zero parameters, both signs, all-direction energies and the saved mixed-profile counterexample. If proved, apply inherited active-index balance to isolate an active sixth coefficient; a pure-sixth exclusion remains a separate task. None of these new comparisons is asserted proved here.

### ARG:original_rank_entry_norm_saturated_left_boundary_195

Location: I603-I607; I625-I638 applicability at I773; downstream I781/I875/I897-I903/I1305. Category: Implementation/manuscript-applicability difficulty; no mathematical gap established. Execution and local compactness infrastructure available..

Status: Partial original argument:211 excludes pure quintics and derives vanishing of coefficients1 through5 for centered far-closure profiles. Degree>=6 profiles, general boundary cases, hwindow and the main theorem remain unresolved.

For fixed k,N and all real B,A and augmented T, if2<A<=B, T is A-stopped, rank(R_T)=4 and ||T||aug=A, then(A,T) is NOT in the closure of{(P,S):2<=P<=B, S is in the actual same-P far family at distance P^(-N), and P<A}. This sufficient boundary exclusion would contradict the newly proved necessary condition for failure and close the unchanged hwindow.

Current remaining portion: 
Checkpoint211 remaining centered case: for every natural k,N, real B,A>=2,s!=0,g, original coefficient representative F=f(x-s*y*z+g*z^3)-C(a_0), original full-profile cap (if g=0 then2else3)*natDegree(f)<=k and complete all-direction A-stop, exclude (A,(F,0)) from closure(originalFarBoundedFamily k N B) when a_1=a_2=a_3=a_4=a_5=0 and natDegree(f)>=6. All higher coefficients and inherited active-index balance are retained. General affine/mixed-curvature states are separate. Uniform hwindow still requires, for each fixed k,N,B, one b>0 with b<=originalRankEntryMinimum k N P for every real P in[2,B].

Inherited exact goal specification, not a completed proof:

```lean
∀ B A : ℝ, ∀ T : PaperI.AugmentedState k, 2 < A → A ≤ B → PaperI.AugmentedTranslationStopped A T → (PaperI.augmentedOrbitMatrix k T).rank = 4 → PaperI.augmentedStateNorm T = A → (A,T) ∉ closure (PaperI.originalFarBoundedFamily k N B ∩ {z | z.1 < A})
```

Obstruction: The pure-quintic obstruction has been discharged by actual coefficient-state deformations and complete translation-energy bounds. Comparisons and shape exclusion for arbitrary profiles supported in degrees>=6 are still unproved. The scalar simultaneous-saturation and affine-centering obstructions, and the explicit mixed-profile contraction counterexample, still prevent unqualified extension. No actual-family counterexample to hwindow has been established. I625 explicitly assumes closed total bounded windows; that assumption is not itself a flaw.

Next: Before a further proof strategy, test the sixth-versus-higher comparison 36*N_5*N_n < n^2*N_6*N_(n-1) for n>=7, using the actual original norms. Check n=7,8,9,10 separately and the possible N_6>=N_1*N_5 plus n>=11 bound n^2>108. Include zero parameters, both signs, all-direction energies and the saved mixed-profile counterexample. If proved, apply inherited active-index balance to isolate an active sixth coefficient; a pure-sixth exclusion remains a separate task. None of these new comparisons is asserted proved here.

### ARG:original_rank_entry_simultaneously_saturated_left_boundary_196

Location: I603-I607; I625-I638 applicability at I773; downstream I781/I875/I897-I903/I1305. Category: Implementation/manuscript-applicability difficulty; no mathematical gap established. Execution and local compactness infrastructure available..

Status: Partial original argument:211 excludes pure quintics and derives vanishing of coefficients1 through5 for centered far-closure profiles. Degree>=6 profiles, general boundary cases, hwindow and the main theorem remain unresolved.

For fixed k,N and all real B,A and augmented T, if2<A<=B, T is A-stopped, rank(R_T)=4, ||T||aug=A, p=T.2.1=0 and M=T.2.2=0, and some physical unit direction h has augmented translation-orbit energy exactly A^(-2), then(A,T) is NOT in the closure of{(P,S):2<=P<=B, S is in the actual same-P far family at distance P^(-N), and P<A}. This sufficient critical-boundary exclusion is OPEN. Combined with the proved necessary condition for bounded-window failure, it would close the unchanged hwindow. No such exclusion is assumed in any completed proof.

Current remaining portion: 
Checkpoint211 remaining centered case: for every natural k,N, real B,A>=2,s!=0,g, original coefficient representative F=f(x-s*y*z+g*z^3)-C(a_0), original full-profile cap (if g=0 then2else3)*natDegree(f)<=k and complete all-direction A-stop, exclude (A,(F,0)) from closure(originalFarBoundedFamily k N B) when a_1=a_2=a_3=a_4=a_5=0 and natDegree(f)>=6. All higher coefficients and inherited active-index balance are retained. General affine/mixed-curvature states are separate. Uniform hwindow still requires, for each fixed k,N,B, one b>0 with b<=originalRankEntryMinimum k N P for every real P in[2,B].

Inherited exact goal specification, not a completed proof:

```lean
∀ B A : ℝ, ∀ T : PaperI.AugmentedState k, 2 < A → A ≤ B → PaperI.AugmentedTranslationStopped A T → (PaperI.augmentedOrbitMatrix k T).rank = 4 → PaperI.augmentedStateNorm T = A → T.2.1 = 0 → T.2.2 = 0 → (∃ h : PaperI.PhysicalSpace, PaperI.physicalEuclideanNorm h = 1 ∧ PaperI.augmentedStateNorm (PaperI.augmentedOrbitDifferential k T (PaperI.upperAffineTranslationCoordinates h)) ^ 2 = A ^ (-2 : ℤ)) → (A,T) ∉ closure (PaperI.originalFarBoundedFamily k N B ∩ {z | z.1 < A})
```

Obstruction: The pure-quintic obstruction has been discharged by actual coefficient-state deformations and complete translation-energy bounds. Comparisons and shape exclusion for arbitrary profiles supported in degrees>=6 are still unproved. The scalar simultaneous-saturation and affine-centering obstructions, and the explicit mixed-profile contraction counterexample, still prevent unqualified extension. No actual-family counterexample to hwindow has been established. I625 explicitly assumes closed total bounded windows; that assumption is not itself a flaw.

Next: Before a further proof strategy, test the sixth-versus-higher comparison 36*N_5*N_n < n^2*N_6*N_(n-1) for n>=7, using the actual original norms. Check n=7,8,9,10 separately and the possible N_6>=N_1*N_5 plus n>=11 bound n^2>108. Include zero parameters, both signs, all-direction energies and the saved mixed-profile counterexample. If proved, apply inherited active-index balance to isolate an active sixth coefficient; a pure-sixth exclusion remains a separate task. None of these new comparisons is asserted proved here.

### ARG:original_rank_entry_remaining_shape_boundary_197

Location: I603-I607; I625-I638 applicability at I773; downstream I781/I875/I897-I903/I1305. Category: Implementation/manuscript-applicability difficulty; no mathematical gap established. Execution and local compactness infrastructure available..

Status: Partial original argument:211 excludes pure quintics and derives vanishing of coefficients1 through5 for centered far-closure profiles. Degree>=6 profiles, general boundary cases, hwindow and the main theorem remain unresolved.

For fixed k,N and all real B,A and augmented T, retain the196 critical conditions:2<A<=B, A-stop, exact rank4, full norm A, p=M=0, and an attained unit translation direction with energy A^(-2). Additionally assume its original polynomial linear-z coefficient is zero and T is not c times any centered symmetric quartic state (for any proof4<=k and any real a,c). Prove(A,T) is NOT in the closure of the actual same-P bounded far family restricted to P<A. This sufficient remaining-shape boundary exclusion is OPEN. It would close the unchanged hwindow when combined with the checked reductions. No such exclusion or general shape-density assertion is assumed in a completed proof.

Current remaining portion: 
Checkpoint211 remaining centered case: for every natural k,N, real B,A>=2,s!=0,g, original coefficient representative F=f(x-s*y*z+g*z^3)-C(a_0), original full-profile cap (if g=0 then2else3)*natDegree(f)<=k and complete all-direction A-stop, exclude (A,(F,0)) from closure(originalFarBoundedFamily k N B) when a_1=a_2=a_3=a_4=a_5=0 and natDegree(f)>=6. All higher coefficients and inherited active-index balance are retained. General affine/mixed-curvature states are separate. Uniform hwindow still requires, for each fixed k,N,B, one b>0 with b<=originalRankEntryMinimum k N P for every real P in[2,B].

Inherited exact goal specification, not a completed proof:

```lean
∀ B A : ℝ, ∀ T : PaperI.AugmentedState k, 2 < A → A ≤ B → PaperI.AugmentedTranslationStopped A T → (PaperI.augmentedOrbitMatrix k T).rank = 4 → PaperI.augmentedStateNorm T = A → T.2.1 = 0 → T.2.2 = 0 → (∃ h : PaperI.PhysicalSpace, PaperI.physicalEuclideanNorm h = 1 ∧ PaperI.augmentedStateNorm (PaperI.augmentedOrbitDifferential k T (PaperI.upperAffineTranslationCoordinates h)) ^ 2 = A ^ (-2 : ℤ)) → (MvPolynomial.coeff (Finsupp.single 2 1) (PaperI.coefficientPolynomial T.1) = 0) → (∀ hk : 4 ≤ k, ∀ a c : ℝ, T ≠ c • PaperI.originalQuarticState k hk a) → (A,T) ∉ closure (PaperI.originalFarBoundedFamily k N B ∩ {z | z.1 < A})
```

Obstruction: The pure-quintic obstruction has been discharged by actual coefficient-state deformations and complete translation-energy bounds. Comparisons and shape exclusion for arbitrary profiles supported in degrees>=6 are still unproved. The scalar simultaneous-saturation and affine-centering obstructions, and the explicit mixed-profile contraction counterexample, still prevent unqualified extension. No actual-family counterexample to hwindow has been established. I625 explicitly assumes closed total bounded windows; that assumption is not itself a flaw.

Next: Before a further proof strategy, test the sixth-versus-higher comparison 36*N_5*N_n < n^2*N_6*N_(n-1) for n>=7, using the actual original norms. Check n=7,8,9,10 separately and the possible N_6>=N_1*N_5 plus n>=11 bound n^2>108. Include zero parameters, both signs, all-direction energies and the saved mixed-profile counterexample. If proved, apply inherited active-index balance to isolate an active sixth coefficient; a pure-sixth exclusion remains a separate task. None of these new comparisons is asserted proved here.

### ARG:original_rank_entry_remaining_tangential_boundary_198

Location: I603-I607; I625-I638 applicability at I773; downstream I781/I875/I897-I903/I1305. Category: Implementation/manuscript-applicability difficulty; no mathematical gap established. Execution and local compactness infrastructure available..

Status: Partial original argument:211 excludes pure quintics and derives vanishing of coefficients1 through5 for centered far-closure profiles. Degree>=6 profiles, general boundary cases, hwindow and the main theorem remain unresolved.

For fixed k,N and all real B,A and augmented T, retain every197 critical condition:2<A<=B, A-stop, exact rank4, full norm A, p=M=0, attained unit translation energy A^(-2), zero original linear-z coefficient and exclusion of all real-scaled centered symmetric quartics. Additionally require OriginalQuadraticClassified T implies its original linear-y coefficient is zero. Prove(A,T) is NOT in closure of the actual same-P bounded far family restricted to P<A. This sufficient exclusion remains OPEN and would close unchanged hwindow with the checked reductions. No general density or exclusion is assumed in a completed proof.

Current remaining portion: 
Checkpoint211 remaining centered case: for every natural k,N, real B,A>=2,s!=0,g, original coefficient representative F=f(x-s*y*z+g*z^3)-C(a_0), original full-profile cap (if g=0 then2else3)*natDegree(f)<=k and complete all-direction A-stop, exclude (A,(F,0)) from closure(originalFarBoundedFamily k N B) when a_1=a_2=a_3=a_4=a_5=0 and natDegree(f)>=6. All higher coefficients and inherited active-index balance are retained. General affine/mixed-curvature states are separate. Uniform hwindow still requires, for each fixed k,N,B, one b>0 with b<=originalRankEntryMinimum k N P for every real P in[2,B].

Inherited exact goal specification, not a completed proof:

```lean
∀ B A : ℝ, ∀ T : PaperI.AugmentedState k, 2 < A → A ≤ B → PaperI.AugmentedTranslationStopped A T → (PaperI.augmentedOrbitMatrix k T).rank = 4 → PaperI.augmentedStateNorm T = A → T.2.1 = 0 → T.2.2 = 0 → (∃ h : PaperI.PhysicalSpace, PaperI.physicalEuclideanNorm h = 1 ∧ PaperI.augmentedStateNorm (PaperI.augmentedOrbitDifferential k T (PaperI.upperAffineTranslationCoordinates h)) ^ 2 = A ^ (-2 : ℤ)) → (MvPolynomial.coeff (Finsupp.single 2 1) (PaperI.coefficientPolynomial T.1) = 0) → (PaperI.OriginalQuadraticClassified T → MvPolynomial.coeff (Finsupp.single 1 1) (PaperI.coefficientPolynomial T.1) = 0) → (∀ hk : 4 ≤ k, ∀ a c : ℝ, T ≠ c • PaperI.originalQuarticState k hk a) → (A,T) ∉ closure (PaperI.originalFarBoundedFamily k N B ∩ {z | z.1 < A})
```

Obstruction: The pure-quintic obstruction has been discharged by actual coefficient-state deformations and complete translation-energy bounds. Comparisons and shape exclusion for arbitrary profiles supported in degrees>=6 are still unproved. The scalar simultaneous-saturation and affine-centering obstructions, and the explicit mixed-profile contraction counterexample, still prevent unqualified extension. No actual-family counterexample to hwindow has been established. I625 explicitly assumes closed total bounded windows; that assumption is not itself a flaw.

Next: Before a further proof strategy, test the sixth-versus-higher comparison 36*N_5*N_n < n^2*N_6*N_(n-1) for n>=7, using the actual original norms. Check n=7,8,9,10 separately and the possible N_6>=N_1*N_5 plus n>=11 bound n^2>108. Include zero parameters, both signs, all-direction energies and the saved mixed-profile counterexample. If proved, apply inherited active-index balance to isolate an active sixth coefficient; a pure-sixth exclusion remains a separate task. None of these new comparisons is asserted proved here.

## Dependency scope

Completed kernel closure 788: zero unexpanded. Completed checklist closure 847: zero unexpanded. Whole-main traversal 9786 references with 1097 unexpanded; no completion percentage. All 9371 parent rows retained; 9 reconciled, all other rows unchanged. All 451 conditional records and 18 contracts byte-preserved. Verification remains incomplete.
