import PaperILean.NullGraphRawConstraints
import PaperILean.OriginalHaarOrbitBody
import PaperILean.OriginalHaarWindowSingularValue
import PaperILean.NullFiberCoordinates

/-! I3350[345,end) / I3355[239,444): the actual ordinary raw-null differential
factors through the phase-only physical H0 action at the fixed original frame.
The raw zz row retains its factorial normalization. -/

noncomputable section
namespace PaperI.OriginalNullPhysicalPivot

open PaperI.NormalFibers PaperI.NullGraphRawConstraints

private def rawPolynomialRows : Poly →ₗ[ℝ] FrameSpace :=
  let ev := (MvPolynomial.aeval (0 : PhysicalSpace)).toLinearMap
  let dx := (MvPolynomial.pderiv (R := ℝ) (0 : Fin 3)).toLinearMap
  let dy := (MvPolynomial.pderiv (R := ℝ) (1 : Fin 3)).toLinearMap
  let dz := (MvPolynomial.pderiv (R := ℝ) (2 : Fin 3)).toLinearMap
  LinearMap.pi ![ev.comp dx, ev.comp (dy.comp dx),
    ev.comp (dz.comp dx), ev.comp (dz.comp (dz.comp dx))]

/-- Four raw normal-jet functionals, with no coefficient factorials discarded. -/
def rawRowCLM (k : ℕ) : CoefficientSpace k →L[ℝ] FrameSpace :=
  LinearMap.toContinuousLinearMap (rawPolynomialRows.comp
    ((zeroConstantPolynomialSpace k).subtype.comp (coefficientPolynomialEquiv k).toLinearMap))

theorem rawRowCLM_apply {k : ℕ} (J : CoefficientSpace k) :
    rawRowCLM k J =
      ![MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (coefficientPolynomial J)),
        MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 (coefficientPolynomial J))),
        MvPolynomial.eval 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 0 (coefficientPolynomial J))),
        MvPolynomial.eval 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2
          (MvPolynomial.pderiv 0 (coefficientPolynomial J))))] := by
  ext i
  fin_cases i <;> simp [rawRowCLM, rawPolynomialRows, coefficientPolynomial, MvPolynomial.aeval_def]

/-- The actual H0 tangent in the old raw-frame order (c,a,b,d) = (Tx,A,C,D). -/
def frameLieEmbed : FrameSpace →L[ℝ] (Fin 6 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 2,
    ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 3, 0, 0]

theorem frameLieEmbed_apply (w : FrameSpace) :
    frameLieEmbed w = ![w 1, w 2, w 0, w 3, 0, 0] := by
  ext i
  fin_cases i <;> simp [frameLieEmbed]

theorem frameLieEmbed_eq_h0 (w : FrameSpace) :
    frameLieEmbed w = originalHaarLieEmbed .H0 ![w 1, w 2, w 0, w 3] := by
  ext i
  fin_cases i <;> rfl

theorem h0_embed_eq_frameLieEmbed (v : OriginalHaarLieCoordinates .H0) :
    originalHaarLieEmbed .H0 v = frameLieEmbed ![v 2, v 0, v 1, v 3] := by
  ext i
  fin_cases i <;> rfl

private theorem affine_pullback (w : FrameSpace) (P : Poly) :
    affinePolynomialMap ![(frameLieEmbed w) 2, (frameLieEmbed w) 4, (frameLieEmbed w) 5]
        (originalUpperLinearMatrix (frameLieEmbed w)) P = pullback w 0 0 P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [affinePolynomialMap]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, hP, map_mul]
      congr 1
      fin_cases i <;>
        simp [affinePolynomialMap, affineCoordinate, originalUpperLinearMatrix,
          frameLieEmbed_apply, frameVariables, Fin.sum_univ_succ] <;> ring

/-- Literal equality with the coefficient orbit after removal only of the parent constant. -/
theorem raw_orbit_eq {k : ℕ} (J : CoefficientSpace k) :
    bracketedRawNullConstraints J 2 =
      fun w => rawRowCLM k (originalUpperCoefficientPullback J (frameLieEmbed w)) := by
  funext w
  rw [rawRowCLM_apply]
  simp only [originalUpperCoefficientPullback, polynomial_affineCoefficientMap, affine_pullback]
  simp [bracketedRawNullConstraints, iteratedPolynomialPartial]

/-- The actual raw normal equations differentiate through the full phase-only H0 action. -/
theorem raw_derivative_physical {k : ℕ} (J : CoefficientSpace k) (v : FrameSpace) :
    fderiv ℝ (bracketedRawNullConstraints J 2) 0 v =
      rawRowCLM k (originalHaarPhysicalLieAction J (frameLieEmbed v)) := by
  have ho := (((OriginalHaarOrbitBody.contDiff_orbit J).differentiable (by simp))
    (0 : Fin 6 → ℝ)).hasFDerivAt
  have he : frameLieEmbed (0 : FrameSpace) = 0 := map_zero _
  rw [← he] at ho
  have hc := (rawRowCLM k).hasFDerivAt.comp 0 (ho.comp 0 frameLieEmbed.hasFDerivAt)
  have hc' : HasFDerivAt (bracketedRawNullConstraints J 2)
      ((rawRowCLM k).comp ((fderiv ℝ (originalUpperCoefficientPullback J) 0).comp frameLieEmbed)) 0 := by
    simpa only [he, Function.comp_def, ← raw_orbit_eq] using hc
  rw [hc'.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hb := OriginalHaarOrbitBody.fderiv_orbit_body J 0 (frameLieEmbed v)
  have hv : originalUpperBodyVelocity 0 (frameLieEmbed v) = frameLieEmbed v := by
    ext i
    fin_cases i <;> simp [originalUpperBodyVelocity]
  rw [hv, NullFiberCoordinates.coefficient_zero] at hb
  exact congrArg (rawRowCLM k) hb

end PaperI.OriginalNullPhysicalPivot
