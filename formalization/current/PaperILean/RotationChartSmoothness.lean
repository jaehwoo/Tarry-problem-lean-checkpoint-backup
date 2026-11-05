import PaperILean.RotationChartMeasurability

/-! I331 prerequisite: actual multidimensional regularity of the forward map.
The derivative at zero has rank three. This does not assert a nine-dimensional
ambient isomorphism or a nonvanishing Haar Jacobian on the entire chart. -/
noncomputable section
open Set
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem rotationCoordinateExp_matrix_analyticAt (x : PhysicalSpace) :
    AnalyticAt ℝ (fun y => rotationMatrix (rotationCoordinateExp y)) x := by
  exact (NormedSpace.exp_analytic (skewMatrixCoordinatesCLM x)).comp
    (skewMatrixCoordinatesCLM.analyticAt x)

theorem rotationCoordinateExp_matrix_contDiff :
    ContDiff ℝ ⊤ (fun x => rotationMatrix (rotationCoordinateExp x)) :=
  (show AnalyticOnNhd ℝ (fun x => rotationMatrix (rotationCoordinateExp x)) univ from
    fun x _ => rotationCoordinateExp_matrix_analyticAt x).contDiff

theorem rotationCoordinateExp_matrix_hasStrictFDerivAt_zero :
    HasStrictFDerivAt (fun x => rotationMatrix (rotationCoordinateExp x))
      skewMatrixCoordinatesCLM (0 : PhysicalSpace) := by
  have he : HasStrictFDerivAt (NormedSpace.exp ℝ)
      (1 : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ)
      (skewMatrixCoordinatesCLM (0 : PhysicalSpace)) := by
    simpa only [map_zero] using
      (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin 3) (Fin 3) ℝ))
  exact he.comp (0 : PhysicalSpace) skewMatrixCoordinatesCLM.hasStrictFDerivAt

theorem rotationCoordinateExp_matrix_hasFDerivAt_zero :
    HasFDerivAt (fun x => rotationMatrix (rotationCoordinateExp x))
      skewMatrixCoordinatesCLM (0 : PhysicalSpace) :=
  rotationCoordinateExp_matrix_hasStrictFDerivAt_zero.hasFDerivAt

theorem rotationCoordinateExp_matrix_fderiv_zero :
    fderiv ℝ (fun x => rotationMatrix (rotationCoordinateExp x)) 0 = skewMatrixCoordinatesCLM :=
  rotationCoordinateExp_matrix_hasFDerivAt_zero.fderiv

theorem rotationCoordinateExp_matrix_fderiv_zero_injective :
    Function.Injective (fderiv ℝ (fun x => rotationMatrix (rotationCoordinateExp x)) 0) := by
  rw [rotationCoordinateExp_matrix_fderiv_zero]
  exact skewMatrixOfCoordinates_injective

theorem rotationCoordinateExp_coordinateProjection_hasStrictFDerivAt_zero :
    HasStrictFDerivAt (fun x => skewCoordinatesOfMatrix (rotationMatrix (rotationCoordinateExp x)))
      (ContinuousLinearMap.id ℝ PhysicalSpace) (0 : PhysicalSpace) := by
  have h := skewCoordinatesMatrixCLM.hasStrictFDerivAt.comp (0 : PhysicalSpace)
    rotationCoordinateExp_matrix_hasStrictFDerivAt_zero
  have hcomp : skewCoordinatesMatrixCLM.comp skewMatrixCoordinatesCLM =
      ContinuousLinearMap.id ℝ PhysicalSpace := by
    ext x i
    exact congrFun (skewCoordinatesOfMatrix_left_inverse x) i
  simpa only [hcomp] using h

end PaperI
