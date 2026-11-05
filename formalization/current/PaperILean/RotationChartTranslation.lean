import PaperILean.RotationChartJacobian

/-! I331 prerequisite: the exact local left-translation Jacobian law.
Both chart-membership conditions are explicit; no global logarithm identity
or Haar-measure formula is assumed. -/
noncomputable section
open Set Filter
open scoped Topology Matrix Matrix.L2OpNorm
namespace PaperI

def rotationChartLeftTranslation (g : rotationGroup3) (x : PhysicalSpace) : PhysicalSpace :=
  rotationCoordinateLog (g * rotationCoordinateExp x)

def rotationChartTranslationSource (g : rotationGroup3) : Set PhysicalSpace :=
  {x | x ∈ rotationChartSource ∧ g * rotationCoordinateExp x ∈ rotationChartTarget}

def rotationChartTranslationDifferential (g : rotationGroup3) (x : PhysicalSpace) :
    PhysicalSpace →L[ℝ] PhysicalSpace :=
  (skewCoordinatesMatrixCLM.comp
    (fderiv ℝ matrixLogSeries (rotationMatrix (g * rotationCoordinateExp x)))).comp
      ((rotationLeftMultiply g).comp (rotationChartDifferential x))

theorem rotationChartTranslationSource_isOpen (g : rotationGroup3) :
    IsOpen (rotationChartTranslationSource g) :=
  rotationChartSource_isOpen.inter
    (rotationChartTarget_isOpen.preimage (continuous_const.mul rotationCoordinateExp_continuous))

theorem rotationChartLeftTranslation_mem_source (g : rotationGroup3) (x : PhysicalSpace)
    (hx : x ∈ rotationChartTranslationSource g) :
    rotationChartLeftTranslation g x ∈ rotationChartSource :=
  rotationCoordinateLog_mapsTo_chart hx.2

theorem rotationChartLeftTranslation_exp (g : rotationGroup3) (x : PhysicalSpace)
    (hx : x ∈ rotationChartTranslationSource g) :
    rotationCoordinateExp (rotationChartLeftTranslation g x) = g * rotationCoordinateExp x :=
  rotationCoordinateExp_coordinateLog _ hx.2

theorem rotationChartLeftTranslation_matrix (g : rotationGroup3) (x : PhysicalSpace)
    (hx : x ∈ rotationChartTranslationSource g) :
    rotationMatrix (rotationCoordinateExp (rotationChartLeftTranslation g x)) =
      rotationMatrix g * rotationMatrix (rotationCoordinateExp x) := by
  rw [rotationChartLeftTranslation_exp g x hx, rotationMatrix_mul]

theorem rotationChartLeftTranslation_hasStrictFDerivAt (g : rotationGroup3) (x : PhysicalSpace)
    (hx : x ∈ rotationChartTranslationSource g) :
    HasStrictFDerivAt (rotationChartLeftTranslation g) (rotationChartTranslationDifferential g x) x := by
  exact (skewCoordinatesMatrixCLM.hasStrictFDerivAt.comp _
    (matrixLogSeries_hasStrictFDerivAt _ hx.2.1)).comp x
      ((rotationLeftMultiply g).hasStrictFDerivAt.comp x
        (rotationCoordinateExp_matrix_hasStrictFDerivAt x))

theorem rotationChartLeftTranslation_fderiv (g : rotationGroup3) (x : PhysicalSpace)
    (hx : x ∈ rotationChartTranslationSource g) :
    fderiv ℝ (rotationChartLeftTranslation g) x = rotationChartTranslationDifferential g x :=
  (rotationChartLeftTranslation_hasStrictFDerivAt g x hx).hasFDerivAt.fderiv

theorem rotationChartLeftTranslation_contDiffAt (g : rotationGroup3) (x : PhysicalSpace)
    (hx : x ∈ rotationChartTranslationSource g) :
    ContDiffAt ℝ ⊤ (rotationChartLeftTranslation g) x := by
  exact ((rotationLogCoordinatesAmbient_analyticAt _ hx.2.1).comp
    (f := fun y : PhysicalSpace => rotationMatrix g * rotationMatrix (rotationCoordinateExp y))
    ((rotationLeftMultiply g).analyticAt _ |>.comp
      (rotationCoordinateExp_matrix_analyticAt x))).contDiffAt

theorem rotationChartLeftTranslation_contDiffOn (g : rotationGroup3) :
    ContDiffOn ℝ ⊤ (rotationChartLeftTranslation g) (rotationChartTranslationSource g) :=
  fun x hx => (rotationChartLeftTranslation_contDiffAt g x hx).contDiffWithinAt

theorem rotationChartTranslation_chain (g : rotationGroup3) (x : PhysicalSpace)
    (hx : x ∈ rotationChartTranslationSource g) :
    (rotationChartDifferential (rotationChartLeftTranslation g x)).comp
      (rotationChartTranslationDifferential g x) =
        (rotationLeftMultiply g).comp (rotationChartDifferential x) := by
  have he : (fun y => rotationMatrix (rotationCoordinateExp (rotationChartLeftTranslation g y)))
      =ᶠ[𝓝 x] (fun y => rotationMatrix g * rotationMatrix (rotationCoordinateExp y)) := by
    filter_upwards [(rotationChartTranslationSource_isOpen g).mem_nhds hx] with y hy
    exact rotationChartLeftTranslation_matrix g y hy
  have hl := (rotationCoordinateExp_matrix_hasStrictFDerivAt
    (rotationChartLeftTranslation g x)).hasFDerivAt.comp x
      (rotationChartLeftTranslation_hasStrictFDerivAt g x hx).hasFDerivAt
  have hr := (rotationLeftMultiply g).hasFDerivAt.comp x
    (rotationCoordinateExp_matrix_hasStrictFDerivAt x).hasFDerivAt
  exact hl.unique (hr.congr_of_eventuallyEq he)

theorem rotationTangentCoordinates_translation_cocycle (g : rotationGroup3) (x : PhysicalSpace)
    (hx : x ∈ rotationChartTranslationSource g) :
    (rotationTangentCoordinates (rotationChartLeftTranslation g x)).comp
      (rotationChartTranslationDifferential g x) = rotationTangentCoordinates x := by
  ext v i
  have hc := congrArg (fun D : PhysicalSpace →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ => D v)
    (rotationChartTranslation_chain g x hx)
  change rotationChartDifferential (rotationChartLeftTranslation g x)
    (rotationChartTranslationDifferential g x v) =
      rotationMatrix g * rotationChartDifferential x v at hc
  simp only [ContinuousLinearMap.comp_apply, rotationTangentCoordinates_apply]
  rw [hc, rotationChartLeftTranslation_matrix g x hx, Matrix.transpose_mul]
  have he : ((rotationMatrix (rotationCoordinateExp x))ᵀ * (rotationMatrix g)ᵀ) *
      (rotationMatrix g * rotationChartDifferential x v) =
        (rotationMatrix (rotationCoordinateExp x))ᵀ * rotationChartDifferential x v := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (rotationMatrix g)ᵀ,
      rotationMatrix_inv_mul, Matrix.one_mul]
  rw [he]

theorem rotationChartSignedJacobian_translation (g : rotationGroup3) (x : PhysicalSpace)
    (hx : x ∈ rotationChartTranslationSource g) :
    rotationChartSignedJacobian (rotationChartLeftTranslation g x) *
      (rotationChartTranslationDifferential g x).toLinearMap.det = rotationChartSignedJacobian x := by
  have h := congrArg (fun D : PhysicalSpace →L[ℝ] PhysicalSpace => D.toLinearMap.det)
    (rotationTangentCoordinates_translation_cocycle g x hx)
  change LinearMap.det ((rotationTangentCoordinates (rotationChartLeftTranslation g x)).toLinearMap.comp
    (rotationChartTranslationDifferential g x).toLinearMap) = _ at h
  rw [LinearMap.det_comp] at h
  exact h

theorem rotationChartJacobian_translation (g : rotationGroup3) (x : PhysicalSpace)
    (hx : x ∈ rotationChartTranslationSource g) :
    rotationChartJacobian (rotationChartLeftTranslation g x) *
      |(rotationChartTranslationDifferential g x).toLinearMap.det| = rotationChartJacobian x := by
  simpa only [abs_mul, rotationChartJacobian] using
    congrArg abs (rotationChartSignedJacobian_translation g x hx)

theorem rotationChartTranslationDifferential_det_ne_zero (g : rotationGroup3) (x : PhysicalSpace)
    (hx : x ∈ rotationChartTranslationSource g) :
    (rotationChartTranslationDifferential g x).toLinearMap.det ≠ 0 := by
  intro h
  have hc := rotationChartSignedJacobian_translation g x hx
  rw [h, mul_zero] at hc
  exact rotationChartSignedJacobian_ne_zero x hx.1 hc.symm

theorem rotationChartLeftTranslation_injOn (g : rotationGroup3) :
    InjOn (rotationChartLeftTranslation g) (rotationChartTranslationSource g) := by
  intro x hx y hy h
  apply rotationCoordinateExp_injOn_chart hx.1 hy.1
  apply mul_left_cancel (a := g)
  rw [← rotationChartLeftTranslation_exp g x hx, ← rotationChartLeftTranslation_exp g y hy, h]

theorem rotationChartLeftTranslation_inverse_source (g : rotationGroup3) (x : PhysicalSpace)
    (hx : x ∈ rotationChartTranslationSource g) :
    rotationChartLeftTranslation g x ∈ rotationChartTranslationSource g⁻¹ := by
  refine ⟨rotationChartLeftTranslation_mem_source g x hx, ?_⟩
  rw [rotationChartLeftTranslation_exp g x hx, inv_mul_cancel_left]
  exact rotationCoordinateExp_mapsTo_chart hx.1

theorem rotationChartLeftTranslation_inverse (g : rotationGroup3) (x : PhysicalSpace)
    (hx : x ∈ rotationChartTranslationSource g) :
    rotationChartLeftTranslation g⁻¹ (rotationChartLeftTranslation g x) = x := by
  unfold rotationChartLeftTranslation
  rw [rotationCoordinateExp_coordinateLog _ hx.2, inv_mul_cancel_left]
  exact rotationCoordinateLog_coordinateExp x hx.1

theorem rotationChartLeftTranslation_image_source (g : rotationGroup3) :
    rotationChartLeftTranslation g '' rotationChartTranslationSource g =
      rotationChartTranslationSource g⁻¹ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact rotationChartLeftTranslation_inverse_source g x hx
  · intro y hy
    refine ⟨rotationChartLeftTranslation g⁻¹ y, ?_, ?_⟩
    · simpa only [inv_inv] using rotationChartLeftTranslation_inverse_source g⁻¹ y hy
    · simpa only [inv_inv] using rotationChartLeftTranslation_inverse g⁻¹ y hy

end PaperI
