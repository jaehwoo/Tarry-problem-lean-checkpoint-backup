import PaperILean.RotationChartRegularity

/-! I331 prerequisite: left-trivialized tangent coordinates for the actual
exponential chart. No Haar measure or volume-identification claim is made here. -/
noncomputable section
open Set
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

theorem rotationMatrix_inv_mul (O : rotationGroup3) :
    (rotationMatrix O)ᵀ * rotationMatrix O = 1 := by
  rw [← rotationMatrix_inv, ← rotationMatrix_mul, inv_mul_cancel, rotationMatrix_one]

def rotationLeftMultiply (O : rotationGroup3) :
    Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
  ContinuousLinearMap.mul ℝ _ (rotationMatrix O)

theorem rotationLeftMultiply_apply (O : rotationGroup3) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    rotationLeftMultiply O A = rotationMatrix O * A := rfl

theorem rotationLeftMultiply_continuous : Continuous rotationLeftMultiply :=
  (ContinuousLinearMap.mul ℝ (Matrix (Fin 3) (Fin 3) ℝ)).continuous.comp
    rotationMatrix_continuous

theorem rotationMatrix_tangent_skew {f : PhysicalSpace → rotationGroup3}
    {P : PhysicalSpace →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ} {x : PhysicalSpace}
    (hf : HasFDerivAt (fun y => rotationMatrix (f y)) P x) (v : PhysicalSpace) :
    ((rotationMatrix (f x))ᵀ * P v)ᵀ = -((rotationMatrix (f x))ᵀ * P v) := by
  let T := (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℝ ℝ).toContinuousLinearEquiv
  have ht := T.hasFDerivAt.comp x hf
  have hp := ht.mul' hf
  have he : (fun y => (rotationMatrix (f y))ᵀ * rotationMatrix (f y)) =
      (fun _ : PhysicalSpace => (1 : Matrix (Fin 3) (Fin 3) ℝ)) :=
    funext (fun y => rotationMatrix_inv_mul (f y))
  change HasFDerivAt (fun y => (rotationMatrix (f y))ᵀ * rotationMatrix (f y)) _ x at hp
  rw [he] at hp
  have hd := congrArg (fun D : PhysicalSpace →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ => D v)
    (hp.unique (hasFDerivAt_const (1 : Matrix (Fin 3) (Fin 3) ℝ) x))
  change (rotationMatrix (f x))ᵀ * P v + (P v)ᵀ * rotationMatrix (f x) = 0 at hd
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  exact eq_neg_of_add_eq_zero_right hd

def rotationTangentCoordinates (x : PhysicalSpace) : PhysicalSpace →L[ℝ] PhysicalSpace :=
  skewCoordinatesMatrixCLM.comp
    ((rotationLeftMultiply (rotationCoordinateExp x)⁻¹).comp (rotationChartDifferential x))

theorem rotationTangentCoordinates_apply (x v : PhysicalSpace) :
    rotationTangentCoordinates x v = skewCoordinatesOfMatrix
      ((rotationMatrix (rotationCoordinateExp x))ᵀ * rotationChartDifferential x v) := by
  simp only [rotationTangentCoordinates, ContinuousLinearMap.comp_apply,
    rotationLeftMultiply_apply, rotationMatrix_inv, skewCoordinatesMatrixCLM_apply]

theorem rotationChartDifferential_left_trivialized_skew (x v : PhysicalSpace) :
    ((rotationMatrix (rotationCoordinateExp x))ᵀ * rotationChartDifferential x v)ᵀ =
      -((rotationMatrix (rotationCoordinateExp x))ᵀ * rotationChartDifferential x v) :=
  rotationMatrix_tangent_skew
    (rotationCoordinateExp_matrix_hasStrictFDerivAt x).hasFDerivAt v

theorem rotationTangentCoordinates_reconstruct (x v : PhysicalSpace) :
    skewMatrixOfCoordinates (rotationTangentCoordinates x v) =
      (rotationMatrix (rotationCoordinateExp x))ᵀ * rotationChartDifferential x v := by
  rw [rotationTangentCoordinates_apply]
  exact skewMatrixOfCoordinates_right_inverse _
    (rotationChartDifferential_left_trivialized_skew x v)

theorem rotationChartDifferential_from_tangent (x v : PhysicalSpace) :
    rotationMatrix (rotationCoordinateExp x) *
      skewMatrixOfCoordinates (rotationTangentCoordinates x v) =
        rotationChartDifferential x v := by
  rw [rotationTangentCoordinates_reconstruct, ← Matrix.mul_assoc,
    rotationMatrix_orthogonal, Matrix.one_mul]

theorem rotationTangentCoordinates_injective (x : PhysicalSpace)
    (hx : x ∈ rotationChartSource) : Function.Injective (rotationTangentCoordinates x) := by
  intro v w h
  apply rotationChartDifferential_injective x hx
  rw [← rotationChartDifferential_from_tangent x v,
    ← rotationChartDifferential_from_tangent x w, h]

theorem rotationTangentCoordinates_bijective (x : PhysicalSpace)
    (hx : x ∈ rotationChartSource) : Function.Bijective (rotationTangentCoordinates x) :=
  ⟨rotationTangentCoordinates_injective x hx,
    LinearMap.injective_iff_surjective.mp (rotationTangentCoordinates_injective x hx)⟩

def rotationTangentCoordinatesEquiv (x : PhysicalSpace) (hx : x ∈ rotationChartSource) :
    PhysicalSpace ≃L[ℝ] PhysicalSpace :=
  (LinearEquiv.ofBijective (rotationTangentCoordinates x).toLinearMap
    (rotationTangentCoordinates_bijective x hx)).toContinuousLinearEquiv

theorem rotationTangentCoordinatesEquiv_apply (x : PhysicalSpace)
    (hx : x ∈ rotationChartSource) (v : PhysicalSpace) :
    rotationTangentCoordinatesEquiv x hx v = rotationTangentCoordinates x v := rfl

theorem rotationTangentCoordinates_continuous : Continuous rotationTangentCoordinates :=
  continuous_const.clm_comp
    ((rotationLeftMultiply_continuous.comp rotationCoordinateExp_continuous.inv).clm_comp
      rotationChartDifferential_continuous)

theorem rotationChartDifferential_zero :
    rotationChartDifferential 0 = skewMatrixCoordinatesCLM := by
  rw [← rotationCoordinateExp_matrix_fderiv, rotationCoordinateExp_matrix_fderiv_zero]

theorem rotationTangentCoordinates_zero :
    rotationTangentCoordinates 0 = ContinuousLinearMap.id ℝ PhysicalSpace := by
  ext v i
  rw [rotationTangentCoordinates_apply, rotationCoordinateExp_zero, rotationMatrix_one,
    Matrix.transpose_one, Matrix.one_mul, rotationChartDifferential_zero]
  exact congrFun (skewCoordinatesOfMatrix_left_inverse v) i

end PaperI
