import PaperILean.FixedDRelativeStage
import PaperILean.RelativeFrameCalculus
import PaperILean.OriginalUpperNormalPullback

/-! The literal original affine neighborhood used in I3244[218,275).
The matrix norms in the conclusion are Euclidean operator norms. All
translations are retained, and no absolute frame bound is assumed. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
open Matrix
namespace PaperI.ExceptionalPackingBounds

private theorem linear_inverse (a : Fin 6 → ℝ) :
    (originalUpperLinearMatrix a)⁻¹ =
      originalUpperLinearMatrix (originalUpperAffineInv a) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originalUpperLinearMatrix,originalUpperAffineInv,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]
  all_goals ring

private theorem linear_relative (a b : Fin 6 → ℝ) :
    (originalUpperLinearMatrix a)⁻¹ * originalUpperLinearMatrix b =
      originalUpperLinearMatrix (originalUpperRelativeFrame a b) := by
  rw [linear_inverse]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originalUpperLinearMatrix,originalUpperRelativeFrame,
      originalUpperAffineComp,originalUpperAffineInv,Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

private theorem translation_relative (a b : Fin 6 → ℝ) :
    (originalUpperLinearMatrix a)⁻¹ *ᵥ (![b 2,b 4,b 5]-![a 2,a 4,a 5]) =
      ![originalUpperRelativeFrame a b 2,originalUpperRelativeFrame a b 4,
        originalUpperRelativeFrame a b 5] := by
  rw [linear_inverse]
  ext i
  fin_cases i <;>
    simp [originalUpperLinearMatrix,originalUpperRelativeFrame,
      originalUpperAffineComp,originalUpperAffineInv,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ] <;> ring

private theorem linear_HS_le_homogeneous (g : Fin 6 → ℝ) :
    matrixFullHSNorm (originalUpperLinearMatrix g) ≤
      matrixFullHSNorm (originalAffineHomogeneousMatrix g) := by
  apply (sq_le_sq₀ (matrixFullHSNorm_nonneg _) (matrixFullHSNorm_nonneg _)).mp
  simp only [matrixFullHSNorm_sq]
  simp [Fin.sum_univ_succ,originalUpperLinearMatrix,originalAffineHomogeneousMatrix]
  nlinarith [sq_nonneg (g 2),sq_nonneg (g 4),sq_nonneg (g 5)]

private theorem translation_norm_le_homogeneous (g : Fin 6 → ℝ) :
    physicalEuclideanNorm ![g 2,g 4,g 5] ≤
      matrixFullHSNorm (originalAffineHomogeneousMatrix g) := by
  apply (sq_le_sq₀ (physicalEuclideanNorm_nonneg _) (matrixFullHSNorm_nonneg _)).mp
  simp only [physicalEuclideanNorm,coordinateL2Norm_sq,matrixFullHSNorm_sq]
  simp [Fin.sum_univ_succ,originalAffineHomogeneousMatrix]
  nlinarith [sq_nonneg (g 0),sq_nonneg (g 1),sq_nonneg (g 3)]

/-- Saved homogeneous matrix and inverse control implies exactly the source
relative-neighborhood maximum, with the original normalized displacement. -/
theorem literal_relative_neighborhood_le (a b : Fin 6 → ℝ) (T : ℝ)
    (hHS : matrixFullHSNorm
        ((originalAffineHomogeneousMatrix a)⁻¹ * originalAffineHomogeneousMatrix b) +
      matrixFullHSNorm
        (((originalAffineHomogeneousMatrix a)⁻¹ * originalAffineHomogeneousMatrix b)⁻¹) ≤ T) :
    max ‖(originalUpperLinearMatrix a)⁻¹ * originalUpperLinearMatrix b‖
      (max ‖((originalUpperLinearMatrix a)⁻¹ * originalUpperLinearMatrix b)⁻¹‖
        (physicalEuclideanNorm
          ((originalUpperLinearMatrix a)⁻¹ *ᵥ (![b 2,b 4,b 5]-![a 2,a 4,a 5])))) ≤ T := by
  rw [originalAffineHomogeneousMatrix_relative,
    originalAffineHomogeneousMatrix_inverse] at hHS
  have hf : matrixFullHSNorm (originalAffineHomogeneousMatrix (originalUpperRelativeFrame a b)) ≤ T :=
    (le_add_of_nonneg_right (matrixFullHSNorm_nonneg _)).trans hHS
  have hi : matrixFullHSNorm
      (originalAffineHomogeneousMatrix (originalUpperAffineInv (originalUpperRelativeFrame a b))) ≤ T :=
    (le_add_of_nonneg_left (matrixFullHSNorm_nonneg _)).trans hHS
  rw [linear_relative,linear_inverse,translation_relative]
  exact max_le ((matrix_opNorm_le_fullHS _).trans ((linear_HS_le_homogeneous _).trans hf))
    (max_le ((matrix_opNorm_le_fullHS _).trans ((linear_HS_le_homogeneous _).trans hi))
      ((translation_norm_le_homogeneous _).trans hf))

end PaperI.ExceptionalPackingBounds
