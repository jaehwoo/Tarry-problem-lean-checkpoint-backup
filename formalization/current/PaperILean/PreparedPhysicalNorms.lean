import PaperILean.MiddleSingularNorm
import PaperILean.AugmentedStateSpace

/-! Exact Euclidean block estimates and body-field normalization for I3253.
The physical matrix norm is the literal Hilbert--Schmidt norm. -/
noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI.PreparedPhysicalNorms
open MiddleSingularNorm RankOneAffineMatrix

def physicalMatrixFrobenius (B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, B i j ^ 2)

theorem physicalMatrixFrobenius_nonneg (B : Matrix (Fin 3) (Fin 3) ℝ) :
    0 ≤ physicalMatrixFrobenius B := Real.sqrt_nonneg _

theorem physicalMatrixFrobenius_sq (B : Matrix (Fin 3) (Fin 3) ℝ) :
    physicalMatrixFrobenius B ^ 2 = ∑ i, ∑ j, B i j ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem physicalAffineNorm_sq_blocks (ell : PhysicalAffineData) :
    physicalAffineNorm ell ^ 2 = physicalEuclideanNorm ell.1 ^ 2 +
      physicalMatrixFrobenius ell.2 ^ 2 := by
  rw [physicalAffineNorm_sq, physicalMatrixFrobenius_sq]
  rw [physicalEuclideanNorm, coordinateL2Norm_sq]

theorem physical_translation_le_affine (ell : PhysicalAffineData) :
    physicalEuclideanNorm ell.1 ≤ physicalAffineNorm ell := by
  apply (sq_le_sq₀ (physicalEuclideanNorm_nonneg _) (physicalAffineNorm_nonneg _)).mp
  rw [physicalAffineNorm_sq_blocks]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem physical_matrix_le_affine (ell : PhysicalAffineData) :
    physicalMatrixFrobenius ell.2 ≤ physicalAffineNorm ell := by
  apply (sq_le_sq₀ (physicalMatrixFrobenius_nonneg _) (physicalAffineNorm_nonneg _)).mp
  rw [physicalAffineNorm_sq_blocks]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem physicalAffineNorm_le_augmented {k : ℕ} (S : AugmentedState k) :
    physicalAffineNorm S.2 ≤ augmentedStateNorm S := by
  apply (sq_le_sq₀ (physicalAffineNorm_nonneg _) (augmentedStateNorm_nonneg _)).mp
  rw [augmentedStateNorm_sq_eq]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem physical_blocks_sum_le_augmented {k : ℕ} (S : AugmentedState k) :
    physicalMatrixFrobenius S.2.2 + physicalEuclideanNorm S.2.1 ≤
      2 * augmentedStateNorm S := by
  have hm := (physical_matrix_le_affine S.2).trans (physicalAffineNorm_le_augmented S)
  have hp := (physical_translation_le_affine S.2).trans (physicalAffineNorm_le_augmented S)
  linarith

theorem affineFieldMatrix_smul (r : ℝ) (b : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) :
    affineFieldMatrix (r • b) (r • N) = r • affineFieldMatrix b N := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [affineFieldMatrix_last, Matrix.smul_apply, Pi.smul_apply]
  · simp only [affineFieldMatrix_castSucc, Matrix.smul_apply, Pi.smul_apply]

theorem matrixFrobenius_smul (r : ℝ) (M : Matrix (Fin 3) (Fin 4) ℝ) :
    matrixFrobenius (r • M) = |r| * matrixFrobenius M := by
  have hs : matrixFrobenius (r • M) ^ 2 = (|r| * matrixFrobenius M) ^ 2 := by
    simp only [matrixFrobenius_sq, Matrix.smul_apply, smul_eq_mul, mul_pow,
      sq_abs, Finset.mul_sum]
  have hleft := matrixFrobenius_nonneg (r • M)
  have hright := mul_nonneg (abs_nonneg r) (matrixFrobenius_nonneg M)
  nlinarith

theorem upperAffineFieldMatrix_norm (ξ : Fin 6 → ℝ) :
    matrixFrobenius (affineFieldMatrix (upperAffineFieldTranslation ξ)
      (upperAffineFieldLinear ξ)) = coordinateL2Norm ξ := by
  unfold matrixFrobenius coordinateL2Norm
  congr 1
  simp only [Fin.sum_univ_castSucc, affineFieldMatrix_last, affineFieldMatrix_castSucc]
  simp [upperAffineFieldTranslation, upperAffineFieldLinear]
  ring

end PaperI.PreparedPhysicalNorms
