import PaperILean.HorizontalCriticalityBound
import PaperILean.TensorFrameBounds

/-! I298: Euclidean operator-norm bridges and exact relative-frame calculus.
The matrix norm below is the Euclidean operator norm, not the entrywise or HS
norm. No commutation or lower bound on individual singular values is assumed. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem euclideanFrameOperatorNorm_eq_matrix_opNorm (A : Matrix (Fin 3) (Fin 3) ℝ) :
    euclideanFrameOperatorNorm A = ‖A‖ := by
  change ‖euclideanFrameMap A‖ = ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A‖
  congr 1

theorem physicalEuclideanNorm_mulVec_le_opNorm (A : Matrix (Fin 3) (Fin 3) ℝ)
    (v : PhysicalSpace) : physicalEuclideanNorm (A *ᵥ v) ≤ ‖A‖ * physicalEuclideanNorm v := by
  rw [← euclideanFrameOperatorNorm_eq_matrix_opNorm]
  exact (euclideanFrameOperatorNorm_le_iff A (euclideanFrameOperatorNorm A)
    (norm_nonneg _)).mp le_rfl v

theorem physicalEuclideanNorm_mulVec_le_fullHS (A : Matrix (Fin 3) (Fin 3) ℝ)
    (v : PhysicalSpace) :
    physicalEuclideanNorm (A *ᵥ v) ≤ matrixFullHSNorm A * physicalEuclideanNorm v := by
  apply (sq_le_sq₀ (physicalEuclideanNorm_nonneg _)
    (mul_nonneg (matrixFullHSNorm_nonneg A) (physicalEuclideanNorm_nonneg v))).mp
  simp only [physicalEuclideanNorm, coordinateL2Norm_sq, mul_pow, matrixFullHSNorm_sq,
    Matrix.mulVec, dotProduct]
  calc
    (∑ i, (∑ j, A i j * v j) ^ 2) ≤ ∑ i, (∑ j, (A i j) ^ 2) * (∑ j, (v j) ^ 2) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) v)
    _ = _ := by rw [Finset.sum_mul]

theorem matrix_opNorm_le_fullHS (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ‖A‖ ≤ matrixFullHSNorm A := by
  rw [← euclideanFrameOperatorNorm_eq_matrix_opNorm]
  exact (euclideanFrameOperatorNorm_le_iff A (matrixFullHSNorm A)
    (matrixFullHSNorm_nonneg A)).mpr (physicalEuclideanNorm_mulVec_le_fullHS A)

theorem relativeFrame_inverse (B₀ B : PositiveFrame) :
    (B₀.val⁻¹ * B.val)⁻¹ = B.val⁻¹ * B₀.val := by
  rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr B₀.property.ne')]

theorem relativeFrame_normalized_velocity (B₀ B : PositiveFrame) (u : PhysicalSpace) :
    B.val⁻¹ *ᵥ (B₀.val *ᵥ u) = (B₀.val⁻¹ * B.val)⁻¹ *ᵥ u := by
  rw [relativeFrame_inverse, Matrix.mulVec_mulVec]

theorem relativeFrame_initial (B₀ : PositiveFrame) : B₀.val⁻¹ * B₀.val = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr B₀.property.ne')

theorem hasDerivAt_relativeFrame {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {S : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ} (B₀ : PositiveFrame)
    (hB : HasDerivAt B (B t * S) t) :
    HasDerivAt (fun u => B₀.val⁻¹ * B u) ((B₀.val⁻¹ * B t) * S) t := by
  simpa only [Matrix.mul_assoc] using hB.const_mul B₀.val⁻¹

theorem hasDerivAt_relativeFrame_inverse {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {S : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ} (B₀ : PositiveFrame)
    (hp : 0 < (B t).det) (hB : HasDerivAt B (B t * S) t) :
    HasDerivAt (fun u => (B₀.val⁻¹ * B u)⁻¹) (-S * (B₀.val⁻¹ * B t)⁻¹) t := by
  apply hasDerivAt_inverse_horizontal (hasDerivAt_relativeFrame B₀ hB)
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_mul, Matrix.det_nonsing_inv]
  simpa only [Ring.inverse_eq_inv] using
    (isUnit_iff_ne_zero.mpr B₀.property.ne').inv.mul (isUnit_iff_ne_zero.mpr hp.ne')

end PaperI
