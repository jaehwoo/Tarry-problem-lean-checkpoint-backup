import PaperILean.FrameEllipsoidQuotient
import PaperILean.LogEnergyHessianFormula

/-! Fixed left-polar reduction of the actual frame log-energy term.
The direction is orthogonally conjugated, never assumed to commute with B.
This applies the already checked alternative proof of Lemma 2.2. -/

noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

def framePolarFactor (B : PositiveFrame) : unitary (Matrix (Fin 3) (Fin 3) ℝ) :=
  ⟨(sourcePositiveSqrt (B.val * B.valᵀ) (positiveFrame_gram_posDef B))⁻¹ * B.val,
    Matrix.mem_unitaryGroup_iff.mpr (by
      have hs := sourcePositiveSqrt_isSymm (B.val * B.valᵀ) (positiveFrame_gram_posDef B)
      have hg : sourcePositiveSqrt (B.val * B.valᵀ) (positiveFrame_gram_posDef B) *
          (sourcePositiveSqrt (B.val * B.valᵀ) (positiveFrame_gram_posDef B))ᵀ = B.val * B.valᵀ := by
        rw [hs.eq, sourcePositiveSqrt_mul_self]
      simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
        inverse_right_factor_orthogonal _ B.val
          (sourcePositiveSqrt_isUnit _ (positiveFrame_gram_posDef B)) hg)⟩

theorem frame_polar_decomposition (B : PositiveFrame) :
    sourcePositiveSqrt (B.val * B.valᵀ) (positiveFrame_gram_posDef B) *
      (framePolarFactor B : Matrix (Fin 3) (Fin 3) ℝ) = B.val := by
  exact Matrix.mul_nonsing_inv_cancel_left _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp (sourcePositiveSqrt_isUnit _ (positiveFrame_gram_posDef B)))

theorem frame_polar_transpose_decomposition (B : PositiveFrame) :
    star (framePolarFactor B : Matrix (Fin 3) (Fin 3) ℝ) *
      sourcePositiveSqrt (B.val * B.valᵀ) (positiveFrame_gram_posDef B) = B.valᵀ := by
  have h := congrArg Matrix.transpose (frame_polar_decomposition B)
  simpa only [Matrix.transpose_mul, (sourcePositiveSqrt_isSymm _ (positiveFrame_gram_posDef B)).eq,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem symmetric_frame_exponential_gram (B H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : H.IsSymm) (t : ℝ) :
    (B * NormedSpace.exp ℝ (t • H)) * (B * NormedSpace.exp ℝ (t • H))ᵀ =
      B * NormedSpace.exp ℝ ((2 * t) • H) * Bᵀ := by
  have he : NormedSpace.exp ℝ ((2 * t) • H) =
      NormedSpace.exp ℝ (t • H) * NormedSpace.exp ℝ (t • H) := by
    rw [show (2 * t) • H = t • H + t • H by rw [← add_smul]; congr 1; ring]
    exact Matrix.exp_add_of_commute ℝ _ _ (Commute.refl _)
  rw [Matrix.transpose_mul, ((hH.smul t).exp ℝ).eq, he]
  simp only [Matrix.mul_assoc]

theorem frame_exponential_gram_eq_source (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (t : ℝ) :
    (B.val * NormedSpace.exp ℝ (t • H)) * (B.val * NormedSpace.exp ℝ (t • H))ᵀ =
      sourceMatrixCurve (B.val * B.valᵀ) (positiveFrame_gram_posDef B)
        (orthogonalConjugate (framePolarFactor B) H) t := by
  rw [symmetric_frame_exponential_gram B.val H hH t, sourceMatrixCurve,
    ← orthogonalConjugate_smul, matrix_exp_orthogonalConjugate]
  simp only [orthogonalConjugate]
  rw [← Matrix.mul_assoc _ _ (star (framePolarFactor B : Matrix (Fin 3) (Fin 3) ℝ)),
    ← Matrix.mul_assoc]
  rw [frame_polar_decomposition]
  simp only [Matrix.mul_assoc, frame_polar_transpose_decomposition]

def frameLogEnergyCurve (B : PositiveFrame) (H : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) : ℝ :=
  sourceMatrixLogEnergy
    ((B.val * NormedSpace.exp ℝ (t • H)) * (B.val * NormedSpace.exp ℝ (t • H))ᵀ)

theorem frameLogEnergyCurve_eq_source (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    frameLogEnergyCurve B H = sourceMatrixLogEnergyCurve (B.val * B.valᵀ)
      (positiveFrame_gram_posDef B) (orthogonalConjugate (framePolarFactor B) H) := by
  funext t
  exact congrArg sourceMatrixLogEnergy (frame_exponential_gram_eq_source B H hH t)

theorem frameLogEnergyCurve_second_derivative_ge_HS (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    8 * (matrixFullHSNorm H) ^ 2 ≤ deriv (deriv (frameLogEnergyCurve B H)) 0 := by
  rw [frameLogEnergyCurve_eq_source B H hH]
  have h := sourceMatrixLogEnergyCurve_second_derivative_ge_HS _ (positiveFrame_gram_posDef B)
    (orthogonalConjugate (framePolarFactor B) H) (orthogonalConjugate_isSymm _ H hH)
  rwa [matrixFullHSNorm_orthogonalConjugate _ H hH] at h

theorem frameLogEnergyCurve_second_derivative_pos (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (hne : H ≠ 0) :
    0 < deriv (deriv (frameLogEnergyCurve B H)) 0 := by
  have hp : 0 < matrixFullHSNorm H := lt_of_le_of_ne (matrixFullHSNorm_nonneg H)
    (fun h => hne ((matrixFullHSNorm_eq_zero_iff H).mp h.symm))
  exact (mul_pos (by norm_num) (pow_pos hp 2)).trans_le
    (frameLogEnergyCurve_second_derivative_ge_HS B H hH)

end PaperI
