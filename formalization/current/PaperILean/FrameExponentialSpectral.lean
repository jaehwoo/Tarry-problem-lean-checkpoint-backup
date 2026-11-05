import PaperILean.TensorOrthogonalInvariance
import PaperILean.MatrixOrthogonalReduction
import PaperILean.DiagonalExponentialDifferential
import PaperILean.FrameEnergy

/-! Fixed orthogonal diagonalization of the symmetric direction at Paper I248.
The frame B is arbitrary and need not commute with H. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

def symmetricFrameEigenvalues {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    Fin n → ℝ := ((realMatrix_isHermitian_iff_isSymm H).mpr hH).eigenvalues

def symmetricFrameEigenbasis {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    unitary (Matrix (Fin n) (Fin n) ℝ) :=
  ((realMatrix_isHermitian_iff_isSymm H).mpr hH).eigenvectorUnitary

theorem real_unitary_mul_transpose {n : ℕ} (U : unitary (Matrix (Fin n) (Fin n) ℝ)) :
    (U : Matrix (Fin n) (Fin n) ℝ) * (U : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    unitary.coe_mul_star_self U

theorem real_unitary_transpose_mul {n : ℕ} (U : unitary (Matrix (Fin n) (Fin n) ℝ)) :
    (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (U : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    unitary.coe_star_mul_self U

theorem symmetricFrame_spectral {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    H = orthogonalConjugate (symmetricFrameEigenbasis H hH)
      (Matrix.diagonal (symmetricFrameEigenvalues H hH)) := by
  simpa only [orthogonalConjugate, symmetricFrameEigenbasis, symmetricFrameEigenvalues,
    Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
    ((realMatrix_isHermitian_iff_isSymm H).mpr hH).spectral_theorem

theorem symmetricFrame_trace {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    Matrix.trace H = ∑ i, symmetricFrameEigenvalues H hH i := by
  conv_lhs => rw [symmetricFrame_spectral H hH]
  rw [trace_orthogonalConjugate, Matrix.trace_diagonal]

theorem matrix_exp_symmetricFrame_spectral {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (t : ℝ) :
    NormedSpace.exp ℝ (t • H) = orthogonalConjugate (symmetricFrameEigenbasis H hH)
      (Matrix.diagonal (fun i => Real.exp (t * symmetricFrameEigenvalues H hH i))) := by
  have ht : t • H = orthogonalConjugate (symmetricFrameEigenbasis H hH)
      (Matrix.diagonal (t • symmetricFrameEigenvalues H hH)) := by
    rw [Matrix.diagonal_smul, orthogonalConjugate_smul, ← symmetricFrame_spectral H hH]
  rw [ht, matrix_exp_orthogonalConjugate, matrix_exp_diagonal_real]
  rfl

theorem det_orthogonalConjugate {n : ℕ} (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ) : (orthogonalConjugate U A).det = A.det := by
  have hu := congrArg Matrix.det (unitary.coe_mul_star_self U)
  simp only [Matrix.det_mul, Matrix.det_one] at hu
  change (U : Matrix (Fin n) (Fin n) ℝ).det * (star (U : Matrix (Fin n) (Fin n) ℝ)).det = 1 at hu
  simp only [orthogonalConjugate, Matrix.det_mul]
  calc
    (U : Matrix (Fin n) (Fin n) ℝ).det * A.det * (star (U : Matrix (Fin n) (Fin n) ℝ)).det =
      ((U : Matrix (Fin n) (Fin n) ℝ).det * (star (U : Matrix (Fin n) (Fin n) ℝ)).det) * A.det := by ring
    _ = A.det := by rw [hu, one_mul]

theorem det_exp_symmetric_real {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (t : ℝ) :
    (NormedSpace.exp ℝ (t • H)).det = Real.exp (t * Matrix.trace H) := by
  rw [matrix_exp_symmetricFrame_spectral H hH t, det_orthogonalConjugate,
    Matrix.det_diagonal, symmetricFrame_trace H hH, Finset.mul_sum, Real.exp_sum]

theorem positiveFrame_log_det_exp (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (t : ℝ) :
    Real.log (B.val * NormedSpace.exp ℝ (t • H)).det =
      Real.log B.val.det + t * Matrix.trace H := by
  rw [Matrix.det_mul, det_exp_symmetric_real H hH t,
    Real.log_mul B.property.ne' (Real.exp_pos _).ne', Real.log_exp]

theorem matrixFullHSNorm_mul_diagonal_sq {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    (matrixFullHSNorm (B * Matrix.diagonal d)) ^ 2 = ∑ i, ∑ j, (B i j) ^ 2 * (d j) ^ 2 := by
  simp only [matrixFullHSNorm_sq, Matrix.mul_diagonal, mul_pow]

theorem matrixFullHSNorm_exp_eq_sum {n : ℕ}
    (B H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (t : ℝ) :
    (matrixFullHSNorm (B * NormedSpace.exp ℝ (t • H))) ^ 2 =
      ∑ i, ∑ j, ((B * (symmetricFrameEigenbasis H hH : Matrix (Fin n) (Fin n) ℝ)) i j) ^ 2 *
        Real.exp (t * (2 * symmetricFrameEigenvalues H hH j)) := by
  rw [matrix_exp_symmetricFrame_spectral H hH t]
  unfold orthogonalConjugate
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, matrixFullHSNorm_right_orthogonal _ _
    (by simpa only [Matrix.transpose_transpose] using
      real_unitary_transpose_mul (symmetricFrameEigenbasis H hH)),
    matrixFullHSNorm_mul_diagonal_sq]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Real.exp_nat_mul]
  congr 2
  ring

end PaperI
