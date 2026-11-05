import PaperILean.TensorOrthogonalInvariance
import PaperILean.ScalarLogEnergy

/-! The exact energy at Paper I 205-212. The total real-valued expression
is used only on positive-determinant frames for the geometric problem.
The tensor sum is over every order 2 <= r <= k. -/

noncomputable section
open scoped BigOperators Matrix
namespace PaperI

def FrameEnergy {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (lam : ℝ) (B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (matrixFullHSNorm B) ^ 2 +
    (∑ r ∈ Finset.Icc 2 k, (jetTensorHSNorm F c B r) ^ 2) -
    2 * Real.log B.det + lam * sourceMatrixLogEnergy (B * Bᵀ)

def sourceFrameEnergy {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (CX C0 R : ℝ) (B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  FrameEnergy F c (sourceRegularization CX C0 R) B

abbrev PositiveFrame := {B : Matrix (Fin 3) (Fin 3) ℝ // 0 < B.det}

theorem frameGram_right_orthogonal {n : ℕ}
    (B Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q * Qᵀ = 1) :
    (B * Q) * (B * Q)ᵀ = B * Bᵀ := by
  rw [Matrix.transpose_mul]
  calc
    B * Q * (Qᵀ * Bᵀ) = B * (Q * Qᵀ) * Bᵀ := by simp only [Matrix.mul_assoc]
    _ = B * Bᵀ := by rw [hQ, mul_one]

theorem positiveDet_right_specialOrthogonal
    (B Q : Matrix (Fin 3) (Fin 3) ℝ) (hB : 0 < B.det) (hdet : Q.det = 1) :
    0 < (B * Q).det := by simpa [Matrix.det_mul, hdet] using hB

theorem FrameEnergy_right_specialOrthogonal {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : Q * Qᵀ = 1) (hdet : Q.det = 1) :
    FrameEnergy F c lam (B * Q) = FrameEnergy F c lam B := by
  simp only [FrameEnergy, matrixFullHSNorm_right_orthogonal B Q hQ,
    jetTensorHSNorm_right_orthogonal F c B Q hQ,
    frameGram_right_orthogonal B Q hQ, Matrix.det_mul, hdet, mul_one]

theorem sourceFrameEnergy_right_specialOrthogonal {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (CX C0 R : ℝ) (B Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : Q * Qᵀ = 1) (hdet : Q.det = 1) :
    sourceFrameEnergy F c CX C0 R (B * Q) = sourceFrameEnergy F c CX C0 R B :=
  FrameEnergy_right_specialOrthogonal F c _ B Q hQ hdet

theorem FrameEnergy_ge_matrix_barrier {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam)
    (B : Matrix (Fin 3) (Fin 3) ℝ) :
    (matrixFullHSNorm B) ^ 2 - 2 * Real.log B.det ≤ FrameEnergy F c lam B := by
  have ht : 0 ≤ ∑ r ∈ Finset.Icc 2 k, (jetTensorHSNorm F c B r) ^ 2 :=
    Finset.sum_nonneg (fun r _ => sq_nonneg _)
  have hl := mul_nonneg hlam (sourceMatrixLogEnergy_nonneg (B * Bᵀ))
  unfold FrameEnergy
  linarith

theorem sourceFrameEnergy_ge_matrix_barrier {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (CX C0 R : ℝ) (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) (hR : 2 ≤ R)
    (B : Matrix (Fin 3) (Fin 3) ℝ) :
    (matrixFullHSNorm B) ^ 2 - 2 * Real.log B.det ≤ sourceFrameEnergy F c CX C0 R B :=
  FrameEnergy_ge_matrix_barrier F c _ (sourceRegularization_pos CX C0 R hCX hC0 hR).le B

theorem positiveFrame_isUnit (B : PositiveFrame) : IsUnit (B : Matrix (Fin 3) (Fin 3) ℝ) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr B.property.ne')

theorem positiveFrame_gram_posDef (B : PositiveFrame) :
    ((B : Matrix (Fin 3) (Fin 3) ℝ) * (B : Matrix (Fin 3) (Fin 3) ℝ)ᵀ).PosDef := by
  have hi : IsUnit ((B : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    simpa only [Matrix.det_transpose] using (isUnit_iff_ne_zero.mpr B.property.ne')
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose, mul_one] using
    (Matrix.PosDef.one : (1 : Matrix (Fin 3) (Fin 3) ℝ).PosDef).conjTranspose_mul_mul_same
      (B := (B : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) (Matrix.mulVec_injective_iff_isUnit.mpr hi)

end PaperI
