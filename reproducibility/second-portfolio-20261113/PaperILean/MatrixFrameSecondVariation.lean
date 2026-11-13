import PaperILean.TensorFrameVariations
import PaperILean.SecondDerivativeAlgebra

/-! Physical second variation on the actual frame path, I248 and I282.
B need not be symmetric, invertible, or commute with H; n=0 is allowed. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem symmetricFrame_eigenbasis_intertwines_general {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    H * (symmetricFrameEigenbasis H hH : Matrix (Fin n) (Fin n) ℝ) =
      (symmetricFrameEigenbasis H hH : Matrix (Fin n) (Fin n) ℝ) *
        Matrix.diagonal (symmetricFrameEigenvalues H hH) := by
  conv_lhs => arg 1; rw [symmetricFrame_spectral H hH]
  simp only [orthogonalConjugate, Matrix.mul_assoc]
  have hu := unitary.coe_star_mul_self (symmetricFrameEigenbasis H hH)
  change star (symmetricFrameEigenbasis H hH : Matrix (Fin n) (Fin n) ℝ) *
    (symmetricFrameEigenbasis H hH : Matrix (Fin n) (Fin n) ℝ) = 1 at hu
  rw [hu, Matrix.mul_one]

def matrixFrameEnergyCurve {n : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : ℝ :=
  (matrixFullHSNorm (B * NormedSpace.exp ℝ (t • H))) ^ 2

theorem matrixFrameEnergyCurve_eq_weightedSum {n : ℕ}
    (B H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    matrixFrameEnergyCurve B H = fun t => ∑ i : Fin n,
      weightedExponentialSum Finset.univ
        (fun j => ((B * (symmetricFrameEigenbasis H hH : Matrix (Fin n) (Fin n) ℝ)) i j) ^ 2)
        (fun j => 2 * symmetricFrameEigenvalues H hH j) t := by
  funext t
  exact matrixFullHSNorm_exp_eq_sum B H hH t

theorem matrixFrameEnergyCurve_differentiable {n : ℕ}
    (B H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    Differentiable ℝ (matrixFrameEnergyCurve B H) := by
  rw [matrixFrameEnergyCurve_eq_weightedSum B H hH]
  exact Differentiable.sum (fun i _ t => (hasDerivAt_weightedExponentialSum _ _ _ t).differentiableAt)

theorem matrixFrameEnergyCurve_deriv_differentiable {n : ℕ}
    (B H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    Differentiable ℝ (deriv (matrixFrameEnergyCurve B H)) := by
  rw [matrixFrameEnergyCurve_eq_weightedSum B H hH]
  have heq : deriv (fun t => ∑ i : Fin n, weightedExponentialSum Finset.univ
      (fun j => ((B * (symmetricFrameEigenbasis H hH : Matrix (Fin n) (Fin n) ℝ)) i j) ^ 2)
      (fun j => 2 * symmetricFrameEigenvalues H hH j) t) =
      fun t => ∑ i : Fin n, deriv (weightedExponentialSum Finset.univ
        (fun j => ((B * (symmetricFrameEigenbasis H hH : Matrix (Fin n) (Fin n) ℝ)) i j) ^ 2)
        (fun j => 2 * symmetricFrameEigenvalues H hH j)) t := by
    funext t
    exact deriv_sum (fun i _ => (hasDerivAt_weightedExponentialSum _ _ _ t).differentiableAt)
  rw [heq]
  exact Differentiable.sum (fun i _ t => (hasDerivAt_deriv_weightedExponentialSum _ _ _ t).differentiableAt)

theorem matrixFrameEnergyCurve_second_derivative_zero {n : ℕ}
    (B H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    deriv (deriv (matrixFrameEnergyCurve B H)) 0 = 4 * (matrixFullHSNorm (B * H)) ^ 2 := by
  rw [matrixFrameEnergyCurve_eq_weightedSum B H hH,
    deriv2_finset_sum _ _ (fun i _ t => (hasDerivAt_weightedExponentialSum _ _ _ t).differentiableAt)
      (fun i _ t => (hasDerivAt_deriv_weightedExponentialSum _ _ _ t).differentiableAt)]
  simp only [deriv2_weightedExponentialSum, weightedExponentialSum, zero_mul, Real.exp_zero, mul_one]
  rw [← matrixFullHSNorm_right_orthogonal (B * H)
    (symmetricFrameEigenbasis H hH : Matrix (Fin n) (Fin n) ℝ)
    (real_unitary_mul_transpose (symmetricFrameEigenbasis H hH)), Matrix.mul_assoc,
    symmetricFrame_eigenbasis_intertwines_general H hH, ← Matrix.mul_assoc,
    matrixFullHSNorm_mul_diagonal_sq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem matrixFrameEnergyCurve_second_derivative_nonneg {n : ℕ}
    (B H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    0 ≤ deriv (deriv (matrixFrameEnergyCurve B H)) 0 := by
  rw [matrixFrameEnergyCurve_second_derivative_zero B H hH]
  positivity

end PaperI
