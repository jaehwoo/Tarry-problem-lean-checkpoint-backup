import PaperILean.MatrixOrthogonalReduction
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! A noncommutative route toward the spectral derivative prerequisite at214-223.
The ambient exponential is analytic in the genuine matrix Banach algebra.
No commuting ring instance is imposed. The CFC logarithm is not differentiated
on the ambient nonsymmetric space. This unit identifies actual exponential
derivatives on commuting and commutator directions.
-/

noncomputable section
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

def matrixExpDifferential {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  fderiv ℝ (NormedSpace.exp ℝ) X

theorem matrix_exp_hasFDerivAt {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) :
    HasFDerivAt (NormedSpace.exp ℝ) (matrixExpDifferential X) X :=
  (NormedSpace.exp_analytic (𝕂 := ℝ) X).differentiableAt.hasFDerivAt

theorem matrix_exp_hasStrictFDerivAt {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) :
    HasStrictFDerivAt (NormedSpace.exp ℝ) (matrixExpDifferential X) X :=
  (NormedSpace.exp_analytic (𝕂 := ℝ) X).hasStrictFDerivAt

theorem matrixExpDifferential_commuting_direction {n : ℕ}
    (X V : Matrix (Fin n) (Fin n) ℝ) (hXV : Commute X V) :
    matrixExpDifferential X V = NormedSpace.exp ℝ X * V := by
  have he (t : ℝ) : NormedSpace.exp ℝ (X + t • V) =
      NormedSpace.exp ℝ X * NormedSpace.exp ℝ (t • V) :=
    NormedSpace.exp_add_of_commute (hXV.smul_right t)
  have hc : HasDerivAt (fun t : ℝ => X + t • V) V 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const V).const_add X
  have h₁ := (matrix_exp_hasFDerivAt X).comp_hasDerivAt_of_eq 0 hc (by simp)
  have h₂ : HasDerivAt (fun t : ℝ => NormedSpace.exp ℝ (X + t • V))
      (NormedSpace.exp ℝ X * V) 0 := by
    simpa only [he, zero_smul, NormedSpace.exp_zero, one_mul] using
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) V (0 : ℝ)).const_mul (NormedSpace.exp ℝ X)
  exact h₁.unique h₂

theorem matrixExpDifferential_commutator_direction {n : ℕ}
    (X K : Matrix (Fin n) (Fin n) ℝ) :
    matrixExpDifferential X (K * X - X * K) =
      K * NormedSpace.exp ℝ X - NormedSpace.exp ℝ X * K := by
  let c : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t =>
    NormedSpace.exp ℝ (t • K) * X * NormedSpace.exp ℝ (t • (-K))
  have he (t : ℝ) : NormedSpace.exp ℝ (c t) =
      NormedSpace.exp ℝ (t • K) * NormedSpace.exp ℝ X *
        NormedSpace.exp ℝ (t • (-K)) := by
    have hn : t • (-K) = -(t • K) := smul_neg t K
    simpa only [c, hn, Matrix.exp_neg] using
      Matrix.exp_conj ℝ (NormedSpace.exp ℝ (t • K)) X (Matrix.isUnit_exp ℝ _)
  have hp := hasDerivAt_exp_smul_const (𝕂 := ℝ) K (0 : ℝ)
  have hm := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-K) (0 : ℝ)
  have hc : HasDerivAt c (K * X - X * K) 0 := by
    simpa only [c, zero_smul, NormedSpace.exp_zero, one_mul, mul_one,
      mul_neg, sub_eq_add_neg] using (hp.mul_const X).mul hm
  have hc0 : c 0 = X := by simp [c]
  have h₁ := (matrix_exp_hasFDerivAt X).comp_hasDerivAt_of_eq 0 hc hc0.symm
  have h₂ : HasDerivAt (fun t : ℝ => NormedSpace.exp ℝ (c t))
      (K * NormedSpace.exp ℝ X - NormedSpace.exp ℝ X * K) 0 := by
    simpa only [he, zero_smul, NormedSpace.exp_zero, one_mul, mul_one,
      mul_neg, sub_eq_add_neg] using (hp.mul_const (NormedSpace.exp ℝ X)).mul hm
  exact h₁.unique h₂

end PaperI
