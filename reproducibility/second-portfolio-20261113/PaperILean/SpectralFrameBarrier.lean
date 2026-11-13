import PaperILean.ScalarFrameBarrier
import PaperILean.MatrixOrthogonalReduction

/-! Exact spectral identity for the SPD representative in Paper I 246.
Eigenvalues are positive, so real logarithms of their product split exactly. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem matrixFullHSNorm_diagonal_sq {n : ℕ} (s : Fin n → ℝ) :
    (matrixFullHSNorm (Matrix.diagonal s)) ^ 2 = ∑ i, (s i) ^ 2 := by
  rw [← trace_matrix_square_eq_fullHS _ (Matrix.isSymm_diagonal s), pow_two,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp only [Pi.mul_apply, pow_two]

theorem matrixFullHSNorm_sq_eq_sum_eigenvalues_sq {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsHermitian) :
    (matrixFullHSNorm S) ^ 2 = ∑ i, (hS.eigenvalues i) ^ 2 := by
  have hspec : S = orthogonalConjugate hS.eigenvectorUnitary (Matrix.diagonal hS.eigenvalues) := by
    simpa [orthogonalConjugate, Function.comp_def] using hS.spectral_theorem
  conv_lhs => rw [hspec]
  rw [matrixFullHSNorm_orthogonalConjugate _ _ (Matrix.isSymm_diagonal _),
    matrixFullHSNorm_diagonal_sq]

theorem posDef_log_det_eq_sum_log_eigenvalues {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) :
    Real.log S.det = ∑ i, Real.log (hS.isHermitian.eigenvalues i) := by
  rw [hS.isHermitian.det_eq_prod_eigenvalues]
  exact Real.log_prod _ _ (fun i _ => (hS.eigenvalues_pos i).ne')

theorem posDef_matrix_barrier_eq_sum {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) :
    (matrixFullHSNorm S) ^ 2 - 2 * Real.log S.det =
      ∑ i, scalarFrameBarrier (hS.isHermitian.eigenvalues i) := by
  rw [matrixFullHSNorm_sq_eq_sum_eigenvalues_sq S hS.isHermitian,
    posDef_log_det_eq_sum_log_eigenvalues S hS]
  simp only [scalarFrameBarrier, Finset.sum_sub_distrib, Finset.mul_sum]

theorem FrameEnergy_ge_spectral_barrier {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : S.PosDef) :
    (∑ i, scalarFrameBarrier (hS.isHermitian.eigenvalues i)) ≤ FrameEnergy F c lam S := by
  rw [← posDef_matrix_barrier_eq_sum S hS]
  exact FrameEnergy_ge_matrix_barrier F c lam hlam S

theorem FrameEnergy_posDef_ge_three {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : S.PosDef) :
    3 ≤ FrameEnergy F c lam S :=
  (scalarFrameBarrier_sum_ge_card _ hS.eigenvalues_pos).trans
    (FrameEnergy_ge_spectral_barrier F c lam hlam S hS)

theorem FrameEnergy_sublevel_eigenvalue_bounds {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : S.PosDef)
    (M : ℝ) (hM : FrameEnergy F c lam S ≤ M) (i : Fin 3) :
    Real.exp (-M / 2) ≤ hS.isHermitian.eigenvalues i ∧
      hS.isHermitian.eigenvalues i ≤ 1 + Real.sqrt M :=
  scalarFrameBarrier_sum_sublevel_bounds _ hS.eigenvalues_pos M
    ((FrameEnergy_ge_spectral_barrier F c lam hlam S hS).trans hM) i

end PaperI
