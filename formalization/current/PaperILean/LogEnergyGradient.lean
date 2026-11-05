import PaperILean.LogEnergyFirstDerivative

/-! Actual first Frechet energy gradient used to differentiate the source first
variation. The logarithm differential is not replaced by inverse multiplication;
only its trace pairing is simplified. Alternative exponential-calculus route. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

set_option maxHeartbeats 400000

theorem trace_diagonal_inverse_exp_differential {n : ℕ}
    (a : Fin n → ℝ) (V : SymmetricMatrix n) :
    Matrix.trace (Matrix.diagonal a *
      ((symmetricDiagonalExpDifferentialEquiv a).symm V : Matrix (Fin n) (Fin n) ℝ)) =
    Matrix.trace (Matrix.diagonal a * Matrix.diagonal (fun i => Real.exp (-a i)) *
      (V : Matrix (Fin n) (Fin n) ℝ)) := by
  simp only [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i hi
  change (Matrix.diagonal a * ((symmetricDiagonalExpDifferentialEquiv a).symm V :
      Matrix (Fin n) (Fin n) ℝ)) i i =
    (Matrix.diagonal a * Matrix.diagonal (fun i => Real.exp (-a i)) *
      (V : Matrix (Fin n) (Fin n) ℝ)) i i
  rw [Matrix.diagonal_mul, Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.diagonal_mul]
  change a i * ((diagonalExpDifferentialEquiv a).symm (V : Matrix (Fin n) (Fin n) ℝ) i i) = _
  rw [diagonalExpDifferentialEquiv_symm_apply, expDividedDifference_self, Real.exp_neg]

theorem symmetric_exp_inverse_differential_trace {n : ℕ}
    (X V : SymmetricMatrix n) :
    Matrix.trace ((X : Matrix (Fin n) (Fin n) ℝ) *
      ((symmetricMatrixExpDifferentialEquiv X).symm V : Matrix (Fin n) (Fin n) ℝ)) =
    Matrix.trace ((X : Matrix (Fin n) (Fin n) ℝ) * NormedSpace.exp ℝ (-(X : Matrix (Fin n) (Fin n) ℝ)) *
      (V : Matrix (Fin n) (Fin n) ℝ)) := by
  let hX := (realMatrix_isHermitian_iff_isSymm (X : Matrix (Fin n) (Fin n) ℝ)).mpr X.property
  let U := hX.eigenvectorUnitary
  let a := hX.eigenvalues
  let W := symmetricOrthogonalConjugateEquiv (star U) V
  have hx : (X : Matrix (Fin n) (Fin n) ℝ) = orthogonalConjugate U (Matrix.diagonal a) := by
    exact hX.spectral_theorem
  have hv : (V : Matrix (Fin n) (Fin n) ℝ) = orthogonalConjugate U W := by
    exact congrArg Subtype.val (symmetricOrthogonalConjugate_inverse U V).symm
  have hd : ((symmetricMatrixExpDifferentialEquiv X).symm V : Matrix (Fin n) (Fin n) ℝ) =
      orthogonalConjugate U
        ((symmetricDiagonalExpDifferentialEquiv a).symm W : Matrix (Fin n) (Fin n) ℝ) := by
    rfl
  have hn : -(X : Matrix (Fin n) (Fin n) ℝ) =
      orthogonalConjugate U (Matrix.diagonal (fun i => -a i)) := by
    rw [hx]
    rw [show Matrix.diagonal (fun i => -a i) = -Matrix.diagonal a by ext i j; simp [Matrix.diagonal_apply]; split_ifs <;> simp_all]
    simp only [orthogonalConjugate, Matrix.mul_neg, Matrix.neg_mul]
  rw [hd, hn, hx, matrix_exp_orthogonalConjugate, matrix_exp_diagonal_real, hv,
    ← orthogonalConjugate_mul, trace_orthogonalConjugate,
    ← orthogonalConjugate_mul, ← orthogonalConjugate_mul, trace_orthogonalConjugate]
  exact trace_diagonal_inverse_exp_differential a W

theorem symmetricLogEnergyDifferential_eq_trace_inverse {n : ℕ}
    (A V : SymmetricMatrix n) (hA : (A : Matrix (Fin n) (Fin n) ℝ).PosDef) :
    symmetricLogEnergyDifferential A V =
      2 * Matrix.trace (CFC.log (A : Matrix (Fin n) (Fin n) ℝ) *
        (A : Matrix (Fin n) (Fin n) ℝ)⁻¹ * (V : Matrix (Fin n) (Fin n) ℝ)) := by
  rw [symmetricLogEnergyDifferential_apply]
  have h := symmetric_exp_inverse_differential_trace (symmetricMatrixLog A) V
  change Matrix.trace (CFC.log (A : Matrix (Fin n) (Fin n) ℝ) * _) =
    Matrix.trace (CFC.log (A : Matrix (Fin n) (Fin n) ℝ) *
      NormedSpace.exp ℝ (-CFC.log (A : Matrix (Fin n) (Fin n) ℝ)) * _) at h
  rw [Matrix.exp_neg, sourceMatrix_exp_log _ hA] at h
  rw [h]

theorem hasDerivAt_symmetricLogEnergy_of_hasDerivAt {n : ℕ}
    {f : ℝ → SymmetricMatrix n} {V : SymmetricMatrix n} {t : ℝ}
    (hf : HasDerivAt f V t) (hA : (f t : Matrix (Fin n) (Fin n) ℝ).PosDef) :
    HasDerivAt (fun s => symmetricLogEnergy (f s))
      (2 * Matrix.trace (CFC.log (f t : Matrix (Fin n) (Fin n) ℝ) *
        (f t : Matrix (Fin n) (Fin n) ℝ)⁻¹ * (V : Matrix (Fin n) (Fin n) ℝ))) t := by
  have h := (symmetricLogEnergy_posDef_hasFDerivAt (f t) hA).comp_hasDerivAt t hf
  rwa [symmetricLogEnergyDifferential_eq_trace_inverse _ _ hA] at h

end PaperI
