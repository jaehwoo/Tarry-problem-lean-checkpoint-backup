import PaperILean.MatrixTraceSquareDifferential
import PaperILean.LogSpectralChainAlgebra

/-! The actual first energy derivative at Paper I223, for every fixed size,
SPD A and symmetric H. Fixed eigenbasis reduction is used without
differentiating that basis. No spectral energy Hessian is assumed.
-/

noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

set_option maxHeartbeats 100000

def symmetricSourceCurve {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (t : ℝ) : SymmetricMatrix n :=
  symmetricMatrixOf (sourceMatrixCurve A hA H t)
    ((realMatrix_isHermitian_iff_isSymm _).mp
      (sourceMatrixCurve_posDef A hA H hH t).isHermitian)

theorem symmetricSourceCurve_coe {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (t : ℝ) :
    (symmetricSourceCurve A hA H hH t : Matrix (Fin n) (Fin n) ℝ) =
      sourceMatrixCurve A hA H t := rfl

theorem sourceMatrixCurve_velocity_isSymm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    (deriv (sourceMatrixCurve A hA H) 0).IsSymm := by
  rw [sourceMatrixCurve_first_derivative_zero]
  have hS : (sourcePositiveSqrt A hA)ᵀ = sourcePositiveSqrt A hA :=
    sourcePositiveSqrt_isSymm A hA
  have hHt : Hᵀ = H := hH
  show ((2 : ℝ) • (sourcePositiveSqrt A hA * H * sourcePositiveSqrt A hA))ᵀ = _
  simp only [Matrix.transpose_smul, Matrix.transpose_mul,
    hS, hHt, Matrix.mul_assoc]

theorem symmetricSourceCurve_velocity_coe {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    ((symmetricMatrixProjection n) (deriv (sourceMatrixCurve A hA H) 0) :
      Matrix (Fin n) (Fin n) ℝ) = deriv (sourceMatrixCurve A hA H) 0 := by
  rw [symmetricMatrixProjection_of_symm _ (sourceMatrixCurve_velocity_isSymm A hA H hH)]
  rfl

theorem symmetricSourceCurve_hasDerivAt_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    HasDerivAt (symmetricSourceCurve A hA H hH)
      ((symmetricMatrixProjection n) (deriv (sourceMatrixCurve A hA H) 0)) 0 := by
  have hc := (hasDerivAt_sourceMatrixCurve A hA H 0).differentiableAt.hasDerivAt
  have hp := (symmetricMatrixProjection n).hasFDerivAt.comp_hasDerivAt 0 hc
  have he : (symmetricMatrixProjection n) ∘ sourceMatrixCurve A hA H =
      symmetricSourceCurve A hA H hH := by
    funext t
    exact symmetricMatrixProjection_of_symm _
      ((realMatrix_isHermitian_iff_isSymm _).mp
        (sourceMatrixCurve_posDef A hA H hH t).isHermitian)
  rw [he] at hp
  exact hp

theorem sourceMatrix_log_exponentialDiagonal {n : ℕ} (a : Fin n → ℝ) :
    CFC.log (exponentialDiagonal a) = Matrix.diagonal a := by
  rw [exponentialDiagonal, ← matrix_exp_diagonal_real]
  exact CFC.log_exp _
    ((realMatrix_isSelfAdjoint_iff_isSymm _).mpr (Matrix.isSymm_diagonal a))

def sourceDiagonalLogVelocity {n : ℕ} (a : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ((symmetricDiagonalExpDifferentialEquiv a).symm
    ((symmetricMatrixProjection n)
      (deriv (sourceMatrixCurve (exponentialDiagonal a) (exponentialDiagonal_posDef a) H) 0)) :
        Matrix (Fin n) (Fin n) ℝ)

theorem sourceDiagonalLogVelocity_diagonal {n : ℕ}
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (i : Fin n) :
    sourceDiagonalLogVelocity a H i i = 2 * H i i := by
  change (diagonalExpDifferentialEquiv a).symm
    ((symmetricMatrixProjection n)
      (deriv (sourceMatrixCurve (exponentialDiagonal a) (exponentialDiagonal_posDef a) H) 0) :
        Matrix (Fin n) (Fin n) ℝ) i i = _
  rw [diagonalExpDifferentialEquiv_symm_apply, expDividedDifference_self,
    symmetricSourceCurve_velocity_coe _ _ H hH,
    sourceMatrixCurve_exponentialDiagonal_first_entry]
  rw [show (a i + a i) / 2 = a i by ring]
  field_simp
  ring

theorem hasDerivAt_log_sourceMatrixCurve_exponentialDiagonal {n : ℕ}
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    HasDerivAt (fun t => CFC.log
      (sourceMatrixCurve (exponentialDiagonal a) (exponentialDiagonal_posDef a) H t))
      (sourceDiagonalLogVelocity a H) 0 := by
  have hc := symmetricSourceCurve_hasDerivAt_zero
    (exponentialDiagonal a) (exponentialDiagonal_posDef a) H hH
  have hz : symmetricMatrixDiagonal (fun i => Real.exp (a i)) =
      symmetricSourceCurve (exponentialDiagonal a) (exponentialDiagonal_posDef a) H hH 0 := by
    apply Subtype.ext
    change exponentialDiagonal a = sourceMatrixCurve _ _ _ 0
    exact (sourceMatrixCurve_zero _ _ H).symm
  have hl := (symmetricMatrixLog_diagonal_hasStrictFDerivAt a).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hc hz
  have hi := (symmetricMatrixIncl n).hasFDerivAt.comp_hasDerivAt 0 hl
  change HasDerivAt (fun t => CFC.log
    (sourceMatrixCurve (exponentialDiagonal a) (exponentialDiagonal_posDef a) H t))
      (sourceDiagonalLogVelocity a H) 0 at hi
  exact hi

theorem hasDerivAt_sourceMatrixLogEnergyCurve_exponentialDiagonal {n : ℕ}
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    HasDerivAt (sourceMatrixLogEnergyCurve (exponentialDiagonal a)
      (exponentialDiagonal_posDef a) H)
      (4 * Matrix.trace (Matrix.diagonal a * H)) 0 := by
  have h := hasDerivAt_trace_matrix_square
    (hasDerivAt_log_sourceMatrixCurve_exponentialDiagonal a H hH)
  rw [sourceMatrixCurve_zero, sourceMatrix_log_exponentialDiagonal] at h
  have he : 2 * Matrix.trace (Matrix.diagonal a * sourceDiagonalLogVelocity a H) =
      4 * Matrix.trace (Matrix.diagonal a * H) := by
    simp only [Matrix.trace, Matrix.diagonal_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change 2 * ((Matrix.diagonal a * sourceDiagonalLogVelocity a H) i i) =
      4 * ((Matrix.diagonal a * H) i i)
    rw [Matrix.diagonal_mul, Matrix.diagonal_mul,
      sourceDiagonalLogVelocity_diagonal a H hH i]
    ring
  rw [he] at h
  exact h

theorem hasDerivAt_sourceMatrixLogEnergyCurve_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    HasDerivAt (sourceMatrixLogEnergyCurve A hA H)
      (4 * Matrix.trace (CFC.log A * H)) 0 := by
  let a : Fin n → ℝ := fun i => Real.log (hA.isHermitian.eigenvalues i)
  let U := hA.isHermitian.eigenvectorUnitary
  let H' := orthogonalConjugate (star U) H
  have hH' : H'.IsSymm := orthogonalConjugate_isSymm (star U) H hH
  have he : exponentialDiagonal a = Matrix.diagonal hA.isHermitian.eigenvalues := by
    unfold exponentialDiagonal
    apply congrArg Matrix.diagonal
    funext i
    exact Real.exp_log (hA.eigenvalues_pos i)
  have h := hasDerivAt_sourceMatrixLogEnergyCurve_exponentialDiagonal a H' hH'
  have hf : sourceMatrixLogEnergyCurve A hA H =
      sourceMatrixLogEnergyCurve (exponentialDiagonal a) (exponentialDiagonal_posDef a) H' := by
    funext t
    simpa only [he, H', U] using sourceMatrixLogEnergyCurve_eigenbasis A hA H hH t
  have hd : CFC.log (orthogonalConjugate (star U) A) = Matrix.diagonal a := by
    rw [sourceMatrix_eigenbasis_diagonal A hA, ← he, sourceMatrix_log_exponentialDiagonal]
  have ht : Matrix.trace (Matrix.diagonal a * H') = Matrix.trace (CFC.log A * H) := by
    rw [← hd, matrix_log_orthogonalConjugate (star U) A hA]
    change Matrix.trace (orthogonalConjugate (star U) (CFC.log A) *
      orthogonalConjugate (star U) H) = _
    rw [← orthogonalConjugate_mul, trace_orthogonalConjugate]
  rw [← hf, ht] at h
  exact h

theorem sourceMatrixLogEnergyCurve_first_derivative_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    deriv (sourceMatrixLogEnergyCurve A hA H) 0 = 4 * Matrix.trace (CFC.log A * H) :=
  (hasDerivAt_sourceMatrixLogEnergyCurve_zero A hA H hH).deriv

end PaperI
