import PaperILean.MatrixExponentialCurve

/-! Fixed orthogonal reduction of the actual source energy curve214-223.
All real orthogonal matrices and symmetric directions are permitted, including
repeated eigenvalues. No moving eigenbasis is differentiated. Neither the
general first derivative nor the spectral Hessian is assumed or proved here.
-/

noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

set_option maxHeartbeats 800000

def orthogonalConjugate {n : ℕ} (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (U : Matrix (Fin n) (Fin n) ℝ) * X * star (U : Matrix (Fin n) (Fin n) ℝ)

theorem orthogonalConjugate_mul {n : ℕ} (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    orthogonalConjugate U (X * Y) = orthogonalConjugate U X * orthogonalConjugate U Y := by
  simp only [orthogonalConjugate, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (U : Matrix (Fin n) (Fin n) ℝ))
      (U : Matrix (Fin n) (Fin n) ℝ),
    unitary.coe_star_mul_self, one_mul]

theorem orthogonalConjugate_smul {n : ℕ} (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (c : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    orthogonalConjugate U (c • X) = c • orthogonalConjugate U X := by
  simp [orthogonalConjugate, Matrix.mul_smul, Matrix.smul_mul]

theorem orthogonalConjugate_star_inverse {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ)) (X : Matrix (Fin n) (Fin n) ℝ) :
    orthogonalConjugate (star U) (orthogonalConjugate U X) = X := by
  simp only [orthogonalConjugate, unitary.coe_star, star_star, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (U : Matrix (Fin n) (Fin n) ℝ))
      (U : Matrix (Fin n) (Fin n) ℝ),
    unitary.coe_star_mul_self, one_mul, mul_one]

theorem orthogonalConjugate_isSymm {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    (orthogonalConjugate U H).IsSymm :=
  (realMatrix_isSelfAdjoint_iff_isSymm _).mp
    (((realMatrix_isSelfAdjoint_iff_isSymm H).mpr hH).conjugate U)

theorem orthogonalConjugate_posDef {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    (orthogonalConjugate U A).PosDef := by
  have hu : IsUnit (star (U : Matrix (Fin n) (Fin n) ℝ)) :=
    (unitary.toUnits (star U)).isUnit
  simpa only [orthogonalConjugate, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose] using
    hA.conjTranspose_mul_mul_same (B := star (U : Matrix (Fin n) (Fin n) ℝ))
      (Matrix.mulVec_injective_iff_isUnit.mpr hu)

theorem sourcePositiveSqrt_orthogonalConjugate {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    sourcePositiveSqrt (orthogonalConjugate U A) (orthogonalConjugate_posDef U A hA) =
      orthogonalConjugate U (sourcePositiveSqrt A hA) := by
  have hp : (orthogonalConjugate U (sourcePositiveSqrt A hA)).PosSemidef :=
    hA.posSemidef.posSemidef_sqrt.mul_mul_conjTranspose_same
      (U : Matrix (Fin n) (Fin n) ℝ)
  exact (hp.eq_sqrt_of_sq_eq (orthogonalConjugate_posDef U A hA).posSemidef
    (by rw [pow_two, ← orthogonalConjugate_mul, sourcePositiveSqrt_mul_self])).symm

theorem matrix_exp_orthogonalConjugate {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (X : Matrix (Fin n) (Fin n) ℝ) :
    NormedSpace.exp ℝ (orthogonalConjugate U X) =
      orthogonalConjugate U (NormedSpace.exp ℝ X) :=
  NormedSpace.exp_units_conj ℝ (unitary.toUnits U) X

theorem matrix_log_orthogonalConjugate {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    CFC.log (orthogonalConjugate U A) = orthogonalConjugate U (CFC.log A) := by
  have hs : IsSelfAdjoint (orthogonalConjugate U (CFC.log A)) :=
    (IsSelfAdjoint.log (a := A)).conjugate (U : Matrix (Fin n) (Fin n) ℝ)
  have he : NormedSpace.exp ℝ (orthogonalConjugate U (CFC.log A)) =
      orthogonalConjugate U A := by
    rw [matrix_exp_orthogonalConjugate, sourceMatrix_exp_log A hA]
  rw [← he, CFC.log_exp _ hs]

theorem trace_orthogonalConjugate {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (orthogonalConjugate U X) = Matrix.trace X := by
  rw [orthogonalConjugate, Matrix.trace_mul_cycle, unitary.coe_star_mul_self, one_mul]

theorem matrixFullHSNorm_orthogonalConjugate {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    matrixFullHSNorm (orthogonalConjugate U H) = matrixFullHSNorm H := by
  have he : (matrixFullHSNorm (orthogonalConjugate U H)) ^ 2 = (matrixFullHSNorm H) ^ 2 := by
    rw [← trace_matrix_square_eq_fullHS _ (orthogonalConjugate_isSymm U H hH),
      ← trace_matrix_square_eq_fullHS H hH, pow_two, pow_two,
      ← orthogonalConjugate_mul, trace_orthogonalConjugate]
  nlinarith [matrixFullHSNorm_nonneg (orthogonalConjugate U H), matrixFullHSNorm_nonneg H]

theorem sourceMatrixCurve_orthogonalConjugate {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    sourceMatrixCurve (orthogonalConjugate U A) (orthogonalConjugate_posDef U A hA)
      (orthogonalConjugate U H) t = orthogonalConjugate U (sourceMatrixCurve A hA H t) := by
  rw [sourceMatrixCurve, sourcePositiveSqrt_orthogonalConjugate U A hA]
  simp only [sourceMatrixCurve,
    ← orthogonalConjugate_smul, matrix_exp_orthogonalConjugate, ← orthogonalConjugate_mul]

theorem sourceMatrixLogEnergy_orthogonalConjugate {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    sourceMatrixLogEnergy (orthogonalConjugate U A) = sourceMatrixLogEnergy A := by
  simp only [sourceMatrixLogEnergy, matrix_log_orthogonalConjugate U A hA, pow_two,
    ← orthogonalConjugate_mul, trace_orthogonalConjugate]

theorem sourceMatrixLogEnergyCurve_orthogonalConjugate {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (t : ℝ) :
    sourceMatrixLogEnergyCurve (orthogonalConjugate U A) (orthogonalConjugate_posDef U A hA)
      (orthogonalConjugate U H) t = sourceMatrixLogEnergyCurve A hA H t := by
  rw [sourceMatrixLogEnergyCurve, sourceMatrixCurve_orthogonalConjugate,
    sourceMatrixLogEnergy_orthogonalConjugate U _ (sourceMatrixCurve_posDef A hA H hH t)]
  rfl

theorem sourceMatrix_eigenbasis_diagonal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    orthogonalConjugate (star hA.isHermitian.eigenvectorUnitary) A =
      Matrix.diagonal hA.isHermitian.eigenvalues := by
  simpa [orthogonalConjugate, Function.comp_def] using hA.isHermitian.star_mul_self_mul_eq_diagonal

theorem sourceMatrix_eigenbasis_diagonal_posDef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    (Matrix.diagonal hA.isHermitian.eigenvalues).PosDef := by
  rw [← sourceMatrix_eigenbasis_diagonal A hA]
  exact orthogonalConjugate_posDef _ A hA

theorem sourceMatrixLogEnergyCurve_eigenbasis {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (t : ℝ) :
    sourceMatrixLogEnergyCurve A hA H t =
      sourceMatrixLogEnergyCurve (Matrix.diagonal hA.isHermitian.eigenvalues)
        (sourceMatrix_eigenbasis_diagonal_posDef A hA)
        (orthogonalConjugate (star hA.isHermitian.eigenvectorUnitary) H) t := by
  have he := sourceMatrixLogEnergyCurve_orthogonalConjugate
    (star hA.isHermitian.eigenvectorUnitary) A hA H hH t
  simpa only [sourceMatrix_eigenbasis_diagonal A hA] using he.symm

end PaperI
