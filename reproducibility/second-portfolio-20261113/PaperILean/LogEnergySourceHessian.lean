import PaperILean.LogEnergyGradient

/-! Source calculus for the matrix logarithm lemma. Constant right generator,
actual all-time first variation, and derivative of that actual variation. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI
set_option maxHeartbeats 400000

def sourceRightGenerator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (H : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (sourcePositiveSqrt A hA)⁻¹ * H * sourcePositiveSqrt A hA

theorem sourceMatrixCurve_velocity_right_generator {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    deriv (sourceMatrixCurve A hA H) t =
      (2 : ℝ) • (sourceMatrixCurve A hA H t * sourceRightGenerator A hA H) := by
  have hi := Matrix.mul_nonsing_inv (sourcePositiveSqrt A hA)
    ((Matrix.isUnit_iff_isUnit_det _).mp (sourcePositiveSqrt_isUnit A hA))
  rw [deriv_sourceMatrixCurve]
  simp only [sourceMatrixCurve, sourceRightGenerator, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (sourcePositiveSqrt A hA) (sourcePositiveSqrt A hA)⁻¹, hi, one_mul]

theorem symmetricSourceCurve_hasDerivAt {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (t : ℝ) :
    HasDerivAt (symmetricSourceCurve A hA H hH)
      ((symmetricMatrixProjection n) (deriv (sourceMatrixCurve A hA H) t)) t := by
  have hc := (hasDerivAt_sourceMatrixCurve A hA H t).differentiableAt.hasDerivAt
  have hp := (symmetricMatrixProjection n).hasFDerivAt.comp_hasDerivAt t hc
  have he : (symmetricMatrixProjection n) ∘ sourceMatrixCurve A hA H =
      symmetricSourceCurve A hA H hH := by
    funext u
    exact symmetricMatrixProjection_of_symm _
      ((realMatrix_isHermitian_iff_isSymm _).mp
        (sourceMatrixCurve_posDef A hA H hH u).isHermitian)
  rw [he] at hp
  exact hp

theorem symmetricSourceCurve_derivative_coe {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (t : ℝ) :
    ((symmetricMatrixProjection n) (deriv (sourceMatrixCurve A hA H) t) :
      Matrix (Fin n) (Fin n) ℝ) = deriv (sourceMatrixCurve A hA H) t := by
  have h := (symmetricMatrixIncl n).hasFDerivAt.comp_hasDerivAt t
    (symmetricSourceCurve_hasDerivAt A hA H hH t)
  exact h.unique ((hasDerivAt_sourceMatrixCurve A hA H t).differentiableAt.hasDerivAt)

theorem hasDerivAt_sourceMatrixLogEnergyCurve {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (t : ℝ) :
    HasDerivAt (sourceMatrixLogEnergyCurve A hA H)
      (4 * Matrix.trace (CFC.log (sourceMatrixCurve A hA H t) * sourceRightGenerator A hA H)) t := by
  have hp := sourceMatrixCurve_posDef A hA H hH t
  have hi := Matrix.nonsing_inv_mul (sourceMatrixCurve A hA H t)
    ((Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit)
  have h := hasDerivAt_symmetricLogEnergy_of_hasDerivAt
    (symmetricSourceCurve_hasDerivAt A hA H hH t) hp
  change HasDerivAt (sourceMatrixLogEnergyCurve A hA H)
    (2 * Matrix.trace (CFC.log (sourceMatrixCurve A hA H t) *
      (sourceMatrixCurve A hA H t)⁻¹ *
      ((symmetricMatrixProjection n) (deriv (sourceMatrixCurve A hA H) t) :
        Matrix (Fin n) (Fin n) ℝ))) t at h
  rw [symmetricSourceCurve_derivative_coe A hA H hH,
    sourceMatrixCurve_velocity_right_generator, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul] at h
  simp only [Matrix.mul_assoc] at h
  rw [← Matrix.mul_assoc (sourceMatrixCurve A hA H t)⁻¹ (sourceMatrixCurve A hA H t),
    hi, one_mul] at h
  convert h using 1 <;> ring

theorem sourceMatrixLogEnergyCurve_deriv {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (t : ℝ) :
    deriv (sourceMatrixLogEnergyCurve A hA H) t =
      4 * Matrix.trace (CFC.log (sourceMatrixCurve A hA H t) * sourceRightGenerator A hA H) :=
  (hasDerivAt_sourceMatrixLogEnergyCurve A hA H hH t).deriv

theorem hasDerivAt_deriv_logEnergy_exponentialDiagonal_trace {n : ℕ}
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    HasDerivAt (deriv (sourceMatrixLogEnergyCurve (exponentialDiagonal a)
      (exponentialDiagonal_posDef a) H))
      (4 * Matrix.trace (sourceDiagonalLogVelocity a H *
        sourceRightGenerator (exponentialDiagonal a) (exponentialDiagonal_posDef a) H)) 0 := by
  have hl := (hasDerivAt_log_sourceMatrixCurve_exponentialDiagonal a H hH).mul_const
    (sourceRightGenerator (exponentialDiagonal a) (exponentialDiagonal_posDef a) H)
  have ht := ((matrixTraceCLM n).hasFDerivAt.comp_hasDerivAt 0 hl).const_mul 4
  have he : deriv (sourceMatrixLogEnergyCurve (exponentialDiagonal a)
      (exponentialDiagonal_posDef a) H) = fun t =>
        4 * Matrix.trace (CFC.log (sourceMatrixCurve (exponentialDiagonal a)
          (exponentialDiagonal_posDef a) H t) *
            sourceRightGenerator (exponentialDiagonal a) (exponentialDiagonal_posDef a) H) :=
    funext (sourceMatrixLogEnergyCurve_deriv _ _ H hH)
  rw [he]
  exact ht

end PaperI
