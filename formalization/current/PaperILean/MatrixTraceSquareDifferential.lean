import PaperILean.SymmetricMatrixExponential

/-! Actual trace-square calculus for Paper I214-223. Multiplication order is
retained before taking the trace. The symmetric logarithm derivative is the
checked inverse-exponential differential, not an assumed energy formula.
-/

noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

def matrixTraceCLM (n : ℕ) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin n) ℝ ℝ).toContinuousLinearMap

theorem matrixTraceCLM_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    matrixTraceCLM n A = Matrix.trace A := rfl

theorem hasDerivAt_trace_matrix_square {n : ℕ}
    {f : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {K : Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (hf : HasDerivAt f K t) :
    HasDerivAt (fun u => Matrix.trace ((f u) ^ 2))
      (2 * Matrix.trace (f t * K)) t := by
  have hm := hf.mul hf
  have ht := (matrixTraceCLM n).hasFDerivAt.comp_hasDerivAt t hm
  convert ht using 1
  · ext u
    simp only [matrixTraceCLM_apply, pow_two, Function.comp_def]
  · simp only [matrixTraceCLM_apply, Matrix.trace_add]
    rw [Matrix.trace_mul_comm K (f t)]
    ring

def symmetricLogEnergy {n : ℕ} (A : SymmetricMatrix n) : ℝ :=
  sourceMatrixLogEnergy (A : Matrix (Fin n) (Fin n) ℝ)

def symmetricLogEnergyDifferential {n : ℕ} (A : SymmetricMatrix n) :
    SymmetricMatrix n →L[ℝ] ℝ :=
  let L : SymmetricMatrix n →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    (symmetricMatrixIncl n).comp
      ((symmetricMatrixExpDifferentialEquiv (symmetricMatrixLog A)).symm :
        SymmetricMatrix n →L[ℝ] SymmetricMatrix n)
  (matrixTraceCLM n).comp
    ((CFC.log (A : Matrix (Fin n) (Fin n) ℝ)) • L +
      L.smulRight (CFC.log (A : Matrix (Fin n) (Fin n) ℝ)))

theorem symmetricLogEnergyDifferential_apply {n : ℕ}
    (A V : SymmetricMatrix n) :
    symmetricLogEnergyDifferential A V =
      2 * Matrix.trace (CFC.log (A : Matrix (Fin n) (Fin n) ℝ) *
        ((symmetricMatrixExpDifferentialEquiv (symmetricMatrixLog A)).symm V :
          Matrix (Fin n) (Fin n) ℝ)) := by
  simp only [symmetricLogEnergyDifferential, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, symmetricMatrixIncl, Submodule.subtypeL_apply,
    matrixTraceCLM_apply, smul_eq_mul, Matrix.trace_add]
  change Matrix.trace (CFC.log (A : Matrix (Fin n) (Fin n) ℝ) *
      ((symmetricMatrixExpDifferentialEquiv (symmetricMatrixLog A)).symm V :
        Matrix (Fin n) (Fin n) ℝ)) +
    Matrix.trace (((symmetricMatrixExpDifferentialEquiv (symmetricMatrixLog A)).symm V :
      Matrix (Fin n) (Fin n) ℝ) * CFC.log (A : Matrix (Fin n) (Fin n) ℝ)) = _
  rw [Matrix.trace_mul_comm
    ((symmetricMatrixExpDifferentialEquiv (symmetricMatrixLog A)).symm V :
      Matrix (Fin n) (Fin n) ℝ) (CFC.log (A : Matrix (Fin n) (Fin n) ℝ))]
  ring

theorem symmetricLogEnergy_posDef_hasFDerivAt {n : ℕ}
    (A : SymmetricMatrix n) (hA : (A : Matrix (Fin n) (Fin n) ℝ).PosDef) :
    HasFDerivAt symmetricLogEnergy (symmetricLogEnergyDifferential A) A := by
  change HasFDerivAt (fun X : SymmetricMatrix n =>
    Matrix.trace ((CFC.log (X : Matrix (Fin n) (Fin n) ℝ)) ^ 2))
      (symmetricLogEnergyDifferential A) A
  simp only [pow_two]
  have hl := (symmetricMatrixIncl n).hasFDerivAt.comp A
    (symmetricMatrixLog_posDef_hasFDerivAt A hA)
  have hm := hl.mul' hl
  have ht := (matrixTraceCLM n).hasFDerivAt.comp A hm
  simpa only [symmetricLogEnergy, sourceMatrixLogEnergy, symmetricMatrixLog,
    symmetricMatrixOf, symmetricMatrixIncl, Submodule.subtypeL_apply,
    matrixTraceCLM_apply, Function.comp_def, pow_two,
    symmetricLogEnergyDifferential] using ht

end PaperI
