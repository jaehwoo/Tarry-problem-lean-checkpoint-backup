import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import PaperILean.SpectralHessianForm

/-! Actual real-matrix model of Paper I214-223.
Positive definiteness and the positive square root are supplied by the fixed
source. No matrix derivative/Hessian identity is assumed. Matrix.L2OpNorm is
used only for functional calculus/calculus; the source HS norm remains the
explicit full ordered-entry norm from SpectralHessianForm.
-/

noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem realMatrix_isHermitian_iff_isSymm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : A.IsHermitian ↔ A.IsSymm := by
  constructor
  · intro h
    show Aᵀ = A
    ext i j
    simpa using h.apply i j
  · intro h
    exact Matrix.IsHermitian.ext (fun i j => by simpa using h.apply i j)

theorem realMatrix_isSelfAdjoint_iff_isSymm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : IsSelfAdjoint A ↔ A.IsSymm := by
  change A.IsHermitian ↔ A.IsSymm
  exact realMatrix_isHermitian_iff_isSymm A

def sourcePositiveSqrt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) : Matrix (Fin n) (Fin n) ℝ := hA.posSemidef.sqrt

def sourceMatrixCurve {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  sourcePositiveSqrt A hA * NormedSpace.exp ℝ ((2 * t) • H) * sourcePositiveSqrt A hA

def sourceMatrixLogEnergy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace ((CFC.log A) ^ 2)

def sourceMatrixLogEnergyCurve {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : ℝ :=
  sourceMatrixLogEnergy (sourceMatrixCurve A hA H t)

theorem sourcePositiveSqrt_mul_self {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    sourcePositiveSqrt A hA * sourcePositiveSqrt A hA = A :=
  hA.posSemidef.sqrt_mul_self

theorem sourcePositiveSqrt_isHermitian {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    (sourcePositiveSqrt A hA).IsHermitian := hA.posSemidef.posSemidef_sqrt.isHermitian

theorem sourcePositiveSqrt_isSymm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    (sourcePositiveSqrt A hA).IsSymm :=
  (realMatrix_isHermitian_iff_isSymm _).mp (sourcePositiveSqrt_isHermitian A hA)

theorem sourcePositiveSqrt_isUnit {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    IsUnit (sourcePositiveSqrt A hA) := by
  apply (isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [pow_two, sourcePositiveSqrt_mul_self A hA]
  exact hA.isUnit

theorem sourceMatrixCurve_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) : sourceMatrixCurve A hA H 0 = A := by
  simp only [sourceMatrixCurve, mul_zero, zero_smul, NormedSpace.exp_zero, mul_one]
  exact sourcePositiveSqrt_mul_self A hA

theorem symmetric_matrix_exp_posDef {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    (NormedSpace.exp ℝ H).PosDef := by
  let K : Matrix (Fin n) (Fin n) ℝ := (1 / 2 : ℝ) • H
  have hsum : K + K = H := by
    ext i j
    simp only [K, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have he : NormedSpace.exp ℝ H = NormedSpace.exp ℝ K * NormedSpace.exp ℝ K := by
    rw [← hsum]
    exact Matrix.exp_add_of_commute ℝ K K (Commute.refl K)
  have hE : (NormedSpace.exp ℝ K).IsHermitian :=
    (realMatrix_isHermitian_iff_isSymm _).mpr ((hH.smul (1 / 2 : ℝ)).exp ℝ)
  have hp := (Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef).conjTranspose_mul_mul_same
    (B := NormedSpace.exp ℝ K) (Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.isUnit_exp ℝ K))
  rw [he]
  simpa only [mul_one, hE.eq] using hp

theorem sourceMatrixCurve_posDef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (t : ℝ) :
    (sourceMatrixCurve A hA H t).PosDef := by
  have he := symmetric_matrix_exp_posDef ((2 * t) • H) (hH.smul (2 * t))
  have hp := he.conjTranspose_mul_mul_same (B := sourcePositiveSqrt A hA)
    (Matrix.mulVec_injective_iff_isUnit.mpr (sourcePositiveSqrt_isUnit A hA))
  simpa only [(sourcePositiveSqrt_isHermitian A hA).eq, sourceMatrixCurve] using hp

theorem posDef_real_spectrum_pos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∀ x ∈ spectrum ℝ A, 0 < x := by
  intro x hx
  rw [hA.isHermitian.eigenvalues_eq_spectrum_real] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hA.eigenvalues_pos i

theorem sourceMatrix_exp_log {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    NormedSpace.exp ℝ (CFC.log A) = A :=
  CFC.exp_log A (posDef_real_spectrum_pos A hA) hA.isHermitian.isSelfAdjoint

theorem sourceMatrix_log_eq_spectral {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    CFC.log A =
      (hA.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
        Matrix.diagonal (fun i => Real.log (hA.isHermitian.eigenvalues i)) *
        star (hA.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
  simpa [CFC.log, Matrix.IsHermitian.cfc, Function.comp_def] using hA.isHermitian.cfc_eq Real.log

theorem trace_matrix_square_eq_fullHS {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    Matrix.trace (H ^ 2) = (matrixFullHSNorm H) ^ 2 := by
  rw [matrixFullHSNorm_sq]
  simp only [Matrix.trace, pow_two, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change (∑ j, H i j * H j i) = ∑ j, H i j * H i j
  apply Finset.sum_congr rfl
  intro j hj
  rw [hH.apply i j]

theorem sourceMatrixLogEnergy_eq_fullHS {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    sourceMatrixLogEnergy A = (matrixFullHSNorm (CFC.log A)) ^ 2 := by
  apply trace_matrix_square_eq_fullHS
  exact (realMatrix_isSelfAdjoint_iff_isSymm _).mp (IsSelfAdjoint.log (a := A))

theorem sourceMatrixLogEnergy_nonneg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ sourceMatrixLogEnergy A := by
  rw [sourceMatrixLogEnergy_eq_fullHS]
  exact sq_nonneg _

end PaperI

