import PaperILean.MatrixLogEnergyModel
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Actual first/second matrix curve derivatives in the proof at Paper I223.
The positive square root is the source object, held fixed as t varies.
Multiplication order is retained for noncommuting A,H; no log-energy derivative
or spectral Hessian formula is assumed here.
-/

noncomputable section
open scoped Matrix.L2OpNorm
namespace PaperI

theorem hasDerivAt_sourceMatrixExponential {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ℝ ((2 * u) • H))
      (NormedSpace.exp ℝ ((2 * t) • H) * ((2 : ℝ) • H)) t := by
  simpa only [smul_smul, mul_comm] using
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) ((2 : ℝ) • H) t)

theorem hasDerivAt_sourceMatrixCurve {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (sourceMatrixCurve A hA H)
      (sourcePositiveSqrt A hA *
        (NormedSpace.exp ℝ ((2 * t) • H) * ((2 : ℝ) • H)) * sourcePositiveSqrt A hA) t :=
  ((hasDerivAt_sourceMatrixExponential H t).const_mul (sourcePositiveSqrt A hA)).mul_const
    (sourcePositiveSqrt A hA)

theorem deriv_sourceMatrixCurve {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    deriv (sourceMatrixCurve A hA H) t =
      sourcePositiveSqrt A hA *
        (NormedSpace.exp ℝ ((2 * t) • H) * ((2 : ℝ) • H)) * sourcePositiveSqrt A hA :=
  (hasDerivAt_sourceMatrixCurve A hA H t).deriv

theorem sourceMatrixCurve_first_derivative_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) :
    deriv (sourceMatrixCurve A hA H) 0 =
      (2 : ℝ) • (sourcePositiveSqrt A hA * H * sourcePositiveSqrt A hA) := by
  rw [deriv_sourceMatrixCurve]
  simp only [mul_zero, zero_smul, NormedSpace.exp_zero, one_mul,
    mul_smul_comm, smul_mul_assoc]

theorem hasDerivAt_deriv_sourceMatrixCurve {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (deriv (sourceMatrixCurve A hA H))
      (sourcePositiveSqrt A hA *
        ((NormedSpace.exp ℝ ((2 * t) • H) * ((2 : ℝ) • H)) * ((2 : ℝ) • H)) *
          sourcePositiveSqrt A hA) t := by
  have he : deriv (sourceMatrixCurve A hA H) =
      (fun u : ℝ => sourcePositiveSqrt A hA *
        (NormedSpace.exp ℝ ((2 * u) • H) * ((2 : ℝ) • H)) * sourcePositiveSqrt A hA) :=
    funext (deriv_sourceMatrixCurve A hA H)
  rw [he]
  exact (((hasDerivAt_sourceMatrixExponential H t).mul_const ((2 : ℝ) • H)).const_mul
    (sourcePositiveSqrt A hA)).mul_const (sourcePositiveSqrt A hA)

theorem deriv_deriv_sourceMatrixCurve {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    deriv (deriv (sourceMatrixCurve A hA H)) t =
      sourcePositiveSqrt A hA *
        ((NormedSpace.exp ℝ ((2 * t) • H) * ((2 : ℝ) • H)) * ((2 : ℝ) • H)) *
          sourcePositiveSqrt A hA :=
  (hasDerivAt_deriv_sourceMatrixCurve A hA H t).deriv

theorem sourceMatrixCurve_second_derivative_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) :
    deriv (deriv (sourceMatrixCurve A hA H)) 0 =
      (4 : ℝ) • (sourcePositiveSqrt A hA * H ^ 2 * sourcePositiveSqrt A hA) := by
  rw [deriv_deriv_sourceMatrixCurve]
  simp only [mul_zero, zero_smul, NormedSpace.exp_zero, one_mul,
    smul_mul_smul, mul_smul_comm, smul_mul_assoc, pow_two, mul_assoc, smul_smul]
  norm_num

end PaperI

