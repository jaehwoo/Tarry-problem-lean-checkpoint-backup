import PaperILean.RotationLogChart
import Mathlib.Analysis.NormedSpace.FunctionSeries

/-! I327/331 prerequisite: continuity of the unchanged literal logarithm series.
The geometric majorant is local to each radius below one; no global continuity
of the total `tsum` definition is asserted. -/
noncomputable section
open Set
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem matrixLogSeries_term_continuous (n : ℕ) :
    Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ =>
      matrixLogSeriesCoefficient n • (A-1)^(n+1)) :=
  ((continuous_id.sub continuous_const).pow (n+1)).const_smul _

theorem matrixLogSeries_continuousOn_closed_radius (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn matrixLogSeries {A : Matrix (Fin 3) (Fin 3) ℝ | ‖A-1‖ ≤ r} := by
  apply continuousOn_tsum (fun n => (matrixLogSeries_term_continuous n).continuousOn)
    (geometric_succ_hasSum r hr hr1).summable
  intro n A hA
  exact (matrix_smul_pow_succ_norm_le (A-1) _ (matrixLogSeriesCoefficient_abs_le_one n) n).trans
    (pow_le_pow_left₀ (norm_nonneg _) hA (n+1))

theorem matrixLogSeries_continuousAt (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ‖A-1‖ < 1) : ContinuousAt matrixLogSeries A := by
  obtain ⟨r, hAr, hr⟩ := exists_between hA
  have hopen : IsOpen {B : Matrix (Fin 3) (Fin 3) ℝ | ‖B-1‖ < r} :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  apply (matrixLogSeries_continuousOn_closed_radius r
    ((norm_nonneg _).trans hAr.le) hr A hAr.le).continuousAt
  exact Filter.mem_of_superset (hopen.mem_nhds hAr)
    (fun B hB => (show ‖B-1‖ < r from hB).le)

theorem matrixLogSeries_continuousOn :
    ContinuousOn matrixLogSeries {A : Matrix (Fin 3) (Fin 3) ℝ | ‖A-1‖ < 1} :=
  fun A hA => (matrixLogSeries_continuousAt A hA).continuousWithinAt

theorem matrix_l2_opNorm_transpose (A : Matrix (Fin 3) (Fin 3) ℝ) : ‖Aᵀ‖ = ‖A‖ := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose A

theorem matrixLogSeries_inverse_eq_neg_of_log_small
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A*B = 1)
    (hA : ‖A-1‖ < 1) (hB : ‖B-1‖ < 1)
    (hlA : ‖matrixLogSeries A‖ < 1/2) (hlB : ‖matrixLogSeries B‖ < 1/2) :
    matrixLogSeries B = -matrixLogSeries A := by
  apply matrix_exp_injOn_half_ball hlB
    (by simpa only [Set.mem_setOf_eq, norm_neg] using hlA)
  apply (NormedSpace.isUnit_exp ℝ (matrixLogSeries A)).mul_left_cancel
  rw [matrix_exp_matrixLogSeries A hA, matrix_exp_matrixLogSeries B hB, hAB]
  have h := Matrix.exp_add_of_commute ℝ (matrixLogSeries A) (-matrixLogSeries A)
    (Commute.refl _).neg_right
  simpa only [add_neg_cancel, NormedSpace.exp_zero, matrix_exp_matrixLogSeries A hA] using h

end PaperI
