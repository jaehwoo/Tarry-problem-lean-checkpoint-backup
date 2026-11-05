import PaperILean.MatrixLogContinuity
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! I327/331: analyticity of the unchanged noncommutative logarithm series.
Only the open convergence domain is asserted. The auxiliary formal series
inserts its zero constant coefficient; it does not change the logarithm. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators Matrix Matrix.L2OpNorm ENNReal
set_option maxHeartbeats 800000
namespace PaperI

def matrixLogPowerCoefficient : ℕ → ℝ
  | 0 => 0
  | n+1 => matrixLogSeriesCoefficient n

def matrixLogPowerSeries : FormalMultilinearSeries ℝ
    (Matrix (Fin 3) (Fin 3) ℝ) (Matrix (Fin 3) (Fin 3) ℝ) :=
  FormalMultilinearSeries.ofScalars _ matrixLogPowerCoefficient

theorem matrixLogPowerCoefficient_norm_le_one (n : ℕ) :
    ‖matrixLogPowerCoefficient n‖ ≤ 1 := by
  cases n with
  | zero => norm_num [matrixLogPowerCoefficient]
  | succ n => exact matrixLogSeriesCoefficient_abs_le_one n

theorem matrixLogPowerSeries_norm_le_one (n : ℕ) :
    ‖matrixLogPowerSeries n‖ ≤ 1 := by
  rw [matrixLogPowerSeries, FormalMultilinearSeries.ofScalars_norm]
  exact matrixLogPowerCoefficient_norm_le_one n

theorem matrixLogPowerSeries_radius_ge_one :
    (1 : ℝ≥0∞) ≤ matrixLogPowerSeries.radius := by
  exact matrixLogPowerSeries.le_radius_of_bound (r := 1) 1
    (fun n => by simpa using matrixLogPowerSeries_norm_le_one n)

theorem matrixLogPowerSeries_mem_ball (X : Matrix (Fin 3) (Fin 3) ℝ)
    (hX : ‖X‖ < 1) : X ∈ EMetric.ball 0 matrixLogPowerSeries.radius := by
  change edist X 0 < matrixLogPowerSeries.radius
  apply lt_of_lt_of_le _ matrixLogPowerSeries_radius_ge_one
  simpa only [EMetric.mem_ball, edist_zero_right, ← ofReal_norm,
    ENNReal.ofReal_lt_one] using hX

theorem matrixLogPowerSeries_sum_eq (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ‖A-1‖ < 1) : matrixLogPowerSeries.sum (A-1) = matrixLogSeries A := by
  change FormalMultilinearSeries.ofScalarsSum matrixLogPowerCoefficient (A-1) = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  have hs : Summable (fun n : ℕ => matrixLogPowerCoefficient (n+1) • (A-1)^(n+1)) :=
    matrixLogSeries_summable A hA
  rw [tsum_eq_zero_add' hs]
  simp only [matrixLogPowerCoefficient, zero_smul, zero_add, matrixLogSeries]

theorem matrixLogPowerSeries_sum_analyticAt (X : Matrix (Fin 3) (Fin 3) ℝ)
    (hX : ‖X‖ < 1) : AnalyticAt ℝ matrixLogPowerSeries.sum X :=
  (matrixLogPowerSeries.hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by norm_num) matrixLogPowerSeries_radius_ge_one)).analyticAt_of_mem
      (matrixLogPowerSeries_mem_ball X hX)

theorem matrixLogSeries_analyticAt (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ‖A-1‖ < 1) : AnalyticAt ℝ matrixLogSeries A := by
  have hb : AnalyticAt ℝ (fun B : Matrix (Fin 3) (Fin 3) ℝ => B-1) A :=
    analyticAt_id.sub analyticAt_const
  have ha : AnalyticAt ℝ (fun B : Matrix (Fin 3) (Fin 3) ℝ =>
      matrixLogPowerSeries.sum (B-1)) A :=
    (matrixLogPowerSeries_sum_analyticAt (A-1) hA).comp
      (f := fun B : Matrix (Fin 3) (Fin 3) ℝ => B-1) hb
  apply ha.congr
  have ho : IsOpen {B : Matrix (Fin 3) (Fin 3) ℝ | ‖B-1‖ < 1} :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  filter_upwards [ho.mem_nhds hA] with B hB
  exact matrixLogPowerSeries_sum_eq B hB

theorem matrixLogSeries_analyticOnNhd :
    AnalyticOnNhd ℝ matrixLogSeries {A : Matrix (Fin 3) (Fin 3) ℝ | ‖A-1‖ < 1} :=
  fun A hA => matrixLogSeries_analyticAt A hA

theorem matrixLogSeries_contDiffOn :
    ContDiffOn ℝ ⊤ matrixLogSeries {A : Matrix (Fin 3) (Fin 3) ℝ | ‖A-1‖ < 1} :=
  matrixLogSeries_analyticOnNhd.contDiffOn
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).uniqueDiffOn

theorem matrixLogSeries_hasStrictFDerivAt (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ‖A-1‖ < 1) :
    HasStrictFDerivAt matrixLogSeries (fderiv ℝ matrixLogSeries A) A :=
  (matrixLogSeries_analyticAt A hA).hasStrictFDerivAt

theorem matrixLogSeries_hasFDerivAt (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ‖A-1‖ < 1) : HasFDerivAt matrixLogSeries (fderiv ℝ matrixLogSeries A) A :=
  (matrixLogSeries_hasStrictFDerivAt A hA).hasFDerivAt

end PaperI
