import PaperILean.MatrixLogAnalytic
import PaperILean.MatrixExponentialDifferential

/-! I327/331 prerequisite: differentiate the already proved inverse identities
on their actual open domains. These are noncommutative Frechet differentials,
not multiplication by the exponential in arbitrary directions. -/
noncomputable section
open Set Filter
open scoped Topology Matrix Matrix.L2OpNorm
namespace PaperI

theorem matrixLog_exp_eventuallyEq (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ‖H‖ < 1/2) :
    (fun X => matrixLogSeries (NormedSpace.exp ℝ X)) =ᶠ[𝓝 H] id := by
  have ho : IsOpen {X : Matrix (Fin 3) (Fin 3) ℝ | ‖X‖ < 1/2} :=
    isOpen_lt continuous_norm continuous_const
  filter_upwards [ho.mem_nhds hH] with X hX
  exact matrixLogSeries_exp X hX

theorem matrix_exp_log_eventuallyEq (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ‖A-1‖ < 1) :
    (fun B => NormedSpace.exp ℝ (matrixLogSeries B)) =ᶠ[𝓝 A] id := by
  have ho : IsOpen {B : Matrix (Fin 3) (Fin 3) ℝ | ‖B-1‖ < 1} :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  filter_upwards [ho.mem_nhds hA] with B hB
  exact matrix_exp_matrixLogSeries B hB

theorem matrixLog_fderiv_comp_exp (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ‖H‖ < 1/2) :
    (fderiv ℝ matrixLogSeries (NormedSpace.exp ℝ H)).comp (matrixExpDifferential H) =
      ContinuousLinearMap.id ℝ (Matrix (Fin 3) (Fin 3) ℝ) := by
  have hd := (matrixLogSeries_hasFDerivAt (NormedSpace.exp ℝ H)
    (matrix_exp_sub_one_norm_lt_one_of_lt_half H hH)).comp H (matrix_exp_hasFDerivAt H)
  exact hd.unique ((hasFDerivAt_id H).congr_of_eventuallyEq (matrixLog_exp_eventuallyEq H hH))

theorem matrix_exp_fderiv_comp_log (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ‖A-1‖ < 1) :
    (matrixExpDifferential (matrixLogSeries A)).comp (fderiv ℝ matrixLogSeries A) =
      ContinuousLinearMap.id ℝ (Matrix (Fin 3) (Fin 3) ℝ) := by
  have hd := (matrix_exp_hasFDerivAt (matrixLogSeries A)).comp A
    (matrixLogSeries_hasFDerivAt A hA)
  exact hd.unique ((hasFDerivAt_id A).congr_of_eventuallyEq (matrix_exp_log_eventuallyEq A hA))

theorem matrix_exp_fderiv_comp_log_at_exp (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ‖H‖ < 1/2) :
    (matrixExpDifferential H).comp (fderiv ℝ matrixLogSeries (NormedSpace.exp ℝ H)) =
      ContinuousLinearMap.id ℝ (Matrix (Fin 3) (Fin 3) ℝ) := by
  simpa only [matrixLogSeries_exp H hH] using
    matrix_exp_fderiv_comp_log (NormedSpace.exp ℝ H)
      (matrix_exp_sub_one_norm_lt_one_of_lt_half H hH)

def matrixExpDifferentialEquiv (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : ‖H‖ < 1/2) :
    Matrix (Fin 3) (Fin 3) ℝ ≃L[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
  ContinuousLinearEquiv.equivOfInverse' (matrixExpDifferential H)
    (fderiv ℝ matrixLogSeries (NormedSpace.exp ℝ H))
    (matrix_exp_fderiv_comp_log_at_exp H hH) (matrixLog_fderiv_comp_exp H hH)

theorem matrixExpDifferentialEquiv_apply (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ‖H‖ < 1/2) (V : Matrix (Fin 3) (Fin 3) ℝ) :
    matrixExpDifferentialEquiv H hH V = matrixExpDifferential H V := rfl

theorem matrixExpDifferentialEquiv_symm_apply (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ‖H‖ < 1/2) (V : Matrix (Fin 3) (Fin 3) ℝ) :
    (matrixExpDifferentialEquiv H hH).symm V =
      fderiv ℝ matrixLogSeries (NormedSpace.exp ℝ H) V := rfl

theorem matrixExpDifferential_injective (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ‖H‖ < 1/2) : Function.Injective (matrixExpDifferential H) :=
  (matrixExpDifferentialEquiv H hH).injective

theorem matrixExpDifferential_surjective (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ‖H‖ < 1/2) : Function.Surjective (matrixExpDifferential H) :=
  (matrixExpDifferentialEquiv H hH).surjective

theorem matrix_exp_hasStrictFDerivAt_equiv (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ‖H‖ < 1/2) :
    HasStrictFDerivAt (NormedSpace.exp ℝ)
      (matrixExpDifferentialEquiv H hH :
        Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ) H :=
  matrix_exp_hasStrictFDerivAt H

theorem matrixLog_hasStrictFDerivAt_inverse (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ‖H‖ < 1/2) :
    HasStrictFDerivAt matrixLogSeries
      ((matrixExpDifferentialEquiv H hH).symm :
        Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ)
      (NormedSpace.exp ℝ H) :=
  matrixLogSeries_hasStrictFDerivAt _ (matrix_exp_sub_one_norm_lt_one_of_lt_half H hH)

theorem matrixExpDifferential_analyticAt (H : Matrix (Fin 3) (Fin 3) ℝ) :
    AnalyticAt ℝ (matrixExpDifferential (n := 3)) H :=
  (NormedSpace.exp_analytic H).fderiv

theorem matrixLog_fderiv_analyticAt (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ‖A-1‖ < 1) : AnalyticAt ℝ (fderiv ℝ matrixLogSeries) A :=
  (matrixLogSeries_analyticAt A hA).fderiv

end PaperI
