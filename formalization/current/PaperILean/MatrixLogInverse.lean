import PaperILean.MatrixLogDerivative
import Mathlib.Analysis.Calculus.MeanValue

/-! I327: the logarithm series is a left inverse to the actual exponential on
its fixed radius-one-half ball. The opposite inverse identity is separate. -/
noncomputable section
open Set
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem matrix_exp_smul_commute (H : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    Commute (NormedSpace.exp ℝ (t • H)) H :=
  ((Commute.refl H).smul_left t).exp_left ℝ

theorem matrix_exp_smul_sub_one_commute_derivative
    (H : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    Commute (NormedSpace.exp ℝ (t • H)-1) (NormedSpace.exp ℝ (t • H)*H) :=
  ((Commute.refl _).mul_right (matrix_exp_smul_commute H t)).sub_left (Commute.one_left _)

theorem matrix_exp_smul_sub_one_norm_le
    (H : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hsmall : r*‖H‖ ≤ 1/2) (t : ℝ) (ht : |t| ≤ r) :
    ‖NormedSpace.exp ℝ (t • H)-1‖ ≤ 2*r*‖H‖ := by
  have hn : ‖t • H‖ ≤ r*‖H‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ht (norm_nonneg H)
  exact (matrix_exp_sub_one_norm_le_two _ (hn.trans hsmall)).trans (by linarith)

theorem matrix_exp_smul_norm_le_two
    (H : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hsmall : r*‖H‖ ≤ 1/2) (t : ℝ) (ht : |t| ≤ r) :
    ‖NormedSpace.exp ℝ (t • H)‖ ≤ 2 := by
  have h := matrix_exp_smul_sub_one_norm_le H r hr hsmall t ht
  have hn := norm_add_le (NormedSpace.exp ℝ (t • H)-1) (1 : Matrix (Fin 3) (Fin 3) ℝ)
  simp only [sub_add_cancel, norm_one] at hn
  linarith

theorem matrixLogSeries_exp_hasDerivAt_on
    (H : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) (hr : 0 < r)
    (hsmall : r*‖H‖ < 1/2) (t : ℝ) (ht : t ∈ Ioo (-r) r) :
    HasDerivAt (fun y : ℝ => matrixLogSeries (NormedSpace.exp ℝ (y • H))) H t := by
  have habs (y : ℝ) (hy : y ∈ Ioo (-r) r) : |y| ≤ r :=
    (abs_lt.mpr hy).le
  have h := matrixLogSeries_hasDerivAt_on
    (fun y : ℝ => NormedSpace.exp ℝ (y • H))
    (fun y : ℝ => NormedSpace.exp ℝ (y • H)*H) (Ioo (-r) r)
    isOpen_Ioo (convex_Ioo (-r) r).isPreconnected (2*r*‖H‖) (2*‖H‖)
    (by positivity) (by linarith)
    (fun y _ => hasDerivAt_exp_smul_const H y)
    (fun y _ => matrix_exp_smul_sub_one_commute_derivative H y)
    (fun y hy => matrix_exp_smul_sub_one_norm_le H r hr.le hsmall.le y (habs y hy))
    (fun y hy => (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
      (matrix_exp_smul_norm_le_two H r hr.le hsmall.le y (habs y hy)) (norm_nonneg H)))
    t ht
  have hdom : ‖NormedSpace.exp ℝ (t • H)-1‖ < 1 :=
    (matrix_exp_smul_sub_one_norm_le H r hr.le hsmall.le t (habs t ht)).trans_lt
      (by linarith)
  simpa only [← mul_assoc, matrixLogSeries_geometric_cancel _ hdom, one_mul] using h

theorem matrixLogSeries_exp_smul_eq
    (H : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) (hr : 0 < r)
    (hsmall : r*‖H‖ < 1/2) (t : ℝ) (ht : t ∈ Ioo (-r) r) :
    matrixLogSeries (NormedSpace.exp ℝ (t • H)) = t • H := by
  have hd (y : ℝ) (hy : y ∈ Ioo (-r) r) :=
    matrixLogSeries_exp_hasDerivAt_on H r hr hsmall y hy
  have hg (y : ℝ) : HasDerivAt (fun z : ℝ => z • H) H y := by
    simpa only [one_smul] using (hasDerivAt_id y).smul_const H
  exact isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo (-r) r).isPreconnected
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y _ => (hg y).differentiableAt.differentiableWithinAt)
    (fun y hy => (hd y hy).deriv.trans (hg y).deriv.symm)
    (show (0 : ℝ) ∈ Ioo (-r) r by constructor <;> linarith)
    (by simp [matrixLogSeries_one]) ht

theorem matrixLogSeries_exp (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : ‖H‖ < 1/2) :
    matrixLogSeries (NormedSpace.exp ℝ H) = H := by
  by_cases hzero : H = 0
  · simp [hzero, matrixLogSeries_one]
  have hn : 0 < ‖H‖ := norm_pos_iff.mpr hzero
  obtain ⟨q, hqH, hqhalf⟩ := exists_between hH
  have hq : 0 < q := hn.trans hqH
  have hr : 0 < q/‖H‖ := div_pos hq hn
  have hr1 : 1 < q/‖H‖ := (lt_div_iff₀ hn).mpr (by simpa using hqH)
  have hsmall : (q/‖H‖)*‖H‖ < 1/2 := by
    rwa [div_mul_cancel₀ _ hn.ne']
  simpa only [one_smul] using matrixLogSeries_exp_smul_eq H (q/‖H‖) hr hsmall 1
    (by constructor <;> linarith)

theorem matrix_exp_injOn_half_ball :
    Set.InjOn (NormedSpace.exp ℝ : Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ)
      {H | ‖H‖ < 1/2} := by
  intro H hH K hK heq
  rw [← matrixLogSeries_exp H hH, ← matrixLogSeries_exp K hK, heq]

theorem matrixLogSeries_skewRotationExp (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : Hᵀ = -H) (hsmall : ‖H‖ < 1/2) :
    rotationLogSeries (skewRotationExp H hH) = H :=
  matrixLogSeries_exp H hsmall

theorem anisotropicSkewBall_exp_injective (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (ht : t < 1/10) :
    Set.InjOn (NormedSpace.exp ℝ : Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ)
      (anisotropicSkewBall e ((10/9)*t)) := by
  intro H hH K hK heq
  exact matrix_exp_injOn_half_ball (anisotropicSkewBall_source_fixed_radius e he t ht H hH)
    (anisotropicSkewBall_source_fixed_radius e he t ht K hK) heq

end PaperI
