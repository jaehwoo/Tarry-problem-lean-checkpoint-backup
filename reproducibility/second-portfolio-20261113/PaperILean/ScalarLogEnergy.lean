import PaperILean.SpectralHessianForm
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Positive scalar log-energy curve and the source regularization scale.
The scalar curve is the dimension-one restriction of the source path. It does
not prove the noncommuting matrix formula. R,C_X,C_0 ranges are exactly the
explicit assumptions at Paper I205-211. Constants below are chosen before R.
-/

noncomputable section
namespace PaperI

def scalarLogEnergyCurve (A h t : ℝ) : ℝ :=
  (Real.log (Real.sqrt A * Real.exp (2 * t * h) * Real.sqrt A)) ^ 2

theorem scalarLogCurve_log_eq (A : ℝ) (hA : 0 < A) (h t : ℝ) :
    Real.log (Real.sqrt A * Real.exp (2 * t * h) * Real.sqrt A) =
      Real.log A + (2 * h) * t := by
  have hc : Real.sqrt A * Real.exp (2 * t * h) * Real.sqrt A =
      A * Real.exp (2 * t * h) := by
    calc
      _ = (Real.sqrt A) ^ 2 * Real.exp (2 * t * h) := by ring
      _ = _ := by rw [Real.sq_sqrt hA.le]
  rw [hc, Real.log_mul hA.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem scalarLogEnergyCurve_eq_quadratic (A : ℝ) (hA : 0 < A) (h t : ℝ) :
    scalarLogEnergyCurve A h t = (Real.log A + (2 * h) * t) ^ 2 := by
  rw [scalarLogEnergyCurve, scalarLogCurve_log_eq A hA h t]

theorem hasDerivAt_scalarLogEnergyCurve (A : ℝ) (hA : 0 < A) (h t : ℝ) :
    HasDerivAt (scalarLogEnergyCurve A h) (4 * h * (Real.log A + (2 * h) * t)) t := by
  have he : scalarLogEnergyCurve A h = (fun y => (Real.log A + (2 * h) * y) ^ 2) :=
    funext (scalarLogEnergyCurve_eq_quadratic A hA h)
  rw [he]
  have hlin : HasDerivAt (fun y : ℝ => Real.log A + (2 * h) * y) (2 * h) t := by
    simpa using (hasDerivAt_const t (Real.log A)).add ((hasDerivAt_id t).const_mul (2 * h))
  convert hlin.pow 2 using 1; ring

theorem deriv_scalarLogEnergyCurve (A : ℝ) (hA : 0 < A) (h t : ℝ) :
    deriv (scalarLogEnergyCurve A h) t = 4 * h * (Real.log A + (2 * h) * t) :=
  (hasDerivAt_scalarLogEnergyCurve A hA h t).deriv

theorem scalarLogEnergyCurve_first_derivative_zero (A : ℝ) (hA : 0 < A) (h : ℝ) :
    deriv (scalarLogEnergyCurve A h) 0 = 4 * Real.log A * h := by
  rw [deriv_scalarLogEnergyCurve A hA h 0]
  ring

theorem hasDerivAt_deriv_scalarLogEnergyCurve (A : ℝ) (hA : 0 < A) (h t : ℝ) :
    HasDerivAt (deriv (scalarLogEnergyCurve A h)) (8 * h ^ 2) t := by
  have he : deriv (scalarLogEnergyCurve A h) =
      (fun y => 4 * h * (Real.log A + (2 * h) * y)) :=
    funext (deriv_scalarLogEnergyCurve A hA h)
  rw [he]
  have hlin : HasDerivAt (fun y : ℝ => Real.log A + (2 * h) * y) (2 * h) t := by
    simpa using (hasDerivAt_const t (Real.log A)).add ((hasDerivAt_id t).const_mul (2 * h))
  convert hlin.const_mul (4 * h) using 1; ring

theorem scalarLogEnergyCurve_second_derivative (A : ℝ) (hA : 0 < A) (h t : ℝ) :
    deriv (deriv (scalarLogEnergyCurve A h)) t = 8 * h ^ 2 :=
  (hasDerivAt_deriv_scalarLogEnergyCurve A hA h t).deriv

def sourceLogScale (CX R : ℝ) : ℝ := Real.log (CX * R)

def sourceRegularization (CX C0 R : ℝ) : ℝ := (C0 * (sourceLogScale CX R) ^ 2)⁻¹

theorem sourceLogScale_pos (CX R : ℝ) (hCX : 2 ≤ CX) (hR : 2 ≤ R) :
    0 < sourceLogScale CX R := by
  have hp : (2 : ℝ) * 2 ≤ CX * R :=
    mul_le_mul hCX hR (by norm_num) (by linarith)
  exact Real.log_pos (by linarith)

theorem sourceRegularization_pos (CX C0 R : ℝ)
    (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) (hR : 2 ≤ R) :
    0 < sourceRegularization CX C0 R := by
  have hL := sourceLogScale_pos CX R hCX hR
  have hC : 0 < C0 := by linarith
  unfold sourceRegularization
  positivity

theorem sourceLogScale_monotone_from_two (CX R : ℝ) (hCX : 2 ≤ CX) (hR : 2 ≤ R) :
    sourceLogScale CX 2 ≤ sourceLogScale CX R := by
  have hCXp : 0 < CX := by linarith
  unfold sourceLogScale
  exact Real.log_le_log (mul_pos hCXp (by norm_num))
    (mul_le_mul_of_nonneg_left hR hCXp.le)

theorem sourceRegularization_scale_identity (CX C0 R : ℝ)
    (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) (hR : 2 ≤ R) :
    sourceRegularization CX C0 R * sourceLogScale CX R = (C0 * sourceLogScale CX R)⁻¹ := by
  have hL : sourceLogScale CX R ≠ 0 := (sourceLogScale_pos CX R hCX hR).ne'
  have hC : C0 ≠ 0 := by linarith
  unfold sourceRegularization
  field_simp
  ring

theorem sourceRegularization_scale_bound (CX C0 : ℝ) (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) :
    ∀ R : ℝ, 2 ≤ R → sourceRegularization CX C0 R * sourceLogScale CX R ≤
      (C0 * sourceLogScale CX 2)⁻¹ := by
  intro R hR
  have hC : 0 < C0 := by linarith
  have hbase : 0 < C0 * sourceLogScale CX 2 :=
    mul_pos hC (sourceLogScale_pos CX 2 hCX (by norm_num))
  rw [sourceRegularization_scale_identity CX C0 R hCX hC0 hR]
  simpa only [one_div] using one_div_le_one_div_of_le hbase
    (mul_le_mul_of_nonneg_left (sourceLogScale_monotone_from_two CX R hCX hR) hC.le)

end PaperI
