import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The scalar coefficient in Paper I's spectral Hessian (lines219,223).
The value at zero is the continuous extension1, never the totalized quotient0.
Both signs are included. This does not prove the matrix spectral derivative.
-/

noncomputable section
open Filter
open scoped Topology
namespace PaperI

def sinhCardinal (x : ℝ) : ℝ := if x = 0 then 1 else Real.sinh x / x

def spectralCothKernel (x : ℝ) : ℝ :=
  if x = 0 then 1 else x * Real.cosh x / Real.sinh x

theorem sinhCardinal_zero : sinhCardinal 0 = 1 := by simp [sinhCardinal]

theorem sinhCardinal_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    sinhCardinal x = Real.sinh x / x := by simp [sinhCardinal, hx]

theorem sinhCardinal_pos (x : ℝ) : 0 < sinhCardinal x := by
  by_cases hx : x = 0
  · simp [hx, sinhCardinal]
  · rw [sinhCardinal_of_ne_zero hx]
    rcases lt_or_gt_of_ne hx with hn | hp
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr hn) hn
    · exact div_pos (Real.sinh_pos_iff.mpr hp) hp

theorem continuousAt_sinhCardinal_zero : ContinuousAt sinhCardinal 0 := by
  have he : sinhCardinal = Function.update
      (fun x : ℝ => (Real.sinh x - Real.sinh 0) / (x - 0)) 0 (Real.cosh 0) := by
    funext x
    by_cases hx : x = 0 <;> simp [sinhCardinal, Function.update, hx, eq_comm]
  rw [he]
  exact (Real.hasDerivAt_sinh 0).continuousAt_div

theorem continuous_sinhCardinal : Continuous sinhCardinal := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · simpa [hx] using continuousAt_sinhCardinal_zero
  · have h := Real.continuous_sinh.continuousAt.div continuousAt_id hx
    apply h.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact sinhCardinal_of_ne_zero hy

theorem spectralCothKernel_zero : spectralCothKernel 0 = 1 := by
  simp [spectralCothKernel]

theorem spectralCothKernel_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    spectralCothKernel x = x * Real.cosh x / Real.sinh x := by
  simp [spectralCothKernel, hx]

theorem spectralCothKernel_eq_cosh_div_sinhCardinal (x : ℝ) :
    spectralCothKernel x = Real.cosh x / sinhCardinal x := by
  by_cases hx : x = 0
  · simp [hx, spectralCothKernel, sinhCardinal]
  · rw [spectralCothKernel_of_ne_zero hx, sinhCardinal_of_ne_zero hx]
    field_simp
    ring

theorem continuous_spectralCothKernel : Continuous spectralCothKernel := by
  have h := Real.continuous_cosh.div continuous_sinhCardinal
    (fun x => (sinhCardinal_pos x).ne')
  exact h.congr (fun x => (spectralCothKernel_eq_cosh_div_sinhCardinal x).symm)

theorem spectralCothKernel_tendsto_zero :
    Tendsto spectralCothKernel (𝓝 0) (𝓝 1) := by
  have h : ContinuousAt spectralCothKernel 0 := continuous_spectralCothKernel.continuousAt
  change Tendsto spectralCothKernel (𝓝 0) (𝓝 (spectralCothKernel 0)) at h
  simpa only [spectralCothKernel_zero] using h

theorem spectralCothKernel_even (x : ℝ) :
    spectralCothKernel (-x) = spectralCothKernel x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [spectralCothKernel, hx, Real.sinh_neg, Real.cosh_neg]

theorem hasDerivAt_cosh_comparison (x : ℝ) :
    HasDerivAt (fun y : ℝ => y * Real.cosh y - Real.sinh y)
      (x * Real.sinh x) x := by
  convert ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
    (Real.hasDerivAt_sinh x) using 1
  simp only [id]
  ring

theorem mul_sinh_nonneg (x : ℝ) : 0 ≤ x * Real.sinh x := by
  by_cases hx : 0 ≤ x
  · exact mul_nonneg hx (Real.sinh_nonneg_iff.mpr hx)
  · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hx)
      (Real.sinh_nonpos_iff.mpr (le_of_not_ge hx))

theorem cosh_comparison_monotone :
    Monotone (fun x : ℝ => x * Real.cosh x - Real.sinh x) :=
  monotone_of_hasDerivAt_nonneg hasDerivAt_cosh_comparison mul_sinh_nonneg

theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.cosh x := by
  have h := cosh_comparison_monotone hx
  simp only [zero_mul, Real.sinh_zero, sub_zero] at h
  linarith

theorem spectralCothKernel_ge_one_of_pos {x : ℝ} (hx : 0 < x) :
    1 ≤ spectralCothKernel x := by
  rw [spectralCothKernel_of_ne_zero hx.ne']
  exact (le_div_iff₀ (Real.sinh_pos_iff.mpr hx)).mpr
    (by simpa using sinh_le_mul_cosh hx.le)

theorem spectralCothKernel_ge_one (x : ℝ) : 1 ≤ spectralCothKernel x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have h := spectralCothKernel_ge_one_of_pos (neg_pos.mpr hx)
    simpa only [spectralCothKernel_even] using h
  · simp [hx, spectralCothKernel_zero]
  · exact spectralCothKernel_ge_one_of_pos hx

end PaperI
