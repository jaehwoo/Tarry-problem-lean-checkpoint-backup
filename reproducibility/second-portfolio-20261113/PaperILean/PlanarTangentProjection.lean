import PaperILean.PlanarDerivativeCones

/-! The numerical tangent-projection claim in I1263. The unit-vector
premise is explicit, so no normalization of a zero time derivative is used. -/

namespace PaperI

theorem dominant_unit_projection_half {u v : ℝ}
    (hunit : u^2+v^2=1) (hdom : |v| ≤ u) : (1/2 : ℝ) ≤ u := by
  have hu : 0 ≤ u := (abs_nonneg v).trans hdom
  have hv2 : v^2 ≤ u^2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg v) hu).mpr hdom
    simpa only [sq_abs] using hsq
  by_contra hnot
  have hsmall := (sq_le_sq₀ hu (show (0 : ℝ) ≤ 1/2 by norm_num)).mpr (le_of_not_ge hnot)
  nlinarith

theorem dominant_nonzero_normalized_projection_half {u v r : ℝ}
    (hr : 0 < r) (hrsq : r^2=u^2+v^2) (hdom : |v| ≤ u) :
    (1/2 : ℝ) ≤ u/r := by
  apply dominant_unit_projection_half (v := v/r)
  · rw [div_pow,div_pow,← add_div,← hrsq]
    exact div_self (pow_ne_zero 2 hr.ne')
  · rw [abs_div,abs_of_pos hr]
    exact div_le_div_of_nonneg_right hdom hr.le

end PaperI
