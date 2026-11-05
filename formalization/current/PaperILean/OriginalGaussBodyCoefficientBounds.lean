import PaperILean.OriginalGaussGraphJetComponents

/-! I1305: actual body coefficients from graph jets and conditioned curvature.
The frozen UUV/UVV formulas from the original proof are used without dropping
their shear terms. No sign condition is imposed on the graph Hessian. -/
set_option maxSynthPendingDepth 4
noncomputable section
namespace PaperI
open Filter
open scoped Topology

theorem originalGauss_shear_norm_bound (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (H M : ℝ) (hM : 0 ≤ M) (hS : |originalGaussS c v| ≤ H)
    (hi : |(originalGaussR c v)⁻¹| ≤ M) :
    |originalGaussShear c v| ≤ H*M := by
  simpa only [originalGaussShear,div_eq_mul_inv,abs_mul,abs_neg] using
    mul_le_mul hS hi (abs_nonneg _) (le_trans (abs_nonneg _) hS)

theorem originalGauss_det_ratio_bound (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 2 c v) (H M : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hR : |originalGaussR c v| ≤ H) (hS : |originalGaussS c v| ≤ H)
    (hT : |originalGaussT c v| ≤ H) (hi : |(originalGaussR c v)⁻¹| ≤ M) :
    |(originalGaussGraphHessian c v).det/originalGaussR c v| ≤ 2*H^2*M := by
  rw [originalGaussGraphHessian_det c v hc,div_eq_mul_inv,abs_mul]
  have hdet : |originalGaussR c v*originalGaussT c v-originalGaussS c v^2| ≤ 2*H^2 := by
    calc
      _ ≤ |originalGaussR c v*originalGaussT c v|+|originalGaussS c v^2| := abs_sub _ _
      _ = |originalGaussR c v| * |originalGaussT c v|+|originalGaussS c v|^2 := by rw [abs_mul,abs_pow]
      _ ≤ H*H+H^2 := by gcongr
      _ = _ := by ring
  exact mul_le_mul hdet hi (abs_nonneg _) (by positivity)

theorem originalGauss_frozen_UUV_bound (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c v) (H M : ℝ) (hH : 1 ≤ H) (hM : 1 ≤ M)
    (hd : |originalGaussShear c v| ≤ H*M)
    (hA : |fderiv ℝ (originalGaussR c) v ![1,0]| ≤ H)
    (hB : |fderiv ℝ (originalGaussS c) v ![1,0]| ≤ H) :
    |originalGaussUUV (originalGaussFrozenGraph c v) 0| ≤ 2*H^2*M := by
  have hH0 : 0 ≤ H := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hg : H ≤ H^2*M := by
    calc
      H = H*1 := by ring
      _ ≤ H*(H*M) := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hH hM) hH0
      _ = _ := by ring
  rw [originalGaussFrozenGraph_UUV c v hc]
  calc
    _ ≤ |fderiv ℝ (originalGaussS c) v ![1,0]|+
        |originalGaussShear c v*fderiv ℝ (originalGaussR c) v ![1,0]| := abs_add _ _
    _ = |fderiv ℝ (originalGaussS c) v ![1,0]|+
        |originalGaussShear c v| * |fderiv ℝ (originalGaussR c) v ![1,0]| := by rw [abs_mul]
    _ ≤ H+(H*M)*H := by gcongr
    _ ≤ 2*H^2*M := by nlinarith [hg]

theorem originalGauss_frozen_UVV_bound (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c v) (H M : ℝ) (hH : 1 ≤ H) (hM : 1 ≤ M)
    (hd : |originalGaussShear c v| ≤ H*M)
    (hA : |fderiv ℝ (originalGaussR c) v ![1,0]| ≤ H)
    (hB : |fderiv ℝ (originalGaussS c) v ![1,0]| ≤ H)
    (hC : |fderiv ℝ (originalGaussS c) v ![0,1]| ≤ H) :
    |originalGaussUVV (originalGaussFrozenGraph c v) 0| ≤ 4*H^3*M^2 := by
  have hH0 : 0 ≤ H := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hg : H ≤ H^3*M^2 := by
    calc
      H = H*1 := by ring
      _ ≤ H*(H^2*M^2) := mul_le_mul_of_nonneg_left
        (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hH) (one_le_pow₀ hM)) hH0
      _ = _ := by ring
  have hg2 : H^2*M ≤ H^3*M^2 := by
    calc
      H^2*M = (H^2*M)*1 := by ring
      _ ≤ (H^2*M)*(H*M) := mul_le_mul_of_nonneg_left
        (one_le_mul_of_one_le_of_one_le hH hM) (by positivity)
      _ = _ := by ring
  rw [originalGaussFrozenGraph_UVV c v hc]
  calc
    _ ≤ |fderiv ℝ (originalGaussS c) v ![0,1]|+
        |2*originalGaussShear c v*fderiv ℝ (originalGaussS c) v ![1,0]|+
        |originalGaussShear c v^2*fderiv ℝ (originalGaussR c) v ![1,0]| :=
          (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ = |fderiv ℝ (originalGaussS c) v ![0,1]|+
        2*|originalGaussShear c v| * |fderiv ℝ (originalGaussS c) v ![1,0]|+
        |originalGaussShear c v|^2*|fderiv ℝ (originalGaussR c) v ![1,0]| := by
          simp only [abs_mul,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<2)]
    _ ≤ H+2*(H*M)*H+(H*M)^2*H := by gcongr
    _ ≤ 4*H^3*M^2 := by nlinarith [hg,hg2]

theorem originalGauss_same_shear_derivative_bounds
    (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c ![Y a,a 1]) (hY : DifferentiableAt ℝ Y a)
    (hr : originalGaussR c ![Y a,a 1] ≠ 0)
    (hright : ∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0)
    (H M : ℝ) (hH : 1 ≤ H) (hM : 1 ≤ M)
    (h2 : ‖fderiv ℝ (fderiv ℝ c) ![Y a,a 1]‖ ≤ H)
    (h3 : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ c)) ![Y a,a 1]‖ ≤ H)
    (hi : |(originalGaussR c ![Y a,a 1])⁻¹| ≤ M) :
    |fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![1,0]| ≤ 2*H^2*M^3 ∧
    |fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![0,1]| ≤ 4*H^3*M^3 := by
  have hH0 : 0 ≤ H := by linarith
  have hM0 : 0 ≤ M := by linarith
  obtain ⟨hR,hS,hT⟩ := originalGauss_second_components_bound c _ (hc.of_le (by decide)) H h2
  obtain ⟨hA,hB,hC⟩ := originalGauss_third_components_bound c _ hc H h3
  have hd := originalGauss_shear_norm_bound c _ H M hM0 hS hi
  have hU := originalGauss_frozen_UUV_bound c _ hc H M hH hM hd hA hB
  have hV := originalGauss_frozen_UVV_bound c _ hc H M hH hM hd hA hB hC
  constructor
  · rw [originalGauss_same_shear_dp c Y a hc hY hr hright]
    calc
      _ = |originalGaussUUV (originalGaussFrozenGraph c ![Y a,a 1]) 0| *
          |(originalGaussR c ![Y a,a 1])⁻¹|^2 := by
            rw [div_eq_mul_inv,abs_mul,abs_neg,← inv_pow,abs_pow]
      _ ≤ (2*H^2*M)*M^2 := by gcongr
      _ = _ := by ring
  · rw [originalGauss_same_shear_dz c Y a hc hY hr hright]
    calc
      _ = |originalGaussUVV (originalGaussFrozenGraph c ![Y a,a 1]) 0| *
          |(originalGaussR c ![Y a,a 1])⁻¹| := by
            simp only [div_eq_mul_inv,abs_mul,abs_neg]
      _ ≤ (4*H^3*M^2)*M := by gcongr
      _ = _ := by ring

theorem originalGauss_body_coordinates_bound
    (c Y : (Fin 2 → ℝ) → ℝ) (a u : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c ![Y a,a 1]) (hY : DifferentiableAt ℝ Y a)
    (hr : originalGaussR c ![Y a,a 1] ≠ 0)
    (hright : ∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0)
    (H M : ℝ) (hH : 1 ≤ H) (hM : 1 ≤ M)
    (h2 : ‖fderiv ℝ (fderiv ℝ c) ![Y a,a 1]‖ ≤ H)
    (h3 : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ c)) ![Y a,a 1]‖ ≤ H)
    (hi : |(originalGaussR c ![Y a,a 1])⁻¹| ≤ M) :
    ‖originalAffineBodyCoordinates (originalGaussFrameField c Y a)
      (originalGaussFrameVelocity c Y a u)‖ ≤ 6*H^3*M^3*‖u‖ := by
  have hH0 : 0 ≤ H := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hc2 : ContDiffAt ℝ 2 c ![Y a,a 1] := hc.of_le (by decide)
  obtain ⟨hR,hS,hT⟩ := originalGauss_second_components_bound c _ hc2 H h2
  have hs := originalGauss_det_ratio_bound c _ hc2 H M hH0 hM0 hR hS hT hi
  obtain ⟨hp,hz⟩ := originalGauss_same_shear_derivative_bounds c Y a hc hY hr hright H M hH hM h2 h3 hi
  have h23 : H^2*M^3 ≤ H^3*M^3 :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hH (by decide : 2 ≤ 3)) (by positivity)
  have h13 : M ≤ M^3 := by simpa only [pow_one] using pow_le_pow_right₀ hM (by decide : 1 ≤ 3)
  have hsmall : H^2*M ≤ H^3*M^3 :=
    mul_le_mul (pow_le_pow_right₀ hH (by decide : 2 ≤ 3)) h13 hM0 (by positivity)
  have hbig : 1 ≤ H^3*M^3 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hH) (one_le_pow₀ hM)
  have hMin : M ≤ H^3*M^3 := h13.trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hH))
  have hu0 : |u 0| ≤ ‖u‖ := norm_le_pi_norm u 0
  have hu1 : |u 1| ≤ ‖u‖ := norm_le_pi_norm u 1
  have hp' : |fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![1,0]| ≤ 2*(H^3*M^3) := by nlinarith
  have hz' : |fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![0,1]| ≤ 4*(H^3*M^3) := by nlinarith
  have hs' : |(originalGaussGraphHessian c ![Y a,a 1]).det/originalGaussR c ![Y a,a 1]| ≤ 2*(H^3*M^3) := by nlinarith
  rw [originalGaussFrameField_body_coordinates c Y a u hc2 hY hr hright]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 6*H^3*M^3*‖u‖)).mpr
  intro j
  fin_cases j <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_succ,Matrix.cons_val_fin_one,Real.norm_eq_abs]
  · exact hu0.trans (by nlinarith [norm_nonneg u])
  · change |((originalGaussGraphHessian c ![Y a,a 1]).det/originalGaussR c ![Y a,a 1])*u 1| ≤ _
    rw [abs_mul]
    exact (mul_le_mul hs' hu1 (abs_nonneg _) (by positivity)).trans (by nlinarith [norm_nonneg u])
  · simp; positivity
  · calc
      _ ≤ |u 0*fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![1,0]|+
          |u 1*fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![0,1]| := abs_add _ _
      _ ≤ ‖u‖*(2*(H^3*M^3))+‖u‖*(4*(H^3*M^3)) := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul hu0 hp' (abs_nonneg _) (norm_nonneg u))
          (mul_le_mul hu1 hz' (abs_nonneg _) (norm_nonneg u))
      _ = _ := by ring
  · change |u 0/originalGaussR c ![Y a,a 1]| ≤ _
    rw [div_eq_mul_inv,abs_mul]
    exact (mul_le_mul hu0 (hi.trans hMin) (abs_nonneg _) (norm_nonneg u)).trans (by nlinarith [norm_nonneg u])
  · exact hu1.trans (by nlinarith [norm_nonneg u])

end PaperI
