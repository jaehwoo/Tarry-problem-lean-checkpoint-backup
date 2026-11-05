import PaperILean.OriginalGaussFrozenCoefficientBounds
import PaperILean.OriginalGaussGraphJetComponents

/-! I1301-I1305: estimate the original body directly in its frozen frame.
Absolute shear is never bounded or assumed small. The determinant may have
either sign or vanish. Only the stated normal and r0 pivots are inverted. -/
set_option maxSynthPendingDepth 4
noncomputable section
namespace PaperI
open Filter
open scoped Topology ContDiff

theorem originalGaussGraphPullback_Cz (c : (Fin 2 → ℝ) → ℝ)
    (g : Fin 6 → ℝ) (v : Fin 2 → ℝ)
    (hc : DifferentiableAt ℝ c (originalGaussGraphBaseChange g v)) :
    originalGaussCz (originalGaussGraphPullback g c) v =
      g 3*originalGaussCy c (originalGaussGraphBaseChange g v)+
        originalGaussCz c (originalGaussGraphBaseChange g v)-g 1 := by
  unfold originalGaussCz
  rw [originalGaussGraphPullback_fderiv c g v ![0,1] hc,originalGauss_linear_apply_two]
  simp [originalGaussCy]

theorem originalGaussGraphPullback_Cz_fderiv (c : (Fin 2 → ℝ) → ℝ)
    (g : Fin 6 → ℝ) (v u : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 2 c (originalGaussGraphBaseChange g v)) :
    fderiv ℝ (originalGaussCz (originalGaussGraphPullback g c)) v u =
      g 3*fderiv ℝ (originalGaussCy c) (originalGaussGraphBaseChange g v) ![u 0+g 3*u 1,u 1]+
        fderiv ℝ (originalGaussCz c) (originalGaussGraphBaseChange g v) ![u 0+g 3*u 1,u 1] := by
  have he : originalGaussCz (originalGaussGraphPullback g c) =ᶠ[𝓝 v]
      (fun w => g 3*originalGaussCy c (originalGaussGraphBaseChange g w)+
        originalGaussCz c (originalGaussGraphBaseChange g w)-g 1) := by
    filter_upwards [(originalGaussGraphBaseChange_hasFDerivAt g v).continuousAt.eventually
      (hc.eventually (by norm_num))] with w hw
    exact originalGaussGraphPullback_Cz c g w (hw.differentiableAt (by norm_num))
  have hP : DifferentiableAt ℝ (originalGaussCy c) (originalGaussGraphBaseChange g v) :=
    ((hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hQ : DifferentiableAt ℝ (originalGaussCz c) (originalGaussGraphBaseChange g v) :=
    ((hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  rw [he.fderiv_eq]
  have hb := originalGaussGraphBaseChange_hasFDerivAt g v
  have hd := (((hP.hasFDerivAt.comp v hb).const_mul (g 3)).add
    (hQ.hasFDerivAt.comp v hb)).sub_const (g 1)
  have h := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L u) hd.fderiv
  simpa [Function.comp_def,originalGaussBaseLinear_apply] using h

theorem originalGaussGraphPullback_T (c : (Fin 2 → ℝ) → ℝ)
    (g : Fin 6 → ℝ) (v : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 2 c (originalGaussGraphBaseChange g v)) :
    originalGaussT (originalGaussGraphPullback g c) v =
      g 3^2*originalGaussR c (originalGaussGraphBaseChange g v)+
      2*g 3*originalGaussS c (originalGaussGraphBaseChange g v)+
        originalGaussT c (originalGaussGraphBaseChange g v) := by
  unfold originalGaussT
  rw [originalGaussGraphPullback_Cz_fderiv c g v ![0,1] hc,
    originalGauss_linear_apply_two (fderiv ℝ (originalGaussCy c) _),
    originalGauss_linear_apply_two (fderiv ℝ (originalGaussCz c) _),originalGauss_mixed_partials c _ hc]
  simp [originalGaussR,originalGaussS]
  ring

theorem originalGaussFrozenGraph_T (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 2 c v) (hr : originalGaussR c v ≠ 0) :
    originalGaussT (originalGaussFrozenGraph c v) 0 =
      (originalGaussGraphHessian c v).det/originalGaussR c v := by
  unfold originalGaussFrozenGraph
  rw [originalGaussGraphPullback_T,originalGaussFrozenGraph_base]
  · change originalGaussShear c v^2*originalGaussR c v +
      2*originalGaussShear c v*originalGaussS c v+originalGaussT c v = _
    rw [originalGaussGraphHessian_det c v hc]
    unfold originalGaussShear
    field_simp [hr]
    ring
  · simpa only [originalGaussFrozenGraph_base] using hc

theorem originalGauss_frozen_graph_coefficient_bounds
    (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c ![Y a,a 1]) (hY : DifferentiableAt ℝ Y a)
    (hr : originalGaussR c ![Y a,a 1] ≠ 0)
    (hright : ∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0)
    (H M : ℝ) (hH : 1 ≤ H) (hM : 1 ≤ M)
    (h2 : ‖fderiv ℝ (fderiv ℝ (originalGaussGraphPullback (originalGaussFrameField c Y a) c)) 0‖ ≤ H)
    (h3 : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (originalGaussGraphPullback (originalGaussFrameField c Y a) c))) 0‖ ≤ H)
    (hi : |(originalGaussR c ![Y a,a 1])⁻¹| ≤ M) :
    |(originalGaussGraphHessian c ![Y a,a 1]).det/originalGaussR c ![Y a,a 1]| ≤ H ∧
    |fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![1,0]| ≤ H*M^2 ∧
    |fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![0,1]| ≤ H*M := by
  let b := originalGaussFrozenGraph c ![Y a,a 1]
  have hb : b = originalGaussGraphPullback (originalGaussFrameField c Y a) c :=
    originalGaussFrozenGraph_eq_frame_pullback c Y a hright.self_of_nhds
  have hbc : ContDiffAt ℝ 3 b 0 := by
    rw [hb]
    apply originalGaussGraphPullback_contDiffAt
    simpa only [originalGaussFrameField_base_zero] using hc
  rw [← hb] at h2 h3
  have hT := (originalGauss_second_components_bound b 0 (hbc.of_le (by decide)) H h2).2.2
  have hUVV := (originalGauss_third_components_bound b 0 hbc H h3).2.2
  have he : ‖(![1,0] : Fin 2 → ℝ)‖=1 := originalGauss_basis_norm 0
  have hf : ‖(![0,1] : Fin 2 → ℝ)‖=1 := originalGauss_basis_norm 1
  have hUUV : |originalGaussUUV b 0| ≤ H := by
    have h := originalGauss_third_partial_bound b 0 ![1,0] ![1,0] ![0,1] hbc
    simp only [he,hf,mul_one] at h
    exact h.trans h3
  refine ⟨?_,?_,?_⟩
  · simpa only [b,originalGaussFrozenGraph_T c _ (hc.of_le (by decide)) hr] using hT
  · rw [originalGauss_same_shear_dp c Y a hc hY hr hright,
      div_eq_mul_inv,abs_mul,abs_neg,← inv_pow,abs_pow]
    exact mul_le_mul hUUV (by gcongr) (sq_nonneg _) (by linarith)
  · rw [originalGauss_same_shear_dz c Y a hc hY hr hright,div_eq_mul_inv,abs_mul,abs_neg]
    exact mul_le_mul hUVV hi (abs_nonneg _) (by linarith)

theorem originalGauss_frozen_graph_body_bound
    (c Y : (Fin 2 → ℝ) → ℝ) (a u : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c ![Y a,a 1]) (hY : DifferentiableAt ℝ Y a)
    (hr : originalGaussR c ![Y a,a 1] ≠ 0)
    (hright : ∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0)
    (H M : ℝ) (hH : 1 ≤ H) (hM : 1 ≤ M)
    (h2 : ‖fderiv ℝ (fderiv ℝ (originalGaussGraphPullback (originalGaussFrameField c Y a) c)) 0‖ ≤ H)
    (h3 : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (originalGaussGraphPullback (originalGaussFrameField c Y a) c))) 0‖ ≤ H)
    (hi : |(originalGaussR c ![Y a,a 1])⁻¹| ≤ M) :
    ‖originalAffineBodyCoordinates (originalGaussFrameField c Y a)
      (originalGaussFrameVelocity c Y a u)‖ ≤ 2*H*M^2*‖u‖ := by
  obtain ⟨hs,hp,hz⟩ := originalGauss_frozen_graph_coefficient_bounds c Y a hc hY hr hright H M hH hM h2 h3 hi
  have hH0 : 0 ≤ H := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hMsq : M ≤ M^2 := by nlinarith
  have hsmall : H ≤ H*M^2 := le_mul_of_one_le_right hH0 (one_le_pow₀ hM)
  have hbig : 1 ≤ H*M^2 := one_le_mul_of_one_le_of_one_le hH (one_le_pow₀ hM)
  have hMin : M ≤ H*M^2 := hMsq.trans (le_mul_of_one_le_left (sq_nonneg _) hH)
  have hz' : |fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![0,1]| ≤ H*M^2 :=
    hz.trans (mul_le_mul_of_nonneg_left hMsq hH0)
  have hu0 : |u 0| ≤ ‖u‖ := norm_le_pi_norm u 0
  have hu1 : |u 1| ≤ ‖u‖ := norm_le_pi_norm u 1
  rw [originalGaussFrameField_body_coordinates c Y a u (hc.of_le (by decide)) hY hr hright]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*H*M^2*‖u‖)).mpr
  intro j
  fin_cases j <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_succ,Matrix.cons_val_fin_one,Real.norm_eq_abs]
  · exact hu0.trans (by nlinarith [norm_nonneg u])
  · change |((originalGaussGraphHessian c ![Y a,a 1]).det/originalGaussR c ![Y a,a 1])*u 1| ≤ _
    rw [abs_mul]
    exact (mul_le_mul (hs.trans hsmall) hu1 (abs_nonneg _) (by positivity)).trans (by nlinarith [norm_nonneg u])
  · simp; positivity
  · calc
      _ ≤ |u 0*fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![1,0]|+
          |u 1*fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![0,1]| := abs_add _ _
      _ ≤ ‖u‖*(H*M^2)+‖u‖*(H*M^2) := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul hu0 hp (abs_nonneg _) (norm_nonneg u))
          (mul_le_mul hu1 hz' (abs_nonneg _) (norm_nonneg u))
      _ = _ := by ring
  · change |u 0/originalGaussR c ![Y a,a 1]| ≤ _
    rw [div_eq_mul_inv,abs_mul]
    exact (mul_le_mul hu0 (hi.trans hMin) (abs_nonneg _) (norm_nonneg u)).trans (by nlinarith [norm_nonneg u])
  · exact hu1.trans (by nlinarith [norm_nonneg u])

theorem originalGauss_normalized_coefficient_body_bound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M : ℝ, 1 ≤ M → ∀ F : CoefficientSpace k,
      ∀ m : ℕ, 2 ≤ m → m ≤ k/2 → ∀ (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ),
      ContinuousAt c ![Y a,a 1] → DifferentiableAt ℝ Y a →
      (∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0) →
      C*coefficientEuclideanNorm (originalUpperCoefficientPullback F (originalGaussFrameField c Y a)) ≤ M →
      (∀ᶠ v in 𝓝 (![Y a,a 1] : Fin 2 → ℝ), originalNormalPhase F (m-1) (originalNormalLift c v)=0) →
      originalNormalPhase F m (originalNormalLift c ![Y a,a 1]) ≠ 0 →
      |(originalNormalPhase F m (originalNormalLift c ![Y a,a 1]))⁻¹| ≤ M →
      originalGaussR c ![Y a,a 1] ≠ 0 → |(originalGaussR c ![Y a,a 1])⁻¹| ≤ M →
      ∀ u : Fin 2 → ℝ, ‖originalAffineBodyCoordinates (originalGaussFrameField c Y a)
        (originalGaussFrameVelocity c Y a u)‖ ≤ 8*M^12*‖u‖ := by
  obtain ⟨C,hC,hbound⟩ := originalGauss_normalized_coefficient_graph_bounds k
  refine ⟨C,hC,?_⟩
  intro M hM F m hm hmk c Y a hc hY hright hF hroot hk hki hr hi u
  obtain ⟨_,h2,h3⟩ := hbound M hM F m hm hmk c Y a hc hF hroot hk hki
  have he : m-1+1=m := by omega
  have hc3 : ContDiffAt ℝ 3 c ![Y a,a 1] :=
    (originalNormalPhase_same_graph_smooth F (m-1) c _ hc hroot (by simpa only [he] using hk)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have h2' : ‖fderiv ℝ (fderiv ℝ (originalGaussGraphPullback (originalGaussFrameField c Y a) c)) 0‖ ≤ 4*M^10 := by
    have hh : M^6 ≤ M^10 := pow_le_pow_right₀ hM (by decide)
    exact h2.trans (by nlinarith [pow_nonneg (by linarith : 0 ≤ M) 10])
  have hH : 1 ≤ 4*M^10 := by nlinarith [one_le_pow₀ hM (n := 10)]
  have h := originalGauss_frozen_graph_body_bound c Y a u hc3 hY hr hright (4*M^10) M hH hM h2' h3 hi
  convert h using 1 <;> ring

end PaperI
