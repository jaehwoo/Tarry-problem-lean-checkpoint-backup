import PaperILean.OriginalGaussFrozenThird

/-! I1303: the actual derivative of the shear along the same inverse.
Normalized third derivatives are those of the literal frozen graph. -/
noncomputable section
namespace PaperI
open Filter
open scoped Topology

theorem originalGaussShear_fderiv (c : (Fin 2 → ℝ) → ℝ) (v u : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c v) (hr : originalGaussR c v ≠ 0) :
    fderiv ℝ (originalGaussShear c) v u =
      -(fderiv ℝ (originalGaussS c) v u*originalGaussR c v-
        originalGaussS c v*fderiv ℝ (originalGaussR c) v u)/originalGaussR c v^2 := by
  obtain ⟨hR,hS⟩ := originalGauss_R_S_differentiableAt c v hc
  have hd := hS.hasFDerivAt.neg.mul ((hasFDerivAt_inv hr).comp v hR.hasFDerivAt)
  have he := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L u) hd.fderiv
  have hf : fderiv ℝ (originalGaussShear c) v u =
      -originalGaussS c v*(fderiv ℝ (originalGaussR c) v u*(-(originalGaussR c v^2)⁻¹))+
        (originalGaussR c v)⁻¹*(-fderiv ℝ (originalGaussS c) v u) := by
    change fderiv ℝ (fun y => -originalGaussS c y * (originalGaussR c y)⁻¹) v u = _
    simpa using he
  rw [hf]
  field_simp [hr]
  ring

theorem originalGauss_same_shear_fderiv (c Y : (Fin 2 → ℝ) → ℝ) (a u : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c ![Y a,a 1]) (hY : DifferentiableAt ℝ Y a)
    (hr : originalGaussR c ![Y a,a 1] ≠ 0)
    (hright : ∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0) :
    fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a u =
      fderiv ℝ (originalGaussShear c) ![Y a,a 1]
        ![u 0/originalGaussR c ![Y a,a 1]+originalGaussShear c ![Y a,a 1]*u 1,u 1] := by
  have hd := (originalGauss_shear_differentiableAt c _ hc hr).hasFDerivAt.comp a
    (originalGauss_inverse_base_hasFDerivAt Y a hY)
  have he := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L u) hd.fderiv
  have he' : fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a u =
      fderiv ℝ (originalGaussShear c) ![Y a,a 1] ![fderiv ℝ Y a u,u 1] := by
    simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,
      originalGauss_inverse_base_derivative_apply] using he
  rw [he',originalGauss_same_inverse_fderiv c Y a u (hc.of_le (by decide)) hY hr hright]

theorem originalGauss_same_shear_dp (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c ![Y a,a 1]) (hY : DifferentiableAt ℝ Y a)
    (hr : originalGaussR c ![Y a,a 1] ≠ 0)
    (hright : ∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0) :
    fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![1,0] =
      -originalGaussUUV (originalGaussFrozenGraph c ![Y a,a 1]) 0/originalGaussR c ![Y a,a 1]^2 := by
  rw [originalGauss_same_shear_fderiv c Y a ![1,0] hc hY hr hright,
    originalGaussShear_fderiv c _ _ hc hr,originalGaussFrozenGraph_UUV c _ hc,
    originalGauss_linear_apply_two (fderiv ℝ (originalGaussS c) ![Y a,a 1]),
    originalGauss_linear_apply_two (fderiv ℝ (originalGaussR c) ![Y a,a 1])]
  simp [originalGaussShear]
  field_simp [hr]
  ring

theorem originalGauss_same_shear_dz (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c ![Y a,a 1]) (hY : DifferentiableAt ℝ Y a)
    (hr : originalGaussR c ![Y a,a 1] ≠ 0)
    (hright : ∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0) :
    fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![0,1] =
      -originalGaussUVV (originalGaussFrozenGraph c ![Y a,a 1]) 0/originalGaussR c ![Y a,a 1] := by
  rw [originalGauss_same_shear_fderiv c Y a ![0,1] hc hY hr hright,
    originalGaussShear_fderiv c _ _ hc hr,originalGaussFrozenGraph_UVV c _ hc,
    originalGauss_linear_apply_two (fderiv ℝ (originalGaussS c) ![Y a,a 1]),
    originalGauss_linear_apply_two (fderiv ℝ (originalGaussR c) ![Y a,a 1]),
    originalGauss_third_mixed_partials c _ hc]
  simp [originalGaussShear]
  field_simp [hr]
  ring

theorem originalGaussFrozenGraph_eq_frame_pullback (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ)
    (hp : originalGaussCy c ![Y a,a 1]=a 0) :
    originalGaussFrozenGraph c ![Y a,a 1] = originalGaussGraphPullback (originalGaussFrameField c Y a) c := by
  unfold originalGaussFrozenGraph originalGaussFrameField
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,hp]

theorem originalGauss_same_shear_original_frame (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c ![Y a,a 1]) (hY : DifferentiableAt ℝ Y a)
    (hr : originalGaussR c ![Y a,a 1] ≠ 0)
    (hright : ∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0) :
    originalGaussS (originalGaussGraphPullback (originalGaussFrameField c Y a) c) 0 = 0 ∧
    fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![1,0] =
      -originalGaussUUV (originalGaussGraphPullback (originalGaussFrameField c Y a) c) 0/originalGaussR c ![Y a,a 1]^2 ∧
    fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![0,1] =
      -originalGaussUVV (originalGaussGraphPullback (originalGaussFrameField c Y a) c) 0/originalGaussR c ![Y a,a 1] := by
  rw [← originalGaussFrozenGraph_eq_frame_pullback c Y a hright.self_of_nhds]
  exact ⟨originalGaussFrozenGraph_mixed_zero c _ (hc.of_le (by decide)) hr,
    originalGauss_same_shear_dp c Y a hc hY hr hright,originalGauss_same_shear_dz c Y a hc hY hr hright⟩

end PaperI
