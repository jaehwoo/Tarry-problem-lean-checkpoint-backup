import PaperILean.OriginalGaussBodyNeighborhood

/-! I1301-I1303: differentiate the existing graph pullback with its affine
frame fixed. Pointwise identities are extended to germs only by smoothness. -/
noncomputable section
namespace PaperI
open Filter
open scoped Topology

def originalGaussBaseLinear (g : Fin 6 → ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0 + g 3 • ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 1]

theorem originalGaussBaseLinear_apply (g : Fin 6 → ℝ) (u : Fin 2 → ℝ) :
    originalGaussBaseLinear g u = ![u 0+g 3*u 1,u 1] := by
  ext i
  fin_cases i <;> rfl

theorem originalGaussGraphBaseChange_hasFDerivAt (g : Fin 6 → ℝ) (v : Fin 2 → ℝ) :
    HasFDerivAt (originalGaussGraphBaseChange g) (originalGaussBaseLinear g) v := by
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · simpa [originalGaussGraphBaseChange,originalGaussBaseLinear] using
      ((hasFDerivAt_apply 0 v).add ((hasFDerivAt_apply 1 v).const_mul (g 3))).add_const (g 4)
  · simpa [originalGaussGraphBaseChange,originalGaussBaseLinear] using
      (hasFDerivAt_apply 1 v).add_const (g 5)

theorem originalGauss_base_comp_fderiv (f : (Fin 2 → ℝ) → ℝ)
    (g : Fin 6 → ℝ) (v u : Fin 2 → ℝ)
    (hf : DifferentiableAt ℝ f (originalGaussGraphBaseChange g v)) :
    fderiv ℝ (fun w => f (originalGaussGraphBaseChange g w)) v u =
      fderiv ℝ f (originalGaussGraphBaseChange g v) ![u 0+g 3*u 1,u 1] := by
  have he := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L u)
    (hf.hasFDerivAt.comp v (originalGaussGraphBaseChange_hasFDerivAt g v)).fderiv
  simpa [Function.comp_def,originalGaussBaseLinear_apply] using he

theorem originalGaussGraphPullback_fderiv (c : (Fin 2 → ℝ) → ℝ)
    (g : Fin 6 → ℝ) (v u : Fin 2 → ℝ)
    (hc : DifferentiableAt ℝ c (originalGaussGraphBaseChange g v)) :
    fderiv ℝ (originalGaussGraphPullback g c) v u =
      fderiv ℝ c (originalGaussGraphBaseChange g v) ![u 0+g 3*u 1,u 1] -
        g 0*u 0-g 1*u 1 := by
  have hd := (((hc.hasFDerivAt.comp v (originalGaussGraphBaseChange_hasFDerivAt g v)).sub
    ((hasFDerivAt_apply 0 v).const_mul (g 0))).sub
    ((hasFDerivAt_apply 1 v).const_mul (g 1))).sub_const (g 2)
  change fderiv ℝ (fun w => c (originalGaussGraphBaseChange g w)-g 0*w 0-g 1*w 1-g 2) v u = _
  have he := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L u) hd.fderiv
  simpa [Function.comp_def,originalGaussBaseLinear_apply] using he

theorem originalGaussGraphPullback_Cy (c : (Fin 2 → ℝ) → ℝ)
    (g : Fin 6 → ℝ) (v : Fin 2 → ℝ)
    (hc : DifferentiableAt ℝ c (originalGaussGraphBaseChange g v)) :
    originalGaussCy (originalGaussGraphPullback g c) v =
      originalGaussCy c (originalGaussGraphBaseChange g v)-g 0 := by
  unfold originalGaussCy
  rw [originalGaussGraphPullback_fderiv c g v ![1,0] hc]
  simp

theorem originalGaussGraphPullback_Cy_germ (c : (Fin 2 → ℝ) → ℝ)
    (g : Fin 6 → ℝ) (v : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 1 c (originalGaussGraphBaseChange g v)) :
    originalGaussCy (originalGaussGraphPullback g c) =ᶠ[𝓝 v]
      (fun w => originalGaussCy c (originalGaussGraphBaseChange g w)-g 0) := by
  filter_upwards [(originalGaussGraphBaseChange_hasFDerivAt g v).continuousAt.eventually
    (hc.eventually (by norm_num))] with w hw
  exact originalGaussGraphPullback_Cy c g w (hw.differentiableAt (by norm_num))

theorem originalGaussGraphPullback_Cy_fderiv (c : (Fin 2 → ℝ) → ℝ)
    (g : Fin 6 → ℝ) (v u : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 2 c (originalGaussGraphBaseChange g v)) :
    fderiv ℝ (originalGaussCy (originalGaussGraphPullback g c)) v u =
      fderiv ℝ (originalGaussCy c) (originalGaussGraphBaseChange g v) ![u 0+g 3*u 1,u 1] := by
  have hP : DifferentiableAt ℝ (originalGaussCy c) (originalGaussGraphBaseChange g v) :=
    ((hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  rw [(originalGaussGraphPullback_Cy_germ c g v (hc.of_le (by decide))).fderiv_eq]
  have he := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L u)
    ((hP.hasFDerivAt.comp v (originalGaussGraphBaseChange_hasFDerivAt g v)).sub_const (g 0)).fderiv
  simpa [Function.comp_def,originalGaussBaseLinear_apply] using he

theorem originalGaussGraphPullback_R (c : (Fin 2 → ℝ) → ℝ)
    (g : Fin 6 → ℝ) (v : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 2 c (originalGaussGraphBaseChange g v)) :
    originalGaussR (originalGaussGraphPullback g c) v =
      originalGaussR c (originalGaussGraphBaseChange g v) := by
  unfold originalGaussR
  rw [originalGaussGraphPullback_Cy_fderiv c g v ![1,0] hc]
  simp

theorem originalGaussGraphPullback_S (c : (Fin 2 → ℝ) → ℝ)
    (g : Fin 6 → ℝ) (v : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 2 c (originalGaussGraphBaseChange g v)) :
    originalGaussS (originalGaussGraphPullback g c) v =
      g 3*originalGaussR c (originalGaussGraphBaseChange g v)+
        originalGaussS c (originalGaussGraphBaseChange g v) := by
  unfold originalGaussS
  rw [originalGaussGraphPullback_Cy_fderiv c g v ![0,1] hc,originalGauss_linear_apply_two]
  simp [originalGaussR]

end PaperI
