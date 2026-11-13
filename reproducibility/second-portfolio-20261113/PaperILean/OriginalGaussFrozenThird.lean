import PaperILean.OriginalGaussPullbackCalculus

/-! The literal frozen-frame graph and its actual normalized derivatives.
No coefficient stands in for a derivative without a proved equality. -/
noncomputable section
namespace PaperI
open Filter
open scoped Topology

def originalGaussUUV (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) : ℝ :=
  fderiv ℝ (originalGaussR c) v ![0,1]
def originalGaussUVV (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) : ℝ :=
  fderiv ℝ (originalGaussS c) v ![0,1]

def originalGaussFrozenGraph (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) : (Fin 2 → ℝ) → ℝ :=
  originalGaussGraphPullback
    (originalGaussNormalFrame (originalGaussCy c v) (v 1) (c v) (v 0)
      (originalGaussCz c v) (originalGaussShear c v)) c

theorem originalGauss_R_S_differentiableAt (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c v) :
    DifferentiableAt ℝ (originalGaussR c) v ∧ DifferentiableAt ℝ (originalGaussS c) v := by
  have hP : ContDiffAt ℝ 2 (originalGaussCy c) v :=
    (hc.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  have hd := hP.fderiv_right (m := 1) (by norm_num)
  exact ⟨(hd.clm_apply contDiffAt_const).differentiableAt (by norm_num),
    (hd.clm_apply contDiffAt_const).differentiableAt (by norm_num)⟩

theorem originalGauss_third_mixed_partials (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c v) :
    fderiv ℝ (originalGaussR c) v ![0,1] = fderiv ℝ (originalGaussS c) v ![1,0] := by
  have hP : ContDiffAt ℝ 2 (originalGaussCy c) v :=
    (hc.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  exact (originalGauss_mixed_partials (originalGaussCy c) v hP).symm

theorem originalGaussGraphPullback_R_fderiv (c : (Fin 2 → ℝ) → ℝ)
    (g : Fin 6 → ℝ) (v u : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c (originalGaussGraphBaseChange g v)) :
    fderiv ℝ (originalGaussR (originalGaussGraphPullback g c)) v u =
      fderiv ℝ (originalGaussR c) (originalGaussGraphBaseChange g v) ![u 0+g 3*u 1,u 1] := by
  have he : originalGaussR (originalGaussGraphPullback g c) =ᶠ[𝓝 v]
      (fun w => originalGaussR c (originalGaussGraphBaseChange g w)) := by
    filter_upwards [(originalGaussGraphBaseChange_hasFDerivAt g v).continuousAt.eventually
      (hc.eventually (by norm_num))] with w hw
    exact originalGaussGraphPullback_R c g w (hw.of_le (by decide))
  rw [he.fderiv_eq]
  exact originalGauss_base_comp_fderiv _ g v u (originalGauss_R_S_differentiableAt c _ hc).1

theorem originalGaussGraphPullback_S_fderiv (c : (Fin 2 → ℝ) → ℝ)
    (g : Fin 6 → ℝ) (v u : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c (originalGaussGraphBaseChange g v)) :
    fderiv ℝ (originalGaussS (originalGaussGraphPullback g c)) v u =
      g 3*fderiv ℝ (originalGaussR c) (originalGaussGraphBaseChange g v) ![u 0+g 3*u 1,u 1]+
        fderiv ℝ (originalGaussS c) (originalGaussGraphBaseChange g v) ![u 0+g 3*u 1,u 1] := by
  have he : originalGaussS (originalGaussGraphPullback g c) =ᶠ[𝓝 v]
      (fun w => g 3*originalGaussR c (originalGaussGraphBaseChange g w)+
        originalGaussS c (originalGaussGraphBaseChange g w)) := by
    filter_upwards [(originalGaussGraphBaseChange_hasFDerivAt g v).continuousAt.eventually
      (hc.eventually (by norm_num))] with w hw
    exact originalGaussGraphPullback_S c g w (hw.of_le (by decide))
  rw [he.fderiv_eq]
  obtain ⟨hR,hS⟩ := originalGauss_R_S_differentiableAt c _ hc
  have hB := originalGaussGraphBaseChange_hasFDerivAt g v
  have hd := ((hR.hasFDerivAt.comp v hB).const_mul (g 3)).add (hS.hasFDerivAt.comp v hB)
  have h := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L u) hd.fderiv
  simpa [Function.comp_def,originalGaussBaseLinear_apply] using h

theorem originalGaussFrozenGraph_formula (c : (Fin 2 → ℝ) → ℝ) (v w : Fin 2 → ℝ) :
    originalGaussFrozenGraph c v w =
      c ![w 0+originalGaussShear c v*w 1+v 0,w 1+v 1] -
        originalGaussCy c v*w 0-(originalGaussCz c v+originalGaussShear c v*originalGaussCy c v)*w 1-c v := by
  simp [originalGaussFrozenGraph,originalGaussGraphPullback,originalGaussGraphBaseChange,originalGaussNormalFrame]

theorem originalGaussFrozenGraph_base (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) :
    originalGaussGraphBaseChange
      (originalGaussNormalFrame (originalGaussCy c v) (v 1) (c v) (v 0)
        (originalGaussCz c v) (originalGaussShear c v)) 0 = v := by
  ext i
  fin_cases i <;> simp [originalGaussGraphBaseChange,originalGaussNormalFrame]

theorem originalGaussFrozenGraph_value (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) :
    originalGaussFrozenGraph c v 0 = 0 := by
  unfold originalGaussFrozenGraph originalGaussGraphPullback
  rw [originalGaussFrozenGraph_base]
  simp [originalGaussNormalFrame]

theorem originalGaussFrozenGraph_R (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 2 c v) :
    originalGaussR (originalGaussFrozenGraph c v) 0 = originalGaussR c v := by
  unfold originalGaussFrozenGraph
  rw [originalGaussGraphPullback_R,originalGaussFrozenGraph_base]
  simpa only [originalGaussFrozenGraph_base] using hc

theorem originalGaussFrozenGraph_mixed_zero (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 2 c v) (hr : originalGaussR c v ≠ 0) :
    originalGaussS (originalGaussFrozenGraph c v) 0 = 0 := by
  unfold originalGaussFrozenGraph
  rw [originalGaussGraphPullback_S,originalGaussFrozenGraph_base]
  · simp [originalGaussNormalFrame,originalGaussShear,hr]
  · simpa only [originalGaussFrozenGraph_base] using hc

theorem originalGaussFrozenGraph_UUV (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c v) :
    originalGaussUUV (originalGaussFrozenGraph c v) 0 =
      fderiv ℝ (originalGaussS c) v ![1,0]+
        originalGaussShear c v*fderiv ℝ (originalGaussR c) v ![1,0] := by
  unfold originalGaussUUV originalGaussFrozenGraph
  rw [originalGaussGraphPullback_R_fderiv,originalGaussFrozenGraph_base]
  · rw [originalGauss_linear_apply_two,originalGauss_third_mixed_partials c v hc]
    simp [originalGaussNormalFrame]
    ring
  · simpa only [originalGaussFrozenGraph_base] using hc

theorem originalGaussFrozenGraph_UVV (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c v) :
    originalGaussUVV (originalGaussFrozenGraph c v) 0 =
      fderiv ℝ (originalGaussS c) v ![0,1]+
        2*originalGaussShear c v*fderiv ℝ (originalGaussS c) v ![1,0]+
        originalGaussShear c v^2*fderiv ℝ (originalGaussR c) v ![1,0] := by
  unfold originalGaussUVV originalGaussFrozenGraph
  rw [originalGaussGraphPullback_S_fderiv,originalGaussFrozenGraph_base]
  · rw [originalGauss_linear_apply_two (fderiv ℝ (originalGaussR c) v),
      originalGauss_linear_apply_two (fderiv ℝ (originalGaussS c) v),
      originalGauss_third_mixed_partials c v hc]
    simp [originalGaussNormalFrame]
    ring
  · simpa only [originalGaussFrozenGraph_base] using hc

end PaperI
