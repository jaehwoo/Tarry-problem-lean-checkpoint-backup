import PaperILean.OriginalGaussInverseChart

/-! I1280-I1284: identify the two equations and their differential, and
specialize the local graph calculation to the original three-variable phase
with z held fixed. No regular branch is selected or discarded by this step.
-/
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology

theorem originalGaussRootEquations_second (G : (Fin 2 → ℝ) → ℝ) (p : ℝ) (x : Fin 2 → ℝ) :
    originalGaussRootEquations G p x 1=fderiv ℝ G x ![0,1]+p*fderiv ℝ G x ![1,0] := by
  change fderiv ℝ G x ![p,1]=_
  rw [originalGauss_linear_apply_two _ ![p,1]]
  simp
  ring

theorem originalGaussRootEquations_hasFDerivAt
    (G : (Fin 2 → ℝ) → ℝ) (p : ℝ) (x : Fin 2 → ℝ) (hG : ContDiffAt ℝ 2 G x) :
    HasFDerivAt (originalGaussRootEquations G p)
      (ContinuousLinearMap.pi ![fderiv ℝ G x,
        fderiv ℝ (fun u => fderiv ℝ G u ![p,1]) x]) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (hG.differentiableAt (by norm_num)).hasFDerivAt
  · exact (((hG.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)).hasFDerivAt

def originalGaussXYEmbedding : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 1,0]

theorem originalGaussXYEmbedding_hasFDerivAt (z : ℝ) (x : Fin 2 → ℝ) :
    HasFDerivAt (fun u => (![u 0,u 1,z] : Fin 3 → ℝ)) originalGaussXYEmbedding x := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasFDerivAt_apply 0 x
  · exact hasFDerivAt_apply 1 x
  · exact hasFDerivAt_const (𝕜 := ℝ) z x

theorem originalGaussXYEmbedding_contDiff (z : ℝ) :
    ContDiff ℝ 2 (fun u : Fin 2 → ℝ => (![u 0,u 1,z] : Fin 3 → ℝ)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff
  · exact (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff
  · exact contDiff_const

def originalGaussPhaseSlice (G : (Fin 3 → ℝ) → ℝ) (z : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  G ![x 0,x 1,z]

theorem originalGaussPhaseSlice_contDiffAt
    (G : (Fin 3 → ℝ) → ℝ) (z : ℝ) (x : Fin 2 → ℝ)
    (hG : ContDiffAt ℝ 2 G ![x 0,x 1,z]) :
    ContDiffAt ℝ 2 (originalGaussPhaseSlice G z) x :=
  hG.comp x (originalGaussXYEmbedding_contDiff z).contDiffAt

theorem originalGaussPhaseSlice_dx
    (G : (Fin 3 → ℝ) → ℝ) (z : ℝ) (x : Fin 2 → ℝ)
    (hG : DifferentiableAt ℝ G ![x 0,x 1,z]) :
    fderiv ℝ (originalGaussPhaseSlice G z) x ![1,0]=
      fderiv ℝ G ![x 0,x 1,z] ![1,0,0] := by
  have hd := hG.hasFDerivAt.comp x (originalGaussXYEmbedding_hasFDerivAt z x)
  change fderiv ℝ (G ∘ (fun u => (![u 0,u 1,z] : Fin 3 → ℝ))) x ![1,0]=_
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  funext i
  fin_cases i <;> simp [originalGaussXYEmbedding]

theorem originalGauss_phase_root_jacobian_det
    (G : (Fin 3 → ℝ) → ℝ) (c : ℝ → ℝ) (y z : ℝ)
    (hG : ContDiffAt ℝ 2 G ![c y,y,z]) (hc : ContDiffAt ℝ 2 c y)
    (hroot : (fun t => G ![c t,t,z]) =ᶠ[𝓝 y] (fun _ => 0)) :
    (originalGaussRootJacobian (originalGaussPhaseSlice G z) (deriv c y) ![c y,y]).det=
      -(fderiv ℝ G ![c y,y,z] ![1,0,0])^2*deriv (deriv c) y := by
  rw [originalGauss_root_jacobian_det (originalGaussPhaseSlice G z) c y
    (originalGaussPhaseSlice_contDiffAt G z ![c y,y] hG) hc hroot]
  rw [originalGaussPhaseSlice_dx G z ![c y,y] (hG.differentiableAt (by norm_num))]
  rfl

theorem originalGauss_regular_phase_root_jacobian_ne_zero
    (G : (Fin 3 → ℝ) → ℝ) (c : ℝ → ℝ) (y z : ℝ)
    (hG : ContDiffAt ℝ 2 G ![c y,y,z]) (hc : ContDiffAt ℝ 2 c y)
    (hroot : (fun t => G ![c t,t,z]) =ᶠ[𝓝 y] (fun _ => 0))
    (hk : fderiv ℝ G ![c y,y,z] ![1,0,0]≠0) (hr : deriv (deriv c) y≠0) :
    (originalGaussRootJacobian (originalGaussPhaseSlice G z) (deriv c y) ![c y,y]).det≠0 := by
  rw [originalGauss_phase_root_jacobian_det G c y z hG hc hroot]
  exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hk)) hr

theorem originalGaussPhaseSlice_directional
    (G : (Fin 3 → ℝ) → ℝ) (z : ℝ) (x v : Fin 2 → ℝ)
    (hG : DifferentiableAt ℝ G ![x 0,x 1,z]) :
    fderiv ℝ (originalGaussPhaseSlice G z) x v=
      fderiv ℝ G ![x 0,x 1,z] ![v 0,v 1,0] := by
  have hd := hG.hasFDerivAt.comp x (originalGaussXYEmbedding_hasFDerivAt z x)
  change fderiv ℝ (G ∘ (fun u => (![u 0,u 1,z] : Fin 3 → ℝ))) x v=_
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  funext i
  fin_cases i <;> simp [originalGaussXYEmbedding]

theorem originalGauss_phase_root_equations
    (G : (Fin 3 → ℝ) → ℝ) (z p : ℝ) (x : Fin 2 → ℝ)
    (hG : DifferentiableAt ℝ G ![x 0,x 1,z]) :
    originalGaussRootEquations (originalGaussPhaseSlice G z) p x=
      ![G ![x 0,x 1,z],fderiv ℝ G ![x 0,x 1,z] ![0,1,0]+p*fderiv ℝ G ![x 0,x 1,z] ![1,0,0]] := by
  funext i
  fin_cases i
  · rfl
  · change originalGaussRootEquations (originalGaussPhaseSlice G z) p x 1=_
    rw [originalGaussRootEquations_second,
      originalGaussPhaseSlice_directional G z x ![0,1] hG,
      originalGaussPhaseSlice_directional G z x ![1,0] hG]
    rfl

end PaperI
