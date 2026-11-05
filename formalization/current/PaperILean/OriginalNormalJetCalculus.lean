import PaperILean.OriginalGaussNormalizedApplication

/-! I1305: the first two steps of repeated implicit differentiation of the
same original normal graph. All derivatives below are actual Fréchet derivatives.
The coordinate spaces carry mathlib's finite product (maximum) norm. -/
noncomputable section
namespace PaperI
open Filter
open scoped Topology

def originalNormalLift (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![c v,v 0,v 1]
def originalNormalLiftLinear (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) :
    (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![fderiv ℝ c v,ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 1]

theorem originalNormalLiftLinear_apply (c : (Fin 2 → ℝ) → ℝ) (v u : Fin 2 → ℝ) :
    originalNormalLiftLinear c v u = ![fderiv ℝ c v u,u 0,u 1] := by
  ext i; fin_cases i <;> rfl

theorem originalNormalLift_hasFDerivAt (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hc : DifferentiableAt ℝ c v) :
    HasFDerivAt (originalNormalLift c) (originalNormalLiftLinear c v) v := by
  apply hasFDerivAt_pi'.mpr
  intro i; fin_cases i
  · exact hc.hasFDerivAt
  · exact hasFDerivAt_apply 0 v
  · exact hasFDerivAt_apply 1 v

theorem originalNormal_linear_normal (L : (Fin 3 → ℝ) →L[ℝ] ℝ) (a : ℝ) :
    L ![a,0,0] = a * L ![1,0,0] := by
  have he : (![a,0,0] : Fin 3 → ℝ)=a • ![1,0,0] := by ext i; fin_cases i <;> simp
  rw [he,map_smul]; rfl

theorem originalNormal_clm_apply_fderiv
    {E U V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : E → U →L[ℝ] V) (b : E → U) (v u : E)
    (hA : DifferentiableAt ℝ A v) (hb : DifferentiableAt ℝ b v) :
    fderiv ℝ (fun x => A x (b x)) v u =
      A v (fderiv ℝ b v u) + fderiv ℝ A v u (b v) := by
  simpa using congrArg (fun L : E →L[ℝ] V => L u) (hA.hasFDerivAt.clm_apply hb.hasFDerivAt).fderiv

theorem originalNormalLiftLinear_fderiv
    (c : (Fin 2 → ℝ) → ℝ) (v u w : Fin 2 → ℝ) (hc : ContDiffAt ℝ 2 c v) :
    fderiv ℝ (fun t => originalNormalLiftLinear c t u) v w =
      ![fderiv ℝ (fderiv ℝ c) v w u,0,0] := by
  have hp : DifferentiableAt ℝ (fun t => fderiv ℝ c t u) v :=
    ((hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hd : HasFDerivAt (fun t => originalNormalLiftLinear c t u)
      (ContinuousLinearMap.pi ![fderiv ℝ (fun t => fderiv ℝ c t u) v,0,0]) v := by
    apply hasFDerivAt_pi'.mpr
    intro i; fin_cases i
    · exact hp.hasFDerivAt
    · exact hasFDerivAt_const (u 0) v
    · exact hasFDerivAt_const (u 1) v
  rw [hd.fderiv]
  ext i; fin_cases i
  · exact originalGauss_partial_fderiv c v u w hc
  · rfl
  · rfl

theorem originalNormalLiftLinear_differentiableAt
    (c : (Fin 2 → ℝ) → ℝ) (v u : Fin 2 → ℝ) (hc : ContDiffAt ℝ 2 c v) :
    DifferentiableAt ℝ (fun t => originalNormalLiftLinear c t u) v := by
  apply differentiableAt_pi.mpr
  intro i; fin_cases i
  · exact ((hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  · exact differentiableAt_const (u 0)
  · exact differentiableAt_const (u 1)

theorem originalNormal_root_first_identity
    (G : (Fin 3 → ℝ) → ℝ) (c : (Fin 2 → ℝ) → ℝ) (v u : Fin 2 → ℝ)
    (hG : DifferentiableAt ℝ G (originalNormalLift c v)) (hc : DifferentiableAt ℝ c v)
    (hroot : ∀ᶠ t in 𝓝 v, G (originalNormalLift c t)=0) :
    fderiv ℝ G (originalNormalLift c v) (originalNormalLiftLinear c v u)=0 := by
  have h := (hG.hasFDerivAt.comp v (originalNormalLift_hasFDerivAt c v hc)).unique
    ((hasFDerivAt_const (0 : ℝ) v).congr_of_eventuallyEq hroot)
  simpa using congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L u) h

theorem originalNormal_root_first_equation
    (G : (Fin 3 → ℝ) → ℝ) (c : (Fin 2 → ℝ) → ℝ) (v u : Fin 2 → ℝ)
    (hG : DifferentiableAt ℝ G (originalNormalLift c v)) (hc : DifferentiableAt ℝ c v)
    (hroot : ∀ᶠ t in 𝓝 v, G (originalNormalLift c t)=0) :
    fderiv ℝ c v u * fderiv ℝ G (originalNormalLift c v) ![1,0,0] +
      fderiv ℝ G (originalNormalLift c v) ![0,u 0,u 1]=0 := by
  have h := originalNormal_root_first_identity G c v u hG hc hroot
  have he : originalNormalLiftLinear c v u =
      (![fderiv ℝ c v u,0,0] : Fin 3 → ℝ)+![0,u 0,u 1] := by
    rw [originalNormalLiftLinear_apply]; ext i; fin_cases i <;> simp
  rwa [he,map_add,originalNormal_linear_normal] at h

theorem originalNormal_root_second_identity
    (G : (Fin 3 → ℝ) → ℝ) (c : (Fin 2 → ℝ) → ℝ) (v u w : Fin 2 → ℝ)
    (hG : ContDiffAt ℝ 2 G (originalNormalLift c v)) (hc : ContDiffAt ℝ 2 c v)
    (hroot : ∀ᶠ t in 𝓝 v, G (originalNormalLift c t)=0) :
    fderiv ℝ (fderiv ℝ G) (originalNormalLift c v)
        (originalNormalLiftLinear c v w) (originalNormalLiftLinear c v u) +
      fderiv ℝ (fderiv ℝ c) v w u * fderiv ℝ G (originalNormalLift c v) ![1,0,0]=0 := by
  have hX := originalNormalLift_hasFDerivAt c v (hc.differentiableAt (by norm_num))
  have hDG := (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA := hDG.comp v hX.differentiableAt
  have hroots : (fun t => G (originalNormalLift c t)) =ᶠ[𝓝 v] (fun _ => 0) := hroot
  have he : (fun t => fderiv ℝ G (originalNormalLift c t) (originalNormalLiftLinear c t u)) =ᶠ[𝓝 v] (fun _ => 0) := by
    filter_upwards [hX.continuousAt.eventually (hG.eventually (by norm_num)),hc.eventually (by norm_num),hroots.eventuallyEq_nhds] with t htG htc htr
    exact originalNormal_root_first_identity G c t u (htG.differentiableAt (by norm_num)) (htc.differentiableAt (by norm_num)) htr
  have hd := originalNormal_clm_apply_fderiv (fun t => fderiv ℝ G (originalNormalLift c t))
    (fun t => originalNormalLiftLinear c t u) v w hA (originalNormalLiftLinear_differentiableAt c v u hc)
  rw [he.fderiv_eq] at hd
  have hcomp := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ((Fin 3 → ℝ) →L[ℝ] ℝ) => L w)
    (hDG.hasFDerivAt.comp v hX).fderiv
  simp only [Function.comp_def,ContinuousLinearMap.comp_apply] at hcomp
  rw [hcomp,originalNormalLiftLinear_fderiv c v u w hc,originalNormal_linear_normal] at hd
  simpa [add_comm] using hd.symm

end PaperI
