import PaperILean.OriginalNormalImplicitFunction
import PaperILean.OriginalGaussRootIsolation

/-! I750-I755 and I1279-I1283: construct the actual local normal graph
from the nonzero x derivative. Keep arbitrary base points, both derivative
signs, and every nearby zero. No quantitative or common-choice conclusion.
-/
noncomputable section
namespace PaperI
open Filter
open scoped Topology

def originalNormalCoordinates : ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ℝ,
    (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ),
    (ContinuousLinearMap.proj 1).comp (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ)]

theorem originalNormalCoordinates_apply (v : Fin 2 → ℝ) (x : ℝ) :
    originalNormalCoordinates (v,x)=![x,v 0,v 1] := by
  ext i
  fin_cases i <;> rfl

def originalNormalScalarEquiv (a : ℝ) (ha : a≠0) : ℝ ≃L[ℝ] ℝ :=
  (LinearEquiv.smulOfNeZero ℝ ℝ a ha).toContinuousLinearEquiv

theorem originalNormalScalarEquiv_apply (a : ℝ) (ha : a≠0) (t : ℝ) :
    originalNormalScalarEquiv a ha t=a*t := rfl

theorem originalNormal_xline_hasDerivAt (v : Fin 2 → ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (![t,v 0,v 1] : Fin 3 → ℝ)) ![1,0,0] x := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_id x
  · exact hasDerivAt_const x (v 0)
  · exact hasDerivAt_const x (v 1)

theorem originalNormal_local_graph
    (G : (Fin 3 → ℝ) → ℝ) (x : ℝ) (v : Fin 2 → ℝ)
    (hG : ContDiffAt ℝ 2 G ![x,v 0,v 1]) (hzero : G ![x,v 0,v 1]=0)
    (hk : fderiv ℝ G ![x,v 0,v 1] ![1,0,0]≠0) :
    ∃ c : (Fin 2 → ℝ) → ℝ, c v=x ∧ ContDiffAt ℝ 2 c v ∧
      (∀ᶠ w in 𝓝 v, G ![c w,w 0,w 1]=0) ∧
      (∀ᶠ u in 𝓝 (![x,v 0,v 1] : Fin 3 → ℝ),
        G u=0 → u 0=c ![u 1,u 2]) := by
  let g := G ∘ originalNormalCoordinates
  let a := fderiv ℝ G ![x,v 0,v 1] ![1,0,0]
  have hg : ContDiffAt ℝ 2 g (v,x) := by
    have hGc : ContDiffAt ℝ 2 G (originalNormalCoordinates (v,x)) := by
      rwa [originalNormalCoordinates_apply]
    exact hGc.comp (v,x) originalNormalCoordinates.contDiff.contDiffAt
  have hline := (hG.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x
    (originalNormal_xline_hasDerivAt v x)
  have hL : HasFDerivAt (fun t => g (v,t))
      (originalNormalScalarEquiv a hk).toContinuousLinearMap x := by
    have hf : (fun t => g (v,t))=(fun t => G ![t,v 0,v 1]) := by
      funext t
      simp only [g,Function.comp_apply,originalNormalCoordinates_apply]
    have he : (originalNormalScalarEquiv a hk).toContinuousLinearMap=
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a := by
      apply ContinuousLinearMap.ext
      intro t
      change a*t=t*a
      exact mul_comm a t
    rw [hf,he]
    exact hline.hasFDerivAt
  have hz : g (v,x)=0 := by
    simpa only [g,Function.comp_apply,originalNormalCoordinates_apply] using hzero
  obtain ⟨c,hc,hcs,hcz,hcu⟩ := original_parameter_local_zero g v x 2 (by norm_num)
    hg hz (originalNormalScalarEquiv a hk) hL
  refine ⟨c,hc,hcs,?_,?_⟩
  · simpa only [g,Function.comp_apply,originalNormalCoordinates_apply] using hcz
  have hcont : ContinuousAt (fun u : Fin 3 → ℝ => ((![u 1,u 2] : Fin 2 → ℝ),u 0))
      ![x,v 0,v 1] := by
    apply ContinuousAt.prodMk
    · apply continuousAt_pi.mpr
      intro i
      fin_cases i <;> exact (continuous_apply _).continuousAt
    · exact (continuous_apply 0).continuousAt
  have hbase : (![v 0,v 1] : Fin 2 → ℝ)=v := by ext i; fin_cases i <;> rfl
  have ht : Tendsto (fun u : Fin 3 → ℝ => ((![u 1,u 2] : Fin 2 → ℝ),u 0))
      (𝓝 ![x,v 0,v 1]) (𝓝 (v,x)) := by
    have heval : (fun u : Fin 3 → ℝ => ((![u 1,u 2] : Fin 2 → ℝ),u 0))
        ![x,v 0,v 1]=(v,x) := Prod.ext hbase rfl
    unfold ContinuousAt at hcont
    rw [heval] at hcont
    exact hcont
  filter_upwards [ht.eventually hcu] with u hu hzu
  apply hu
  have he : originalNormalCoordinates (![u 1,u 2],u 0)=u := by
    ext i
    fin_cases i <;> rfl
  simpa only [g,Function.comp_apply,he] using hzu

theorem originalNormal_graph_agrees_with_selected
    (G : (Fin 3 → ℝ) → ℝ) (x : ℝ) (v : Fin 2 → ℝ)
    (c b : (Fin 2 → ℝ) → ℝ)
    (hunique : ∀ᶠ u in 𝓝 (![x,v 0,v 1] : Fin 3 → ℝ), G u=0 → u 0=c ![u 1,u 2])
    (hb : ContinuousAt b v) (hbv : b v=x)
    (hroot : ∀ᶠ w in 𝓝 v, G ![b w,w 0,w 1]=0) : b =ᶠ[𝓝 v] c := by
  have ht : Tendsto (fun w : Fin 2 → ℝ => (![b w,w 0,w 1] : Fin 3 → ℝ))
      (𝓝 v) (𝓝 ![x,v 0,v 1]) := by
    rw [← hbv]
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · exact hb
    · exact (continuous_apply 0).continuousAt
    · exact (continuous_apply 1).continuousAt
  filter_upwards [ht.eventually hunique,hroot] with w hw hz
  have h := hw hz
  have he : (![w 0,w 1] : Fin 2 → ℝ)=w := by ext i; fin_cases i <;> rfl
  change b w=c ![w 0,w 1] at h
  rwa [he] at h

theorem originalNormal_graph_slice
    (G : (Fin 3 → ℝ) → ℝ) (c : (Fin 2 → ℝ) → ℝ) (y z : ℝ)
    (hc : ContDiffAt ℝ 2 c ![y,z])
    (hroot : ∀ᶠ w in 𝓝 (![y,z] : Fin 2 → ℝ), G ![c w,w 0,w 1]=0) :
    ContDiffAt ℝ 2 (fun t : ℝ => c ![t,z]) y ∧
      (fun t => G ![c ![t,z],t,z]) =ᶠ[𝓝 y] (fun _ => 0) := by
  have hline : ContDiff ℝ 2 (fun t : ℝ => (![t,z] : Fin 2 → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_id
    · exact contDiff_const
  exact ⟨hc.comp y hline.contDiffAt,hline.continuous.continuousAt.eventually hroot⟩

end PaperI
