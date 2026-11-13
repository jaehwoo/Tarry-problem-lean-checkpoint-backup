import PaperILean.OriginalGaussBodyMatrix

/-! Smoothness of the original normal graph, obtained from the same IFT and
its uniqueness. This discharges the C3 calculus requirement without adding a
manuscript hypothesis or replacing the selected graph. -/
noncomputable section
namespace PaperI
open Filter
open scoped Topology ContDiff

theorem originalNormal_local_graph_of_order
    (G : (Fin 3 → ℝ) → ℝ) (x : ℝ) (v : Fin 2 → ℝ)
    (n : WithTop ℕ∞) (hn : 1 ≤ n)
    (hG : ContDiffAt ℝ n G ![x,v 0,v 1]) (hzero : G ![x,v 0,v 1]=0)
    (hk : fderiv ℝ G ![x,v 0,v 1] ![1,0,0]≠0) :
    ∃ c : (Fin 2 → ℝ) → ℝ, c v=x ∧ ContDiffAt ℝ n c v ∧
      (∀ᶠ w in 𝓝 v, G ![c w,w 0,w 1]=0) ∧
      (∀ᶠ u in 𝓝 (![x,v 0,v 1] : Fin 3 → ℝ),
        G u=0 → u 0=c ![u 1,u 2]) := by
  let g := G ∘ originalNormalCoordinates
  let a := fderiv ℝ G ![x,v 0,v 1] ![1,0,0]
  have hg : ContDiffAt ℝ n g (v,x) := by
    have hGc : ContDiffAt ℝ n G (originalNormalCoordinates (v,x)) := by
      rwa [originalNormalCoordinates_apply]
    exact hGc.comp (v,x) originalNormalCoordinates.contDiff.contDiffAt
  have hline := (hG.differentiableAt hn).hasFDerivAt.comp_hasDerivAt x
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
  obtain ⟨c,hc,hcs,hcz,hcu⟩ := original_parameter_local_zero g v x n hn
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

theorem originalNormal_same_graph_contDiffAt
    (G : (Fin 3 → ℝ) → ℝ) (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (n : WithTop ℕ∞) (hn : 1 ≤ n)
    (hG : ContDiffAt ℝ n G ![c v,v 0,v 1]) (hc : ContinuousAt c v)
    (hroot : ∀ᶠ w in 𝓝 v, G ![c w,w 0,w 1]=0)
    (hk : fderiv ℝ G ![c v,v 0,v 1] ![1,0,0] ≠ 0) :
    ContDiffAt ℝ n c v := by
  obtain ⟨b,hb,hbs,hbz,hbu⟩ := originalNormal_local_graph_of_order G (c v) v n hn hG hroot.self_of_nhds hk
  have heq := originalNormal_graph_agrees_with_selected G (c v) v b c hbu hc rfl hroot
  exact hbs.congr_of_eventuallyEq heq

theorem originalNormalPhase_same_graph_smooth {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) (hc : ContinuousAt c v)
    (hroot : ∀ᶠ w in 𝓝 v, originalNormalPhase F n ![c w,w 0,w 1]=0)
    (hk : originalNormalPhase F (n+1) ![c v,v 0,v 1] ≠ 0) :
    ContDiffAt ℝ ∞ c v := by
  apply originalNormal_same_graph_contDiffAt (originalNormalPhase F n) c v ∞ (by simp)
    (originalNormalPhase_contDiff F n ∞).contDiffAt hc hroot
  rwa [originalNormalPhase_dx]

end PaperI
