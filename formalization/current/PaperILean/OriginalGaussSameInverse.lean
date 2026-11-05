import PaperILean.OriginalGaussChartRegularity

/-! I1287-I1295: C1 regularity of the same inverse of (c_y,z), and local
agreement with the retained root section. The original basepoint derivative
identities are retained. No higher conditioned or full-parent bound is asserted. -/
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology ContDiff

theorem originalGauss_inverse_contDiffAt
    (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) (hc : ContDiffAt ℝ 2 c v)
    (hr : fderiv ℝ (fun x => fderiv ℝ c x ![1,0]) v ![1,0]≠0)
    (Y : (Fin 2 → ℝ) → ℝ) (hYv : Y ![fderiv ℝ c v ![1,0],v 1]=v 0)
    (hY : ContinuousAt Y ![fderiv ℝ c v ![1,0],v 1])
    (hright : ∀ᶠ q in 𝓝 (![fderiv ℝ c v ![1,0],v 1] : Fin 2 → ℝ),
      fderiv ℝ c ![Y q,q 1] ![1,0]=q 0) :
    ContDiffAt ℝ 1 Y ![fderiv ℝ c v ![1,0],v 1] := by
  let Φ := originalGaussSlopeCoordinates c
  have hd := originalGaussSlopeCoordinates_hasFDerivAt c v hc hr
  have hΦ := originalGaussSlopeCoordinates_contDiffAt c v hc
  let ψ := hΦ.localInverse hd (by norm_num)
  have hs : ContDiffAt ℝ 1 ψ (Φ v) := hΦ.to_localInverse hd (by norm_num)
  have hleft : ∀ᶠ w in 𝓝 v, ψ (Φ w)=w :=
    (hΦ.hasStrictFDerivAt' hd (by norm_num)).eventually_left_inverse
  have ht : Tendsto (fun q : Fin 2 → ℝ => (![Y q,q 1] : Fin 2 → ℝ))
      (𝓝 (Φ v)) (𝓝 v) := by
    have hcont : ContinuousAt (fun q : Fin 2 → ℝ => (![Y q,q 1] : Fin 2 → ℝ)) (Φ v) := by
      apply continuousAt_pi.mpr
      intro i
      fin_cases i
      · exact hY
      · exact (continuous_apply 1).continuousAt
    have hv : (![Y (Φ v),(Φ v) 1] : Fin 2 → ℝ)=v := by
      ext i
      fin_cases i
      · exact hYv
      · rfl
    change Tendsto _ _ (𝓝 (![Y (Φ v),(Φ v) 1] : Fin 2 → ℝ)) at hcont
    rwa [hv] at hcont
  have heq : Y =ᶠ[𝓝 (Φ v)] (fun q => ψ q 0) := by
    filter_upwards [ht.eventually hleft,hright] with q hq hqr
    have he : Φ ![Y q,q 1]=q := by
      ext i
      fin_cases i
      · exact hqr
      · rfl
    rw [he] at hq
    exact (congrFun hq 0).symm
  exact ((contDiff_apply ℝ ℝ 0).contDiffAt.comp (Φ v) hs).congr_of_eventuallyEq heq

theorem originalGauss_local_C1_inverse_chart
    (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) (hc : ContDiffAt ℝ 2 c v)
    (hr : fderiv ℝ (fun x => fderiv ℝ c x ![1,0]) v ![1,0]≠0) :
    let Pfun := fun x => fderiv ℝ c x ![1,0]
    let r := fderiv ℝ Pfun v ![1,0]
    let s := fderiv ℝ Pfun v ![0,1]
    ∃ Y : (Fin 2 → ℝ) → ℝ,
      Y ![Pfun v,v 1]=v 0 ∧ ContDiffAt ℝ 1 Y ![Pfun v,v 1] ∧
      (∀ᶠ q in 𝓝 ![Pfun v,v 1], Pfun ![Y q,q 1]=q 0) ∧
      (∀ᶠ w in 𝓝 v, Y ![Pfun w,w 1]=w 0) ∧
      HasDerivAt (fun t => Y ![t,v 1]) r⁻¹ (Pfun v) ∧
      HasDerivAt (fun t => Y ![Pfun v,t]) (-s/r) (v 1) := by
  obtain ⟨Y,hv,hY,hR,hL,hp,hz⟩ := originalGauss_local_inverse_chart c v hc hr
  exact ⟨Y,hv,originalGauss_inverse_contDiffAt c v hc hr Y hv hY hR,hR,hL,hp,hz⟩

theorem originalGauss_inverse_lift_is_local_zero {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (c : (Fin 2 → ℝ) → ℝ) (y z : ℝ) (hc : ContDiffAt ℝ 2 c ![y,z])
    (hroot : ∀ᶠ v in 𝓝 (![y,z] : Fin 2 → ℝ), originalNormalPhase F n ![c v,v 0,v 1]=0)
    (Y : (Fin 2 → ℝ) → ℝ)
    (hYv : Y ![fderiv ℝ c ![y,z] ![1,0],z]=y)
    (hY : ContinuousAt Y ![fderiv ℝ c ![y,z] ![1,0],z])
    (hright : ∀ᶠ q in 𝓝 (![fderiv ℝ c ![y,z] ![1,0],z] : Fin 2 → ℝ),
      fderiv ℝ c ![Y q,q 1] ![1,0]=q 0) :
    ∀ᶠ q in 𝓝 (![fderiv ℝ c ![y,z] ![1,0],z] : Fin 2 → ℝ),
      originalGaussParameterEquations F n (q,![c ![Y q,q 1],Y q])=0 := by
  let a : Fin 2 → ℝ := ![fderiv ℝ c ![y,z] ![1,0],z]
  have ht : Tendsto (fun q : Fin 2 → ℝ => (![Y q,q 1] : Fin 2 → ℝ)) (𝓝 a) (𝓝 ![y,z]) := by
    have hcont : ContinuousAt (fun q : Fin 2 → ℝ => (![Y q,q 1] : Fin 2 → ℝ)) a := by
      apply continuousAt_pi.mpr
      intro i
      fin_cases i
      · exact hY
      · exact (continuous_apply 1).continuousAt
    change Tendsto _ _ (𝓝 (![Y a,a 1] : Fin 2 → ℝ)) at hcont
    simpa only [a,hYv,Matrix.cons_val_one,Matrix.head_cons] using hcont
  have hnear := ht.eventually ((hc.eventually (by norm_num)).and (eventually_eventually_nhds.mpr hroot))
  filter_upwards [hnear,hright] with q hq hp
  rw [originalGaussParameterEquations_apply]
  have hzero := hq.2.self_of_nhds
  have hslope := originalNormal_graph_slope_equation (originalNormalPhase F n) c (Y q) (q 1)
    (originalNormalPhase_contDiff F n 2).contDiffAt hq.1 hq.2
  rw [hp] at hslope
  ext i
  fin_cases i
  · exact hzero
  · exact hslope

theorem originalGauss_selected_agrees_with_inverse {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (S : Set (Fin 2 → ℝ)) (b : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (c : (Fin 2 → ℝ) → ℝ) (y z : ℝ) (hc : ContDiffAt ℝ 2 c ![y,z])
    (hroot : ∀ᶠ v in 𝓝 (![y,z] : Fin 2 → ℝ), originalNormalPhase F n ![c v,v 0,v 1]=0)
    (ha : (![fderiv ℝ c ![y,z] ![1,0],z] : Fin 2 → ℝ)∈S)
    (hb : ContinuousWithinAt b S ![fderiv ℝ c ![y,z] ![1,0],z])
    (hbv : b ![fderiv ℝ c ![y,z] ![1,0],z]=![c ![y,z],y])
    (hbroot : ∀ q∈S, b q∈originalGaussRegularRootSet F n (q 0) (q 1))
    (Y : (Fin 2 → ℝ) → ℝ)
    (hYv : Y ![fderiv ℝ c ![y,z] ![1,0],z]=y)
    (hY : ContinuousAt Y ![fderiv ℝ c ![y,z] ![1,0],z])
    (hright : ∀ᶠ q in 𝓝 (![fderiv ℝ c ![y,z] ![1,0],z] : Fin 2 → ℝ),
      fderiv ℝ c ![Y q,q 1] ![1,0]=q 0) :
    b =ᶠ[𝓝[S] ![fderiv ℝ c ![y,z] ![1,0],z]]
      (fun q => (![c ![Y q,q 1],Y q] : Fin 2 → ℝ)) := by
  let a : Fin 2 → ℝ := ![fderiv ℝ c ![y,z] ![1,0],z]
  let B := fun q : Fin 2 → ℝ => (![c ![Y q,q 1],Y q] : Fin 2 → ℝ)
  obtain ⟨e,_,_,_,hu,hbe⟩ := originalGauss_selected_local_extension F n S b a ha hb hbroot
  have hBc : ContinuousAt B a := by
    have hv : (![Y a,a 1] : Fin 2 → ℝ)=![y,z] := by simp [a,hYv]
    have hQ : ContinuousAt (fun q : Fin 2 → ℝ => (![Y q,q 1] : Fin 2 → ℝ)) a := by
      apply continuousAt_pi.mpr
      intro i
      fin_cases i
      · exact hY
      · exact (continuous_apply 1).continuousAt
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · have hcc : ContinuousAt c ![Y a,a 1] := by rw [hv]; exact hc.continuousAt
      exact ContinuousAt.comp (f := fun q : Fin 2 → ℝ => (![Y q,q 1] : Fin 2 → ℝ)) (x := a) hcc hQ
    · exact hY
  have hBv : B a=b a := by
    rw [hbv]
    simp [B,a,hYv]
  have hz := originalGauss_inverse_lift_is_local_zero F n c y z hc hroot Y hYv hY hright
  have hBe : B =ᶠ[𝓝 a] e := by
    have ht : Tendsto (fun q => (q,B q)) (𝓝 a) (𝓝 (a,b a)) := by
      have h : Tendsto (fun q => (q,B q)) (𝓝 a) (𝓝 (a,B a)) := continuousAt_id.prodMk hBc
      rwa [hBv] at h
    filter_upwards [ht.eventually hu,hz] with q hq hqz
    exact hq hqz
  exact hbe.trans (hBe.filter_mono nhdsWithin_le_nhds).symm

theorem originalGaussCellSection_same_inverse {k n : ℕ}
    {C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k n)}
    (A : PlanarGraphRefinement C) (F : CoefficientSpace k) (i : Fin A.refined.count)
    (c : (Fin 2 → ℝ) → ℝ) (y z : ℝ) (hc : ContDiffAt ℝ 2 c ![y,z])
    (hroot : ∀ᶠ v in 𝓝 (![y,z] : Fin 2 → ℝ), originalNormalPhase F n ![c v,v 0,v 1]=0)
    (hr : fderiv ℝ (fun v => fderiv ℝ c v ![1,0]) ![y,z] ![1,0]≠0)
    (ha : (![fderiv ℝ c ![y,z] ![1,0],z] : Fin 2 → ℝ)∈projectionFiber (A.refined.domain i) F)
    (hbv : originalGaussCellSection A F i ![fderiv ℝ c ![y,z] ![1,0],z]=![c ![y,z],y]) :
    let Pfun := fun v => fderiv ℝ c v ![1,0]
    let r := fderiv ℝ Pfun ![y,z] ![1,0]
    let s := fderiv ℝ Pfun ![y,z] ![0,1]
    ∃ Y : (Fin 2 → ℝ) → ℝ,
      Y ![Pfun ![y,z],z]=y ∧ ContDiffAt ℝ 1 Y ![Pfun ![y,z],z] ∧
      (∀ᶠ q in 𝓝 ![Pfun ![y,z],z], Pfun ![Y q,q 1]=q 0) ∧
      (∀ᶠ v in 𝓝 (![y,z] : Fin 2 → ℝ), Y ![Pfun v,v 1]=v 0) ∧
      HasDerivAt (fun t => Y ![t,z]) r⁻¹ (Pfun ![y,z]) ∧
      HasDerivAt (fun t => Y ![Pfun ![y,z],t]) (-s/r) z ∧
      originalGaussCellSection A F i =ᶠ[𝓝[projectionFiber (A.refined.domain i) F] ![Pfun ![y,z],z]]
        (fun q => (![c ![Y q,q 1],Y q] : Fin 2 → ℝ)) := by
  obtain ⟨Y,hv,hY,hR,hL,hp,hz⟩ := originalGauss_local_C1_inverse_chart c ![y,z] hc hr
  exact ⟨Y,hv,hY,hR,hL,hp,hz,originalGauss_selected_agrees_with_inverse F n _ _ c y z hc hroot ha
    (A.fiber_section_continuousOn i F _ ha) hbv (originalGaussCellSection_mem_regular A F i)
    Y hv hY.continuousAt hR⟩

end PaperI
