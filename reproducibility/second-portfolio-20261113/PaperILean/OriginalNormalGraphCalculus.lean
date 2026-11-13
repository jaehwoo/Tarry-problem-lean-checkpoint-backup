import PaperILean.OriginalNormalGraph

/-! Identify the fixed-z derivatives used in the original Gauss determinant
and isolation argument with the actual two-variable normal graph derivatives.
The curvature and normal derivative remain explicit nonzero hypotheses.
-/
noncomputable section
namespace PaperI
open Filter
open scoped Topology

theorem originalNormal_yline_hasDerivAt (y z : ℝ) :
    HasDerivAt (fun t : ℝ => (![t,z] : Fin 2 → ℝ)) ![1,0] y := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_id y
  · exact hasDerivAt_const y z

theorem originalNormal_slice_deriv
    (c : (Fin 2 → ℝ) → ℝ) (y z : ℝ) (hc : DifferentiableAt ℝ c ![y,z]) :
    deriv (fun t => c ![t,z]) y=fderiv ℝ c ![y,z] ![1,0] :=
  (hc.hasFDerivAt.comp_hasDerivAt y (originalNormal_yline_hasDerivAt y z)).deriv

theorem originalNormal_slice_second_deriv
    (c : (Fin 2 → ℝ) → ℝ) (y z : ℝ) (hc : ContDiffAt ℝ 2 c ![y,z]) :
    deriv (deriv (fun t => c ![t,z])) y=
      fderiv ℝ (fun w => fderiv ℝ c w ![1,0]) ![y,z] ![1,0] := by
  have hP : DifferentiableAt ℝ (fun w => fderiv ℝ c w ![1,0]) ![y,z] :=
    ((hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hnear := (originalNormal_yline_hasDerivAt y z).continuousAt.eventually
    (hc.eventually (by norm_num))
  have he : deriv (fun t => c ![t,z]) =ᶠ[𝓝 y] (fun t => fderiv ℝ c ![t,z] ![1,0]) := by
    filter_upwards [hnear] with t ht
    exact originalNormal_slice_deriv c t z (ht.differentiableAt (by norm_num))
  exact ((hP.hasFDerivAt.comp_hasDerivAt y (originalNormal_yline_hasDerivAt y z)).congr_of_eventuallyEq he).deriv

theorem originalNormal_graph_slope_equation
    (G : (Fin 3 → ℝ) → ℝ) (c : (Fin 2 → ℝ) → ℝ) (y z : ℝ)
    (hG : ContDiffAt ℝ 2 G ![c ![y,z],y,z]) (hc : ContDiffAt ℝ 2 c ![y,z])
    (hroot : ∀ᶠ w in 𝓝 (![y,z] : Fin 2 → ℝ), G ![c w,w 0,w 1]=0) :
    fderiv ℝ G ![c ![y,z],y,z] ![0,1,0]+
      fderiv ℝ c ![y,z] ![1,0]*fderiv ℝ G ![c ![y,z],y,z] ![1,0,0]=0 := by
  obtain ⟨hcs,hcz⟩ := originalNormal_graph_slice G c y z hc hroot
  have hs := originalGaussPhaseSlice_contDiffAt G z ![c ![y,z],y] hG
  have hz := originalGauss_root_equations_zero (originalGaussPhaseSlice G z)
    (fun t => c ![t,z]) y (hs.differentiableAt (by norm_num))
    (hcs.differentiableAt (by norm_num)) hcz
  rw [originalGauss_phase_root_equations G z _ _ (hG.differentiableAt (by norm_num))] at hz
  have h1 := congrFun hz 1
  change fderiv ℝ G ![c ![y,z],y,z] ![0,1,0]+
    deriv (fun t => c ![t,z]) y*fderiv ℝ G ![c ![y,z],y,z] ![1,0,0]=0 at h1
  rwa [originalNormal_slice_deriv c y z (hc.differentiableAt (by norm_num))] at h1

theorem originalNormal_graph_slope_quotient
    (G : (Fin 3 → ℝ) → ℝ) (c : (Fin 2 → ℝ) → ℝ) (y z : ℝ)
    (hG : ContDiffAt ℝ 2 G ![c ![y,z],y,z]) (hc : ContDiffAt ℝ 2 c ![y,z])
    (hroot : ∀ᶠ w in 𝓝 (![y,z] : Fin 2 → ℝ), G ![c w,w 0,w 1]=0)
    (hk : fderiv ℝ G ![c ![y,z],y,z] ![1,0,0]≠0) :
    fderiv ℝ c ![y,z] ![1,0]=
      -fderiv ℝ G ![c ![y,z],y,z] ![0,1,0]/fderiv ℝ G ![c ![y,z],y,z] ![1,0,0] := by
  apply (eq_div_iff hk).mpr
  have h := originalNormal_graph_slope_equation G c y z hG hc hroot
  linarith

theorem originalNormal_graph_gauss_jacobian_det
    (G : (Fin 3 → ℝ) → ℝ) (c : (Fin 2 → ℝ) → ℝ) (y z : ℝ)
    (hG : ContDiffAt ℝ 2 G ![c ![y,z],y,z]) (hc : ContDiffAt ℝ 2 c ![y,z])
    (hroot : ∀ᶠ w in 𝓝 (![y,z] : Fin 2 → ℝ), G ![c w,w 0,w 1]=0) :
    (originalGaussRootJacobian (originalGaussPhaseSlice G z)
      (fderiv ℝ c ![y,z] ![1,0]) ![c ![y,z],y]).det=
      -(fderiv ℝ G ![c ![y,z],y,z] ![1,0,0])^2*
        fderiv ℝ (fun w => fderiv ℝ c w ![1,0]) ![y,z] ![1,0] := by
  obtain ⟨hcs,hcz⟩ := originalNormal_graph_slice G c y z hc hroot
  have h := originalGauss_phase_root_jacobian_det G (fun t => c ![t,z]) y z hG hcs hcz
  simpa only [originalNormal_slice_deriv c y z (hc.differentiableAt (by norm_num)),
    originalNormal_slice_second_deriv c y z hc] using h

theorem originalNormal_graph_gauss_isolated
    (G : (Fin 3 → ℝ) → ℝ) (c : (Fin 2 → ℝ) → ℝ) (y z : ℝ)
    (hG : ContDiffAt ℝ 2 G ![c ![y,z],y,z]) (hc : ContDiffAt ℝ 2 c ![y,z])
    (hroot : ∀ᶠ w in 𝓝 (![y,z] : Fin 2 → ℝ), G ![c w,w 0,w 1]=0)
    (hk : fderiv ℝ G ![c ![y,z],y,z] ![1,0,0]≠0)
    (hr : fderiv ℝ (fun w => fderiv ℝ c w ![1,0]) ![y,z] ![1,0]≠0) :
    ∀ᶠ w in 𝓝 (![c ![y,z],y] : Fin 2 → ℝ),
      G ![w 0,w 1,z]=0 →
      fderiv ℝ G ![w 0,w 1,z] ![0,1,0]+
        fderiv ℝ c ![y,z] ![1,0]*fderiv ℝ G ![w 0,w 1,z] ![1,0,0]=0 →
      w=![c ![y,z],y] := by
  obtain ⟨hcs,hcz⟩ := originalNormal_graph_slice G c y z hc hroot
  have hrs : deriv (deriv (fun t => c ![t,z])) y≠0 := by
    rwa [originalNormal_slice_second_deriv c y z hc]
  have h := originalGauss_original_phase_pair_isolated G (fun t => c ![t,z]) y z hG hcs hcz hk hrs
  simpa only [originalNormal_slice_deriv c y z (hc.differentiableAt (by norm_num))] using h

end PaperI
