import PaperILean.OriginalGaussNormalFrame
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! I1280-I1284, with z fixed. Differentiate the actual local root graph
twice; the nonzero Jacobian is a conclusion, not a supplied jet identity.
The local C2 assumptions are sufficient regularity, not global extensions.
-/
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology

theorem originalGauss_linear_apply_two (l : (Fin 2 → ℝ) →L[ℝ] ℝ) (v : Fin 2 → ℝ) :
    l v=v 0*l ![1,0]+v 1*l ![0,1] := by
  have hv : v=v 0 • (![1,0] : Fin 2 → ℝ)+v 1 • ![0,1] := by
    funext i
    fin_cases i <;> simp
  rw [hv,map_add,map_smul,map_smul]
  simp

def originalGaussRootEquations (G : (Fin 2 → ℝ) → ℝ) (p : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![G x,fderiv ℝ G x ![p,1]]

def originalGaussRootJacobian (G : (Fin 2 → ℝ) → ℝ) (p : ℝ) (x : Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![fderiv ℝ G x ![1,0],fderiv ℝ G x ![0,1];
    fderiv ℝ (fun u => fderiv ℝ G u ![p,1]) x ![1,0],
    fderiv ℝ (fun u => fderiv ℝ G u ![p,1]) x ![0,1]]

theorem originalGauss_graph_hasDerivAt (c : ℝ → ℝ) (y : ℝ)
    (hc : DifferentiableAt ℝ c y) :
    HasDerivAt (fun t => (![c t,t] : Fin 2 → ℝ)) ![deriv c y,1] y := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hc.hasDerivAt
  · exact hasDerivAt_id y

theorem originalGauss_root_tangent_zero
    (G : (Fin 2 → ℝ) → ℝ) (c : ℝ → ℝ) (y : ℝ)
    (hG : DifferentiableAt ℝ G ![c y,y]) (hc : DifferentiableAt ℝ c y)
    (hroot : (fun t => G ![c t,t]) =ᶠ[𝓝 y] (fun _ => 0)) :
    fderiv ℝ G ![c y,y] ![deriv c y,1]=0 := by
  exact (hG.hasFDerivAt.comp_hasDerivAt y (originalGauss_graph_hasDerivAt c y hc)).unique
    ((hasDerivAt_const y (0:ℝ)).congr_of_eventuallyEq hroot)

theorem originalGauss_root_equations_zero
    (G : (Fin 2 → ℝ) → ℝ) (c : ℝ → ℝ) (y : ℝ)
    (hG : DifferentiableAt ℝ G ![c y,y]) (hc : DifferentiableAt ℝ c y)
    (hroot : (fun t => G ![c t,t]) =ᶠ[𝓝 y] (fun _ => 0)) :
    originalGaussRootEquations G (deriv c y) ![c y,y]=0 := by
  have h0 : G ![c y,y]=0 := hroot.self_of_nhds
  have h1 := originalGauss_root_tangent_zero G c y hG hc hroot
  funext i
  fin_cases i <;> simp [originalGaussRootEquations,h0,h1]

theorem originalGauss_root_second_identity
    (G : (Fin 2 → ℝ) → ℝ) (c : ℝ → ℝ) (y : ℝ)
    (hG : ContDiffAt ℝ 2 G ![c y,y]) (hc : ContDiffAt ℝ 2 c y)
    (hroot : (fun t => G ![c t,t]) =ᶠ[𝓝 y] (fun _ => 0)) :
    fderiv ℝ (fun u => fderiv ℝ G u ![deriv c y,1]) ![c y,y] ![deriv c y,1]
      +deriv (deriv c) y*fderiv ℝ G ![c y,y] ![1,0]=0 := by
  let p := deriv c y
  let H := fun u : Fin 2 → ℝ => fderiv ℝ G u ![p,1]
  let X := fun u : Fin 2 → ℝ => fderiv ℝ G u ![1,0]
  have hgraph := originalGauss_graph_hasDerivAt c y (hc.differentiableAt (by norm_num))
  have hH : DifferentiableAt ℝ H ![c y,y] :=
    ((hG.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hX : DifferentiableAt ℝ X ![c y,y] :=
    ((hG.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hcp : DifferentiableAt ℝ (deriv c) y :=
    ((hc.fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiffAt_const (c := (1:ℝ)))).differentiableAt (by norm_num)
  have hnearG := hgraph.continuousAt.eventually (hG.eventually (by norm_num))
  have hnearc := hc.eventually (by norm_num)
  have hzero : (fun t => H ![c t,t]+(deriv c t-p)*X ![c t,t]) =ᶠ[𝓝 y] (fun _ => 0) := by
    filter_upwards [hnearG,hnearc,hroot.eventuallyEq_nhds] with t htG htc htroot
    have ht := originalGauss_root_tangent_zero G c t (htG.differentiableAt (by norm_num))
      (htc.differentiableAt (by norm_num)) htroot
    have hv : (![deriv c t,1] : Fin 2 → ℝ)=![p,1]+(deriv c t-p) • ![1,0] := by
      funext i
      fin_cases i <;> simp <;> ring
    rw [hv,map_add,map_smul] at ht
    exact ht
  have hder := (hH.hasFDerivAt.comp_hasDerivAt y hgraph).add
    ((hcp.hasDerivAt.sub_const p).mul (hX.hasFDerivAt.comp_hasDerivAt y hgraph))
  have heq := hder.unique ((hasDerivAt_const y (0:ℝ)).congr_of_eventuallyEq hzero)
  simpa [p,H,X] using heq

theorem originalGauss_root_jacobian_det
    (G : (Fin 2 → ℝ) → ℝ) (c : ℝ → ℝ) (y : ℝ)
    (hG : ContDiffAt ℝ 2 G ![c y,y]) (hc : ContDiffAt ℝ 2 c y)
    (hroot : (fun t => G ![c t,t]) =ᶠ[𝓝 y] (fun _ => 0)) :
    (originalGaussRootJacobian G (deriv c y) ![c y,y]).det=
      -(fderiv ℝ G ![c y,y] ![1,0])^2*deriv (deriv c) y := by
  have hfirst := originalGauss_root_tangent_zero G c y
    (hG.differentiableAt (by norm_num)) (hc.differentiableAt (by norm_num)) hroot
  have hsecond := originalGauss_root_second_identity G c y hG hc hroot
  rw [originalGauss_linear_apply_two _ ![deriv c y,1]] at hfirst hsecond
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,one_mul] at hfirst hsecond
  have hy : fderiv ℝ G ![c y,y] ![0,1]=
      -(deriv c y*fderiv ℝ G ![c y,y] ![1,0]) := by linarith
  have hh : deriv c y*fderiv ℝ (fun u => fderiv ℝ G u ![deriv c y,1]) ![c y,y] ![1,0]
      +fderiv ℝ (fun u => fderiv ℝ G u ![deriv c y,1]) ![c y,y] ![0,1]=
      -(deriv (deriv c) y*fderiv ℝ G ![c y,y] ![1,0]) := by linarith
  simp only [originalGaussRootJacobian,Matrix.det_fin_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
  rw [hy]
  calc
    _ = fderiv ℝ G ![c y,y] ![1,0]*
      (deriv c y*fderiv ℝ (fun u => fderiv ℝ G u ![deriv c y,1]) ![c y,y] ![1,0]+
        fderiv ℝ (fun u => fderiv ℝ G u ![deriv c y,1]) ![c y,y] ![0,1]) := by ring
    _ = _ := by rw [hh]; ring

theorem originalGauss_regular_root_jacobian_ne_zero
    (G : (Fin 2 → ℝ) → ℝ) (c : ℝ → ℝ) (y : ℝ)
    (hG : ContDiffAt ℝ 2 G ![c y,y]) (hc : ContDiffAt ℝ 2 c y)
    (hroot : (fun t => G ![c t,t]) =ᶠ[𝓝 y] (fun _ => 0))
    (hk : fderiv ℝ G ![c y,y] ![1,0]≠0) (hr : deriv (deriv c) y≠0) :
    (originalGaussRootJacobian G (deriv c y) ![c y,y]).det≠0 := by
  rw [originalGauss_root_jacobian_det G c y hG hc hroot]
  exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hk)) hr

end PaperI
