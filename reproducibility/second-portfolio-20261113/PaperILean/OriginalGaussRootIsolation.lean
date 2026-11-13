import PaperILean.OriginalGaussRootSlice
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! I1284: the computed nonzero Jacobian makes the original two-equation
root locally isolated. The separate polynomial-degree/Bezout count is not
asserted here. No global component or branch selection is made.
-/
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology

def originalGaussMatrixEquiv (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det≠0) :
    (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  (LinearEquiv.ofBijective M.mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr (M.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hM)),
     Matrix.mulVec_surjective_iff_isUnit.mpr (M.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hM))⟩).toContinuousLinearEquiv

theorem originalGaussRootJacobian_mulVec
    (G : (Fin 2 → ℝ) → ℝ) (p : ℝ) (x v : Fin 2 → ℝ) :
    (originalGaussRootJacobian G p x).mulVec v=
      ![fderiv ℝ G x v,fderiv ℝ (fun u => fderiv ℝ G u ![p,1]) x v] := by
  funext i
  fin_cases i
  · change _=fderiv ℝ G x v
    rw [originalGauss_linear_apply_two _ v]
    simp [originalGaussRootJacobian,Matrix.mulVec,dotProduct,Fin.sum_univ_two,mul_comm]
  · change _=fderiv ℝ (fun u => fderiv ℝ G u ![p,1]) x v
    rw [originalGauss_linear_apply_two _ v]
    simp [originalGaussRootJacobian,Matrix.mulVec,dotProduct,Fin.sum_univ_two,mul_comm]

theorem originalGaussRootEquations_contDiffAt
    (G : (Fin 2 → ℝ) → ℝ) (p : ℝ) (x : Fin 2 → ℝ) (hG : ContDiffAt ℝ 2 G x) :
    ContDiffAt ℝ 1 (originalGaussRootEquations G p) x := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hG.of_le (by norm_num)
  · exact (hG.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

theorem originalGaussRootEquations_hasStrictFDerivAt
    (G : (Fin 2 → ℝ) → ℝ) (p : ℝ) (x : Fin 2 → ℝ) (hG : ContDiffAt ℝ 2 G x)
    (hdet : (originalGaussRootJacobian G p x).det≠0) :
    HasStrictFDerivAt (originalGaussRootEquations G p)
      (originalGaussMatrixEquiv (originalGaussRootJacobian G p x) hdet).toContinuousLinearMap x := by
  have he : (originalGaussMatrixEquiv (originalGaussRootJacobian G p x) hdet).toContinuousLinearMap=
      ContinuousLinearMap.pi ![fderiv ℝ G x,fderiv ℝ (fun u => fderiv ℝ G u ![p,1]) x] := by
    ext v i
    fin_cases i
    · simpa [originalGaussMatrixEquiv] using congrFun (originalGaussRootJacobian_mulVec G p x v) 0
    · simpa [originalGaussMatrixEquiv] using congrFun (originalGaussRootJacobian_mulVec G p x v) 1
  have hd : HasFDerivAt (originalGaussRootEquations G p)
      (originalGaussMatrixEquiv (originalGaussRootJacobian G p x) hdet).toContinuousLinearMap x := by
    rw [he]
    exact originalGaussRootEquations_hasFDerivAt G p x hG
  exact (originalGaussRootEquations_contDiffAt G p x hG).hasStrictFDerivAt' hd (by norm_num)

theorem originalGauss_regular_root_isolated
    (G : (Fin 2 → ℝ) → ℝ) (c : ℝ → ℝ) (y : ℝ)
    (hG : ContDiffAt ℝ 2 G ![c y,y]) (hc : ContDiffAt ℝ 2 c y)
    (hroot : (fun t => G ![c t,t]) =ᶠ[𝓝 y] (fun _ => 0))
    (hk : fderiv ℝ G ![c y,y] ![1,0]≠0) (hr : deriv (deriv c) y≠0) :
    ∀ᶠ w in 𝓝 (![c y,y] : Fin 2 → ℝ),
      originalGaussRootEquations G (deriv c y) w=0 → w=![c y,y] := by
  have hdet := originalGauss_regular_root_jacobian_ne_zero G c y hG hc hroot hk hr
  have hs := originalGaussRootEquations_hasStrictFDerivAt G (deriv c y) ![c y,y] hG hdet
  have hzero := originalGauss_root_equations_zero G c y
    (hG.differentiableAt (by norm_num)) (hc.differentiableAt (by norm_num)) hroot
  filter_upwards [hs.eventually_left_inverse] with w hw
  intro hweq
  rw [hweq,← hzero,hs.localInverse_apply_image] at hw
  exact hw.symm

theorem originalGauss_regular_phase_root_isolated
    (G : (Fin 3 → ℝ) → ℝ) (c : ℝ → ℝ) (y z : ℝ)
    (hG : ContDiffAt ℝ 2 G ![c y,y,z]) (hc : ContDiffAt ℝ 2 c y)
    (hroot : (fun t => G ![c t,t,z]) =ᶠ[𝓝 y] (fun _ => 0))
    (hk : fderiv ℝ G ![c y,y,z] ![1,0,0]≠0) (hr : deriv (deriv c) y≠0) :
    ∀ᶠ w in 𝓝 (![c y,y] : Fin 2 → ℝ),
      originalGaussRootEquations (originalGaussPhaseSlice G z) (deriv c y) w=0 → w=![c y,y] := by
  apply originalGauss_regular_root_isolated (originalGaussPhaseSlice G z) c y
    (originalGaussPhaseSlice_contDiffAt G z ![c y,y] hG) hc hroot _ hr
  simpa only [originalGaussPhaseSlice_dx G z ![c y,y] (hG.differentiableAt (by norm_num))] using hk

theorem originalGauss_original_phase_pair_isolated
    (G : (Fin 3 → ℝ) → ℝ) (c : ℝ → ℝ) (y z : ℝ)
    (hG : ContDiffAt ℝ 2 G ![c y,y,z]) (hc : ContDiffAt ℝ 2 c y)
    (hroot : (fun t => G ![c t,t,z]) =ᶠ[𝓝 y] (fun _ => 0))
    (hk : fderiv ℝ G ![c y,y,z] ![1,0,0]≠0) (hr : deriv (deriv c) y≠0) :
    ∀ᶠ w in 𝓝 (![c y,y] : Fin 2 → ℝ),
      G ![w 0,w 1,z]=0 →
      fderiv ℝ G ![w 0,w 1,z] ![0,1,0]+deriv c y*fderiv ℝ G ![w 0,w 1,z] ![1,0,0]=0 →
      w=![c y,y] := by
  have hiso := originalGauss_regular_phase_root_isolated G c y z hG hc hroot hk hr
  have hnear := (originalGaussXYEmbedding_hasFDerivAt z ![c y,y]).continuousAt.eventually
    (hG.eventually (by norm_num))
  filter_upwards [hiso,hnear] with w hw hwG
  intro h0 h1
  apply hw
  rw [originalGauss_phase_root_equations G z (deriv c y) w (hwG.differentiableAt (by norm_num))]
  funext i
  fin_cases i <;> simp [h0,h1]

end PaperI
