import PaperILean.OriginalGaussSameInverse
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! I1289-I1299: actual graph derivatives and implicit differentiation of the
same ambient inverse. No sign assumption on the Hessian determinant. -/
noncomputable section
namespace PaperI
open Filter
open scoped Topology

def originalGaussCy (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) : ℝ :=
  fderiv ℝ c v ![1,0]
def originalGaussCz (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) : ℝ :=
  fderiv ℝ c v ![0,1]
def originalGaussR (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) : ℝ :=
  fderiv ℝ (originalGaussCy c) v ![1,0]
def originalGaussS (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) : ℝ :=
  fderiv ℝ (originalGaussCy c) v ![0,1]
def originalGaussT (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) : ℝ :=
  fderiv ℝ (originalGaussCz c) v ![0,1]
def originalGaussShear (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) : ℝ :=
  -originalGaussS c v / originalGaussR c v

theorem originalGauss_partial_fderiv (c : (Fin 2 → ℝ) → ℝ)
    (v e u : Fin 2 → ℝ) (hc : ContDiffAt ℝ 2 c v) :
    fderiv ℝ (fun w => fderiv ℝ c w e) v u = fderiv ℝ (fderiv ℝ c) v u e := by
  have hd := (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const e v)).fderiv
  simpa using congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L u) h

theorem originalGauss_mixed_partials (c : (Fin 2 → ℝ) → ℝ)
    (v : Fin 2 → ℝ) (hc : ContDiffAt ℝ 2 c v) :
    fderiv ℝ (originalGaussCz c) v ![1,0] = originalGaussS c v := by
  unfold originalGaussCz originalGaussS originalGaussCy
  rw [originalGauss_partial_fderiv c v ![0,1] ![1,0] hc,
    originalGauss_partial_fderiv c v ![1,0] ![0,1] hc]
  exact hc.isSymmSndFDerivAt (by norm_num) _ _

theorem originalGauss_inverse_base_hasFDerivAt
    (Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ) (hY : DifferentiableAt ℝ Y a) :
    HasFDerivAt (fun q : Fin 2 → ℝ => (![Y q,q 1] : Fin 2 → ℝ))
      (ContinuousLinearMap.pi ![fderiv ℝ Y a,ContinuousLinearMap.proj 1]) a := by
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · exact hY.hasFDerivAt
  · exact hasFDerivAt_apply 1 a

theorem originalGauss_inverse_base_derivative_apply
    (Y : (Fin 2 → ℝ) → ℝ) (a u : Fin 2 → ℝ) :
    (ContinuousLinearMap.pi ![fderiv ℝ Y a,ContinuousLinearMap.proj 1]) u =
      (![fderiv ℝ Y a u,u 1] : Fin 2 → ℝ) := by
  ext i
  fin_cases i <;> rfl

theorem originalGauss_same_inverse_fderiv
    (c Y : (Fin 2 → ℝ) → ℝ) (a u : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 2 c ![Y a,a 1]) (hY : DifferentiableAt ℝ Y a)
    (hr : originalGaussR c ![Y a,a 1] ≠ 0)
    (hright : ∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0) :
    fderiv ℝ Y a u = u 0 / originalGaussR c ![Y a,a 1] +
      originalGaussShear c ![Y a,a 1] * u 1 := by
  have hP : DifferentiableAt ℝ (originalGaussCy c) ![Y a,a 1] :=
    ((hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hcomp := hP.hasFDerivAt.comp a (originalGauss_inverse_base_hasFDerivAt Y a hY)
  have he := hcomp.unique ((hasFDerivAt_apply 0 a).congr_of_eventuallyEq hright)
  have hu := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L u) he
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    originalGauss_inverse_base_derivative_apply] at hu
  rw [originalGauss_linear_apply_two] at hu
  change fderiv ℝ Y a u * originalGaussR c ![Y a,a 1] +
    u 1 * originalGaussS c ![Y a,a 1] = u 0 at hu
  unfold originalGaussShear
  field_simp [hr]
  nlinarith [hu]

theorem originalGauss_same_graph_fderiv
    (c Y : (Fin 2 → ℝ) → ℝ) (a u : Fin 2 → ℝ)
    (hc : DifferentiableAt ℝ c ![Y a,a 1]) (hY : DifferentiableAt ℝ Y a)
    (hp : originalGaussCy c ![Y a,a 1]=a 0) :
    fderiv ℝ (fun q => c ![Y q,q 1]) a u =
      a 0 * fderiv ℝ Y a u + originalGaussCz c ![Y a,a 1] * u 1 := by
  have hf : fderiv ℝ (fun q => c ![Y q,q 1]) a = _ :=
    (hc.hasFDerivAt.comp a (originalGauss_inverse_base_hasFDerivAt Y a hY)).fderiv
  rw [hf, ContinuousLinearMap.comp_apply, originalGauss_inverse_base_derivative_apply]
  rw [originalGauss_linear_apply_two]
  change fderiv ℝ Y a u * originalGaussCy c ![Y a,a 1] +
    u 1 * originalGaussCz c ![Y a,a 1] = _
  rw [hp]
  ring

theorem originalGauss_same_q0_fderiv
    (c Y : (Fin 2 → ℝ) → ℝ) (a u : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 2 c ![Y a,a 1]) (hY : DifferentiableAt ℝ Y a)
    (hr : originalGaussR c ![Y a,a 1] ≠ 0)
    (hright : ∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0) :
    fderiv ℝ (fun q => originalGaussCz c ![Y q,q 1]) a u =
      -originalGaussShear c ![Y a,a 1] * u 0 +
      ((originalGaussR c ![Y a,a 1] * originalGaussT c ![Y a,a 1] -
        originalGaussS c ![Y a,a 1]^2) / originalGaussR c ![Y a,a 1]) * u 1 := by
  have hQ : DifferentiableAt ℝ (originalGaussCz c) ![Y a,a 1] :=
    ((hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hf : fderiv ℝ (fun q => originalGaussCz c ![Y q,q 1]) a = _ :=
    (HasFDerivAt.comp (g := originalGaussCz c)
      (f := fun q : Fin 2 → ℝ => (![Y q,q 1] : Fin 2 → ℝ))
      a hQ.hasFDerivAt (originalGauss_inverse_base_hasFDerivAt Y a hY)).fderiv
  rw [hf, ContinuousLinearMap.comp_apply, originalGauss_inverse_base_derivative_apply]
  rw [originalGauss_linear_apply_two,originalGauss_mixed_partials c _ hc]
  change fderiv ℝ Y a u * originalGaussS c ![Y a,a 1] + u 1 * originalGaussT c ![Y a,a 1] = _
  rw [originalGauss_same_inverse_fderiv c Y a u hc hY hr hright]
  unfold originalGaussShear
  field_simp [hr]
  ring

theorem originalGauss_shear_differentiableAt
    (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c v) (hr : originalGaussR c v ≠ 0) :
    DifferentiableAt ℝ (originalGaussShear c) v := by
  have hP : ContDiffAt ℝ 2 (originalGaussCy c) v :=
    (hc.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  have hd := hP.fderiv_right (m := 1) (by norm_num)
  have hS : DifferentiableAt ℝ (originalGaussS c) v :=
    (hd.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hR : DifferentiableAt ℝ (originalGaussR c) v :=
    (hd.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  change DifferentiableAt ℝ (fun w => -originalGaussS c w / originalGaussR c w) v
  simpa only [div_eq_mul_inv] using hS.neg.mul (hR.inv hr)

end PaperI
