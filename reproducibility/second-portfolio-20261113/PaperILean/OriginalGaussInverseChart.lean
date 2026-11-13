import PaperILean.OriginalGaussRootJacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! I1287-I1295. Construct the original LOCAL inverse of (c_y,z).
This is not the global finite, parameter-compatible Borel chart catalogue.
-/
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology

def originalGaussTriangularEquiv (r s : ℝ) (hr : r≠0) :
    (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) where
  toLinearEquiv :=
    { toFun := fun v => ![r*v 0+s*v 1,v 1]
      invFun := fun w => ![(w 0-s*w 1)/r,w 1]
      left_inv := by
        intro v
        funext i
        fin_cases i <;> simp [hr]
      right_inv := by
        intro w
        funext i
        fin_cases i
        · simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
          field_simp
        · rfl
      map_add' := by
        intro u v
        funext i
        fin_cases i <;> simp <;> ring
      map_smul' := by
        intro a v
        funext i
        fin_cases i <;> simp <;> ring }
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_const.mul (continuous_apply 0)).add (continuous_const.mul (continuous_apply 1))
    · exact continuous_apply 1
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun w : Fin 2 → ℝ => (w 0-s*w 1)/r)
      have h0 : Continuous (fun w : Fin 2 → ℝ => w 0) := continuous_apply 0
      have h1 : Continuous (fun w : Fin 2 → ℝ => w 1) := continuous_apply 1
      exact (h0.sub (continuous_const.mul h1)).div_const r
    · exact continuous_apply 1

def originalGaussSlopeCoordinates (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![fderiv ℝ c v ![1,0],v 1]

theorem originalGaussSlopeCoordinates_contDiffAt
    (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) (hc : ContDiffAt ℝ 2 c v) :
    ContDiffAt ℝ 1 (originalGaussSlopeCoordinates c) v := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact (hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  · change ContDiffAt ℝ 1 (fun x : Fin 2 → ℝ => x 1) v
    exact (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt

theorem originalGaussSlopeCoordinates_hasFDerivAt
    (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) (hc : ContDiffAt ℝ 2 c v)
    (hr : fderiv ℝ (fun x => fderiv ℝ c x ![1,0]) v ![1,0]≠0) :
    HasFDerivAt (originalGaussSlopeCoordinates c)
      (originalGaussTriangularEquiv
        (fderiv ℝ (fun x => fderiv ℝ c x ![1,0]) v ![1,0])
        (fderiv ℝ (fun x => fderiv ℝ c x ![1,0]) v ![0,1]) hr).toContinuousLinearMap v := by
  have hP : DifferentiableAt ℝ (fun x => fderiv ℝ c x ![1,0]) v :=
    ((hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert hP.hasFDerivAt using 1
    ext w
    simpa [originalGaussTriangularEquiv,mul_comm] using
      (originalGauss_linear_apply_two (fderiv ℝ (fun x => fderiv ℝ c x ![1,0]) v) w).symm
  · exact hasFDerivAt_apply 1 v

theorem originalGauss_local_inverse_chart
    (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) (hc : ContDiffAt ℝ 2 c v)
    (hr : fderiv ℝ (fun x => fderiv ℝ c x ![1,0]) v ![1,0]≠0) :
    let Pfun := fun x => fderiv ℝ c x ![1,0]
    let r := fderiv ℝ Pfun v ![1,0]
    let s := fderiv ℝ Pfun v ![0,1]
    ∃ Y : (Fin 2 → ℝ) → ℝ,
      Y ![Pfun v,v 1]=v 0 ∧ ContinuousAt Y ![Pfun v,v 1] ∧
      (∀ᶠ u in 𝓝 ![Pfun v,v 1], Pfun ![Y u,u 1]=u 0) ∧
      (∀ᶠ w in 𝓝 v, Y ![Pfun w,w 1]=w 0) ∧
      HasDerivAt (fun t => Y ![t,v 1]) r⁻¹ (Pfun v) ∧
      HasDerivAt (fun t => Y ![Pfun v,t]) (-s/r) (v 1) := by
  let Pfun := fun x => fderiv ℝ c x ![1,0]
  let r := fderiv ℝ Pfun v ![1,0]
  let s := fderiv ℝ Pfun v ![0,1]
  let e := originalGaussTriangularEquiv r s hr
  let Φ := originalGaussSlopeCoordinates c
  have hd := originalGaussSlopeCoordinates_hasFDerivAt c v hc hr
  have hs := (originalGaussSlopeCoordinates_contDiffAt c v hc).hasStrictFDerivAt' hd (by norm_num)
  let ψ := hs.localInverse Φ e v
  let Y := fun u => ψ u 0
  have hψ : HasFDerivAt ψ e.symm.toContinuousLinearMap (Φ v) := hs.to_localInverse.hasFDerivAt
  have hY := (hasFDerivAt_apply (𝕜 := ℝ) 0 (ψ (Φ v))).comp (Φ v) hψ
  have hvalue : Y ![Pfun v,v 1]=v 0 := congrFun hs.localInverse_apply_image 0
  have hright : ∀ᶠ u in 𝓝 ![Pfun v,v 1], Pfun ![Y u,u 1]=u 0 := by
    filter_upwards [hs.eventually_right_inverse] with u hu
    have hz : ψ u 1=u 1 := congrFun hu 1
    have hx : Pfun (ψ u)=u 0 := congrFun hu 0
    have heq : ψ u=![Y u,u 1] := by
      funext i
      fin_cases i
      · rfl
      · exact hz
    rwa [heq] at hx
  have hleft : ∀ᶠ w in 𝓝 v, Y ![Pfun w,w 1]=w 0 :=
    hs.eventually_left_inverse.mono (fun w hw => congrFun hw 0)
  refine ⟨Y,hvalue,hY.continuousAt,hright,hleft,?_,?_⟩
  · have hline : HasDerivAt (fun t : ℝ => (![t,v 1] : Fin 2 → ℝ)) ![1,0] (Pfun v) := by
      apply hasDerivAt_pi.mpr
      intro i
      fin_cases i
      · exact hasDerivAt_id _
      · exact hasDerivAt_const _ _
    have hp := hY.comp_hasDerivAt (Pfun v) hline
    change HasDerivAt (fun t => Y ![t,v 1]) ((1-s*0)/r) (Pfun v) at hp
    simpa only [mul_zero,sub_zero,one_div] using hp
  · have hline : HasDerivAt (fun t : ℝ => (![Pfun v,t] : Fin 2 → ℝ)) ![0,1] (v 1) := by
      apply hasDerivAt_pi.mpr
      intro i
      fin_cases i
      · exact hasDerivAt_const _ _
      · exact hasDerivAt_id _
    have hz := hY.comp_hasDerivAt (v 1) hline
    change HasDerivAt (fun t => Y ![Pfun v,t]) ((0-s*1)/r) (v 1) at hz
    simpa only [mul_one,zero_sub] using hz

end PaperI
