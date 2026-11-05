import PaperILean.OriginalNormalJetCalculus

/-! I1305: the third implicit derivative, obtained by differentiating the
proved second identity. All three mixed second-derivative terms are retained. -/
noncomputable section
namespace PaperI
open Filter
open scoped Topology

def originalNormalLiftSecond (c : (Fin 2 → ℝ) → ℝ) (v u w : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![fderiv ℝ (fderiv ℝ c) v w u,0,0]

theorem originalNormal_second_apply_fderiv
    (c : (Fin 2 → ℝ) → ℝ) (v u w z : Fin 2 → ℝ) (hc : ContDiffAt ℝ 3 c v) :
    fderiv ℝ (fun t => fderiv ℝ (fderiv ℝ c) t w u) v z =
      fderiv ℝ (fderiv ℝ (fderiv ℝ c)) v z w u := by
  have hDD := ((hc.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd := (hDD.hasFDerivAt.clm_apply (hasFDerivAt_const w v)).clm_apply (hasFDerivAt_const u v)
  simpa using congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L z) hd.fderiv

theorem originalNormalLiftSecond_differentiableAt
    (c : (Fin 2 → ℝ) → ℝ) (v u w : Fin 2 → ℝ) (hc : ContDiffAt ℝ 3 c v) :
    DifferentiableAt ℝ (fun t => originalNormalLiftSecond c t u w) v := by
  have hDD := ((hc.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  apply differentiableAt_pi.mpr
  intro i; fin_cases i
  · exact (hDD.clm_apply (differentiableAt_const w)).clm_apply (differentiableAt_const u)
  · exact differentiableAt_const 0
  · exact differentiableAt_const 0

theorem originalNormalLiftSecond_fderiv
    (c : (Fin 2 → ℝ) → ℝ) (v u w z : Fin 2 → ℝ) (hc : ContDiffAt ℝ 3 c v) :
    fderiv ℝ (fun t => originalNormalLiftSecond c t u w) v z =
      ![fderiv ℝ (fderiv ℝ (fderiv ℝ c)) v z w u,0,0] := by
  have hDD := ((hc.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hp := (hDD.clm_apply (differentiableAt_const w)).clm_apply (differentiableAt_const u)
  have hd : HasFDerivAt (fun t => originalNormalLiftSecond c t u w)
      (ContinuousLinearMap.pi ![fderiv ℝ (fun t => fderiv ℝ (fderiv ℝ c) t w u) v,0,0]) v := by
    apply hasFDerivAt_pi'.mpr
    intro i; fin_cases i
    · exact hp.hasFDerivAt
    · exact hasFDerivAt_const 0 v
    · exact hasFDerivAt_const 0 v
  rw [hd.fderiv]
  ext i; fin_cases i
  · exact originalNormal_second_apply_fderiv c v u w z hc
  · rfl
  · rfl

theorem originalNormal_root_third_identity
    (G : (Fin 3 → ℝ) → ℝ) (c : (Fin 2 → ℝ) → ℝ) (v u w z : Fin 2 → ℝ)
    (hG : ContDiffAt ℝ 3 G (originalNormalLift c v)) (hc : ContDiffAt ℝ 3 c v)
    (hroot : ∀ᶠ t in 𝓝 v, G (originalNormalLift c t)=0) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ G)) (originalNormalLift c v)
        (originalNormalLiftLinear c v z) (originalNormalLiftLinear c v w) (originalNormalLiftLinear c v u) +
      fderiv ℝ (fderiv ℝ G) (originalNormalLift c v)
        (originalNormalLiftSecond c v w z) (originalNormalLiftLinear c v u) +
      fderiv ℝ (fderiv ℝ G) (originalNormalLift c v)
        (originalNormalLiftLinear c v w) (originalNormalLiftSecond c v u z) +
      fderiv ℝ (fderiv ℝ G) (originalNormalLift c v)
        (originalNormalLiftLinear c v z) (originalNormalLiftSecond c v u w) +
      fderiv ℝ (fderiv ℝ (fderiv ℝ c)) v z w u *
        fderiv ℝ G (originalNormalLift c v) ![1,0,0] = 0 := by
  have hc2 : ContDiffAt ℝ 2 c v := hc.of_le (by decide)
  have hX := originalNormalLift_hasFDerivAt c v (hc.differentiableAt (by norm_num))
  have hDG := (hG.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hDDG := ((hG.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let A := fun t => fderiv ℝ (fderiv ℝ G) (originalNormalLift c t)
  let B := fun t => fderiv ℝ G (originalNormalLift c t)
  have hA : DifferentiableAt ℝ A v := hDDG.comp v hX.differentiableAt
  have hB : DifferentiableAt ℝ B v := hDG.comp v hX.differentiableAt
  have hu := originalNormalLiftLinear_differentiableAt c v u hc2
  have hw := originalNormalLiftLinear_differentiableAt c v w hc2
  have huw := originalNormalLiftSecond_differentiableAt c v u w hc
  have hT := (hA.clm_apply hw).clm_apply hu
  have hS := hB.clm_apply huw
  have hroots : (fun t => G (originalNormalLift c t)) =ᶠ[𝓝 v] (fun _ => 0) := hroot
  have he : (fun t => A t (originalNormalLiftLinear c t w) (originalNormalLiftLinear c t u) +
      B t (originalNormalLiftSecond c t u w)) =ᶠ[𝓝 v] (fun _ => 0) := by
    filter_upwards [hX.continuousAt.eventually (hG.eventually (by norm_num)),hc.eventually (by norm_num),hroots.eventuallyEq_nhds] with t htG htc htr
    change fderiv ℝ (fderiv ℝ G) (originalNormalLift c t) (originalNormalLiftLinear c t w) (originalNormalLiftLinear c t u) + fderiv ℝ G (originalNormalLift c t) ![fderiv ℝ (fderiv ℝ c) t w u,0,0] = 0
    rw [originalNormal_linear_normal]
    exact originalNormal_root_second_identity G c t u w (htG.of_le (by decide)) (htc.of_le (by decide)) htr
  have hz : fderiv ℝ (fun t => A t (originalNormalLiftLinear c t w) (originalNormalLiftLinear c t u) +
      B t (originalNormalLiftSecond c t u w)) v z = 0 := by
    rw [he.fderiv_eq]; simp
  rw [fderiv_add hT hS,ContinuousLinearMap.add_apply] at hz
  rw [originalNormal_clm_apply_fderiv _ _ v z (hA.clm_apply hw) hu,
      originalNormal_clm_apply_fderiv A _ v z hA hw,
      originalNormal_clm_apply_fderiv B _ v z hB huw] at hz
  have ha := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ((Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] ℝ) => L z)
    (hDDG.hasFDerivAt.comp v hX).fderiv
  have hb := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ((Fin 3 → ℝ) →L[ℝ] ℝ) => L z)
    (hDG.hasFDerivAt.comp v hX).fderiv
  change fderiv ℝ A v z = _ at ha
  change fderiv ℝ B v z = _ at hb
  simp only [ContinuousLinearMap.comp_apply] at ha hb
  rw [ha,hb,originalNormalLiftLinear_fderiv c v u z hc2,
    originalNormalLiftLinear_fderiv c v w z hc2,originalNormalLiftSecond_fderiv c v u w z hc] at hz
  simp only [A,B,ContinuousLinearMap.add_apply] at hz
  rw [originalNormal_linear_normal (fderiv ℝ G (originalNormalLift c v))] at hz
  unfold originalNormalLiftSecond at hz ⊢
  linarith

end PaperI
