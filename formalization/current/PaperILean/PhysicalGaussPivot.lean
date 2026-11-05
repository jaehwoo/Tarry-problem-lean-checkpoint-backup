import PaperILean.NormalJacobianStage
import PaperILean.OriginalNormalGraphSmooth
import PaperILean.OriginalNormalJetCalculus

/-! I3353[0,143): the actual fixed-physical-center Gauss normalization pivot.
The graph is the selected local graph through the normalized origin, as in I2129.
No coefficient-substitution or joint incidence-density conclusion is asserted. -/

noncomputable section
namespace PaperI.PhysicalGaussPivot

open Filter PaperI.NormalFibers
open scoped Topology ContDiff

/-- The original y,y derivative of the selected graph. -/
def graphYY (c : (Fin 2 → ℝ) → ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ c) 0 (Pi.single 0 1) (Pi.single 0 1)

/-- Differentiating the normalized phase retains the full derivative phase. -/
theorem normalized_phase_dx (F : Poly) (w : FrameSpace) (e f : ℝ) :
    MvPolynomial.pderiv 0
        (pullback w e f F - MvPolynomial.C (MvPolynomial.eval 0 (pullback w e f F))) =
      pullback w e f (MvPolynomial.pderiv 0 F) := by
  rw [map_sub, MvPolynomial.pderiv_C, sub_zero, pullback_dx]

private theorem polynomial_yy_second (H : Poly) :
    fderiv ℝ (fderiv ℝ (fun x : PhysicalSpace => MvPolynomial.eval x H)) 0
        (Pi.single 1 1) (Pi.single 1 1) =
      MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 H)) := by
  let G : PhysicalSpace → ℝ := fun x => MvPolynomial.eval x H
  have hA : DifferentiableAt ℝ (fderiv ℝ G) 0 :=
    (((contDiff_evalPolynomial H 2).contDiffAt).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  have he : (fun x : PhysicalSpace => fderiv ℝ G x (Pi.single 1 1)) =
      (fun x : PhysicalSpace => MvPolynomial.eval x (MvPolynomial.pderiv 1 H)) := by
    funext x
    exact fderiv_evalPolynomial_single H x 1
  have ha := originalNormal_clm_apply_fderiv (fderiv ℝ G)
    (fun _ : PhysicalSpace => (Pi.single 1 1 : PhysicalSpace)) 0
    (Pi.single 1 1) hA (differentiableAt_const _)
  have ha' : fderiv ℝ (fun x : PhysicalSpace => fderiv ℝ G x (Pi.single 1 1)) 0
        (Pi.single 1 1) = fderiv ℝ (fderiv ℝ G) 0 (Pi.single 1 1) (Pi.single 1 1) := by
    simpa using ha
  rw [he, fderiv_evalPolynomial_single] at ha'
  exact ha'.symm

/-- The yy graph identity uses local roots and derives smoothness of that same graph. -/
theorem graph_yy_derivative (H : Poly) (c : (Fin 2 → ℝ) → ℝ)
    (hc : ContinuousAt c 0) (hc0 : c 0 = 0) (hDc : fderiv ℝ c 0 = 0)
    (hroot : ∀ᶠ v in 𝓝 0, MvPolynomial.eval ![c v, v 0, v 1] H = 0)
    (hlam : MvPolynomial.eval 0 (MvPolynomial.pderiv 0 H) ≠ 0) :
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 H)) =
      -MvPolynomial.eval 0 (MvPolynomial.pderiv 0 H) * graphYY c := by
  let G : PhysicalSpace → ℝ := fun x => MvPolynomial.eval x H
  have hcenter : originalNormalLift c 0 = (0 : PhysicalSpace) := by
    ext i
    fin_cases i <;> simp [originalNormalLift, hc0]
  have hnormal : (![1, 0, 0] : PhysicalSpace) = Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp [Pi.single_apply]
  have hG : ContDiffAt ℝ 2 G (originalNormalLift c 0) :=
    (contDiff_evalPolynomial H 2).contDiffAt
  have hk : fderiv ℝ G (originalNormalLift c 0) ![1, 0, 0] ≠ 0 := by
    rw [hcenter, hnormal]
    change fderiv ℝ (fun x : PhysicalSpace => MvPolynomial.eval x H) 0 (Pi.single 0 1) ≠ 0
    rw [fderiv_evalPolynomial_single]
    exact hlam
  have hc2 : ContDiffAt ℝ 2 c 0 :=
    originalNormal_same_graph_contDiffAt G c 0 2 (by norm_num) hG hc hroot hk
  have hroot' : ∀ᶠ v in 𝓝 0, G (originalNormalLift c v) = 0 := hroot
  have hid := originalNormal_root_second_identity G c 0
    (Pi.single 0 1) (Pi.single 0 1) hG hc2 hroot'
  have hiy : originalNormalLiftLinear c 0 (Pi.single 0 1) =
      (Pi.single 1 1 : PhysicalSpace) := by
    rw [originalNormalLiftLinear_apply, hDc]
    ext i
    fin_cases i <;> simp [Pi.single_apply]
  rw [hcenter, hiy, hnormal] at hid
  change fderiv ℝ (fderiv ℝ (fun x : PhysicalSpace => MvPolynomial.eval x H)) 0
      (Pi.single 1 1) (Pi.single 1 1) + graphYY c *
      fderiv ℝ (fun x : PhysicalSpace => MvPolynomial.eval x H) 0 (Pi.single 0 1) = 0 at hid
  rw [polynomial_yy_second, fderiv_evalPolynomial_single] at hid
  linarith

/-- I3353[0,143): apply the saved actual chart-I Jacobian to G = F_x.
The four equations are evaluated at the actual affine frame with fixed (e,f).
The graph-origin and zero-tangent hypotheses are the normalized convention I2129.
The result holds for every full polynomial F, hence for every finite-degree phase. -/
theorem physical_gauss_pivot_stage
    (F : Poly) (e f : ℝ) (w : FrameSpace) (c : (Fin 2 → ℝ) → ℝ)
    (hc : ContinuousAt c 0) (hc0 : c 0 = 0) (hDc : fderiv ℝ c 0 = 0)
    (hroot : ∀ᶠ v in 𝓝 0,
      MvPolynomial.eval ![c v, v 0, v 1] (pullback w e f (MvPolynomial.pderiv 0 F)) = 0)
    (hrows : normalizationEquationsI (MvPolynomial.pderiv 0 F) e f w = 0)
    (hlam : MvPolynomial.eval 0
      (MvPolynomial.pderiv 0 (pullback w e f (MvPolynomial.pderiv 0 F))) ≠ 0)
    (hr : graphYY c ≠ 0) :
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1
        (MvPolynomial.pderiv 1 (pullback w e f (MvPolynomial.pderiv 0 F)))) =
        -MvPolynomial.eval 0
          (MvPolynomial.pderiv 0 (pullback w e f (MvPolynomial.pderiv 0 F))) * graphYY c ∧
      DifferentiableAt ℝ (normalizationEquationsI (MvPolynomial.pderiv 0 F) e f) w ∧
      (ordinaryJacobian (normalizationEquationsI (MvPolynomial.pderiv 0 F) e f) w).det =
        -(MvPolynomial.eval 0
          (MvPolynomial.pderiv 0 (pullback w e f (MvPolynomial.pderiv 0 F)))) ^ 4 * graphYY c ∧
      |(ordinaryJacobian (normalizationEquationsI (MvPolynomial.pderiv 0 F) e f) w).det| =
        |MvPolynomial.eval 0
          (MvPolynomial.pderiv 0 (pullback w e f (MvPolynomial.pderiv 0 F)))| ^ 4 * |graphYY c| := by
  let G := MvPolynomial.pderiv 0 F
  let H := pullback w e f G
  have hyy := graph_yy_derivative H c hc hc0 hDc hroot hlam
  have h0 : MvPolynomial.eval 0 H = 0 := by
    simpa [normalizationEquationsI, H, G] using congrFun hrows 0
  have hy : MvPolynomial.eval 0 (MvPolynomial.pderiv 1 H) = 0 := by
    simpa [normalizationEquationsI, H, G] using congrFun hrows 1
  have hz : MvPolynomial.eval 0 (MvPolynomial.pderiv 2 H) = 0 := by
    simpa [normalizationEquationsI, H, G] using congrFun hrows 2
  have hyz : MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 H)) = 0 := by
    simpa [normalizationEquationsI, H, G] using congrFun hrows 3
  have hyyne : MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 H)) ≠ 0 := by
    rw [hyy]
    exact mul_ne_zero (neg_ne_zero.mpr hlam) hr
  have hframe : w ∈ normalizedFrames G e f :=
    ⟨h0, hlam, hy, hz, Or.inl ⟨hyz, hyyne⟩⟩
  have hsigned := signed_jacobian_chartI G e f w hframe
  change (ordinaryJacobian (normalizationEquationsI G e f) w).det =
    (MvPolynomial.eval 0 (MvPolynomial.pderiv 0 H)) ^ 3 *
      MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 H)) at hsigned
  rw [hyy] at hsigned
  have hsigned' : (ordinaryJacobian (normalizationEquationsI G e f) w).det =
      -(MvPolynomial.eval 0 (MvPolynomial.pderiv 0 H)) ^ 4 * graphYY c :=
    hsigned.trans (by ring)
  refine ⟨hyy, (hasFDerivAt_normalizationEquationsI G e f w).differentiableAt, hsigned', ?_⟩
  rw [hsigned', abs_mul, abs_neg, abs_pow]

end PaperI.PhysicalGaussPivot
