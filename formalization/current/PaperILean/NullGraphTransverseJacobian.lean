import PaperILean.OriginalNormalGraphSmooth
import PaperILean.OriginalNormalJetCalculus
import PaperILean.NormalJacobianStage
import PaperILean.NullGraphRawConstraints

/-! I2371[233,394): the actual normalized graph curvature and raw transverse Jacobian. -/

noncomputable section
namespace PaperI.NullGraphTransverseJacobian

open Filter PaperI.NormalFibers PaperI.NullGraphRawConstraints
open scoped Topology ContDiff

/-- The mixed derivative of the same selected graph, in the original y,z order. -/
def mixedGraphDerivative (c : (Fin 2 → ℝ) → ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ c) 0 (Pi.single 0 1) (Pi.single 1 1)

private theorem polynomial_mixed_second (G : Poly) :
    fderiv ℝ (fderiv ℝ (fun x : PhysicalSpace => MvPolynomial.eval x G)) 0
        (Pi.single 1 1) (Pi.single 2 1) =
      MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G)) := by
  let H : PhysicalSpace → ℝ := fun x => MvPolynomial.eval x G
  have hA : DifferentiableAt ℝ (fderiv ℝ H) 0 :=
    (((contDiff_evalPolynomial G 2).contDiffAt).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  have he : (fun x : PhysicalSpace => fderiv ℝ H x (Pi.single 2 1)) =
      (fun x : PhysicalSpace => MvPolynomial.eval x (MvPolynomial.pderiv 2 G)) := by
    funext x
    exact fderiv_evalPolynomial_single G x 2
  have ha := originalNormal_clm_apply_fderiv (fderiv ℝ H)
    (fun _ : PhysicalSpace => (Pi.single 2 1 : PhysicalSpace)) 0
    (Pi.single 1 1) hA (differentiableAt_const _)
  have ha' : fderiv ℝ (fun x : PhysicalSpace => fderiv ℝ H x (Pi.single 2 1)) 0
        (Pi.single 1 1) = fderiv ℝ (fderiv ℝ H) 0 (Pi.single 1 1) (Pi.single 2 1) := by
    simpa using ha
  rw [he, fderiv_evalPolynomial_single] at ha'
  exact ha'.symm

private theorem pullback_origin (G : Poly) : pullback (0 : FrameSpace) 0 0 G = G := by
  induction G using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      fin_cases i <;> simp [hP, frameVariables]

/-- The mixed derivative follows from the original root equation and its derived smoothness. -/
theorem graph_mixed_derivative {k : ℕ} (J : CoefficientSpace k) (n : ℕ)
    (c : (Fin 2 → ℝ) → ℝ) (hc : ContinuousAt c 0) (hc0 : c 0 = 0)
    (hDc : fderiv ℝ c 0 = 0)
    (hroot : ∀ᶠ v in 𝓝 0, originalNormalPhase J n ![c v, v 0, v 1] = 0)
    (hκ : originalNormalPhase J (n + 1) 0 ≠ 0) :
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1
        (MvPolynomial.pderiv 2 (originalNormalPolynomial J n))) =
      -originalNormalPhase J (n + 1) 0 * mixedGraphDerivative c := by
  have hcenter : originalNormalLift c 0 = (0 : PhysicalSpace) := by
    ext i
    fin_cases i <;> simp [originalNormalLift, hc0]
  have hκ' : originalNormalPhase J (n + 1) ![c 0, (0 : Fin 2 → ℝ) 0, 0] ≠ 0 := by
    change originalNormalPhase J (n + 1) (originalNormalLift c 0) ≠ 0
    rwa [hcenter]
  have hsmooth := originalNormalPhase_same_graph_smooth J n c 0 hc hroot hκ'
  have hG : ContDiffAt ℝ 2 (originalNormalPhase J n) (originalNormalLift c 0) :=
    (originalNormalPhase_contDiff J n 2).contDiffAt
  have hc2 : ContDiffAt ℝ 2 c 0 := hsmooth.of_le (WithTop.coe_le_coe.mpr le_top)
  have hroot' : ∀ᶠ v in 𝓝 0, originalNormalPhase J n (originalNormalLift c v) = 0 := hroot
  have hid := originalNormal_root_second_identity (originalNormalPhase J n) c 0
    (Pi.single 1 1) (Pi.single 0 1) hG hc2 hroot'
  have hiy : originalNormalLiftLinear c 0 (Pi.single 0 1) =
      (Pi.single 1 1 : PhysicalSpace) := by
    rw [originalNormalLiftLinear_apply, hDc]
    ext i
    fin_cases i <;> simp [Pi.single_apply]
  have hiz : originalNormalLiftLinear c 0 (Pi.single 1 1) =
      (Pi.single 2 1 : PhysicalSpace) := by
    rw [originalNormalLiftLinear_apply, hDc]
    ext i
    fin_cases i <;> simp [Pi.single_apply]
  rw [hcenter, hiy, hiz, originalNormalPhase_dx] at hid
  have hfun : originalNormalPhase J n =
      (fun x : PhysicalSpace => MvPolynomial.eval x (originalNormalPolynomial J n)) :=
    funext (originalNormalPhase_eq_eval J n)
  have hsecond : fderiv ℝ (fderiv ℝ (originalNormalPhase J n)) 0
        (Pi.single 1 1) (Pi.single 2 1) =
      MvPolynomial.eval 0 (MvPolynomial.pderiv 1
        (MvPolynomial.pderiv 2 (originalNormalPolynomial J n))) := by
    rw [hfun]
    exact polynomial_mixed_second _
  rw [hsecond] at hid
  change _ + mixedGraphDerivative c * originalNormalPhase J (n + 1) 0 = 0 at hid
  linarith

/-- The two complete source sentences, retaining the raw constraints and original order range. -/
theorem null_graph_transverse_jacobian_stage {k : ℕ} (J : CoefficientSpace k) (m : ℕ)
    (hm : 2 ≤ m) (hmk : m ≤ k / 2) (c : (Fin 2 → ℝ) → ℝ)
    (hc : ContinuousAt c 0) (hc0 : c 0 = 0) (hDc : fderiv ℝ c 0 = 0)
    (hroot : ∀ᶠ v in 𝓝 0, originalNormalPhase J (m - 1) ![c v, v 0, v 1] = 0)
    (hκ : originalNormalPhase J m 0 ≠ 0) (hB : mixedGraphDerivative c ≠ 0)
    (hconstraints : bracketedRawNullConstraints J m 0 = 0) :
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1
        (MvPolynomial.pderiv 2 (originalNormalPolynomial J (m - 1)))) =
        -originalNormalPhase J m 0 * mixedGraphDerivative c ∧
      DifferentiableAt ℝ (bracketedRawNullConstraints J m) 0 ∧
      (ordinaryJacobian (bracketedRawNullConstraints J m) 0).det =
        -2 * (originalNormalPhase J m 0) ^ 4 * mixedGraphDerivative c ∧
      |(ordinaryJacobian (bracketedRawNullConstraints J m) 0).det| =
        2 * |originalNormalPhase J m 0| ^ 4 * |mixedGraphDerivative c| := by
  have hn : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
  have hκn : originalNormalPhase J (m - 1 + 1) 0 ≠ 0 := by rwa [hn]
  have hmix := graph_mixed_derivative J (m - 1) c hc hc0 hDc hroot hκn
  rw [hn] at hmix
  let G := originalNormalPolynomial J (m - 1)
  have hpull : pullback (0 : FrameSpace) 0 0 G = G := pullback_origin G
  have hx : MvPolynomial.eval 0 (MvPolynomial.pderiv 0 G) = originalNormalPhase J m 0 := by
    rw [← originalNormalPolynomial_succ, ← originalNormalPhase_eq_eval, hn]
  have hrows : normalizationEquationsII G 0 0 0 = 0 := by
    simpa only [bracketedRawNullConstraints_eq J m hm] using hconstraints
  have h0 : MvPolynomial.eval 0 G = 0 := by
    simpa [normalizationEquationsII, hpull] using congrFun hrows 0
  have hy : MvPolynomial.eval 0 (MvPolynomial.pderiv 1 G) = 0 := by
    simpa [normalizationEquationsII, hpull] using congrFun hrows 1
  have hz : MvPolynomial.eval 0 (MvPolynomial.pderiv 2 G) = 0 := by
    simpa [normalizationEquationsII, hpull] using congrFun hrows 2
  have hzz : MvPolynomial.eval 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 G)) = 0 := by
    simpa [normalizationEquationsII, hpull] using congrFun hrows 3
  have hmixne : MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G)) ≠ 0 := by
    rw [hmix]
    exact mul_ne_zero (neg_ne_zero.mpr hκ) hB
  have hframe : (0 : FrameSpace) ∈ normalizedFrames G 0 0 := by
    change _ = 0 ∧ _ ≠ 0 ∧ _ = 0 ∧ _ = 0 ∧ ((_ = 0 ∧ _ ≠ 0) ∨ (_ = 0 ∧ _ ≠ 0))
    simp only [hpull]
    exact ⟨h0, by rwa [hx], hy, hz, Or.inr ⟨hzz, hmixne⟩⟩
  have hsigned := signed_jacobian_chartII G 0 0 0 hframe
  rw [hpull, hx, hmix] at hsigned
  have hsigned' : (ordinaryJacobian (bracketedRawNullConstraints J m) 0).det =
      -2 * (originalNormalPhase J m 0) ^ 4 * mixedGraphDerivative c := by
    rw [bracketedRawNullConstraints_eq J m hm]
    exact hsigned.trans (by ring)
  refine ⟨hmix, ?_, hsigned', ?_⟩
  · rw [bracketedRawNullConstraints_eq J m hm]
    exact (hasFDerivAt_normalizationEquationsII G 0 0 0).differentiableAt
  · rw [hsigned', abs_mul, abs_mul, abs_pow]
    norm_num

end PaperI.NullGraphTransverseJacobian
