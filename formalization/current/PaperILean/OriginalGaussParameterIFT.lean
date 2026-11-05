import PaperILean.OriginalImplicitSection
import PaperILean.OriginalGaussCommonRootCover

/-! I1317/I1319: the original two equations, with (p,z) as parameters.
The regular output Jacobian gives a smooth local branch and uniqueness of
every nearby zero. No quantitative radius or admissibility margin is claimed. -/
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology ContDiff

def originalGaussParameterEquations {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (u : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : Fin 2 → ℝ :=
  originalGaussRootEquations (originalGaussPhaseSlice (originalNormalPhase F n) (u.1 1)) (u.1 0) u.2

theorem originalGaussParameterEquations_apply {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (a w : Fin 2 → ℝ) :
    originalGaussParameterEquations F n (a,w)=
      ![originalNormalPhase F n ![w 0,w 1,a 1],
        fderiv ℝ (originalNormalPhase F n) ![w 0,w 1,a 1] ![0,1,0]+
          a 0*fderiv ℝ (originalNormalPhase F n) ![w 0,w 1,a 1] ![1,0,0]] :=
  originalGauss_phase_root_equations _ _ _ _
    ((originalNormalPhase_contDiff F n 2).differentiable (by norm_num)).differentiableAt

theorem originalGaussParameterEquations_contDiff {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (d : WithTop ℕ∞) : ContDiff ℝ d (originalGaussParameterEquations F n) := by
  let T : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) → (Fin 3 → ℝ) :=
    fun u => ![u.2 0,u.2 1,u.1 1]
  have hT : ContDiff ℝ d T := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff.comp contDiff_snd
    · exact (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff.comp contDiff_snd
    · exact (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff.comp contDiff_fst
  have hpoly (j : Fin 3) :
      ContDiff ℝ d (fun u => fderiv ℝ (originalNormalPhase F n) (T u) (Pi.single j 1)) := by
    have he : (fun u => fderiv ℝ (originalNormalPhase F n) (T u) (Pi.single j 1))=
        (fun u => MvPolynomial.eval (T u) (MvPolynomial.pderiv j (originalNormalPolynomial F n))) :=
      funext (fun u => originalNormalPhase_partial F n (T u) j)
    rw [he]
    exact (contDiff_evalPolynomial _ d).comp hT
  have he : originalGaussParameterEquations F n=(fun u =>
      (![originalNormalPhase F n (T u),
      fderiv ℝ (originalNormalPhase F n) (T u) ![0,1,0]+
      u.1 0*fderiv ℝ (originalNormalPhase F n) (T u) ![1,0,0]] : Fin 2 → ℝ)) := by
    funext u
    exact originalGaussParameterEquations_apply F n u.1 u.2
  rw [he]
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (originalNormalPhase_contDiff F n d).comp hT
  · simpa only [originalNormal_x_basis,originalNormal_y_basis] using
      (hpoly 1).add (((ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff.comp contDiff_fst).mul (hpoly 0))

theorem originalGaussParameterEquations_zero {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (a w : Fin 2 → ℝ) (hw : w∈originalGaussRegularRootSet F n (a 0) (a 1)) :
    originalGaussParameterEquations F n (a,w)=0 := by
  rw [originalGaussParameterEquations_apply]
  ext i
  fin_cases i
  · exact hw.1
  · exact hw.2.1

theorem originalGaussParameterEquations_partial {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (a w : Fin 2 → ℝ) (hw : w∈originalGaussRegularRootSet F n (a 0) (a 1)) :
    HasFDerivAt (fun t => originalGaussParameterEquations F n (a,t))
      (originalGaussMatrixEquiv
        (originalGaussRootJacobian (originalGaussPhaseSlice (originalNormalPhase F n) (a 1)) (a 0) w)
        hw.2.2).toContinuousLinearMap w :=
  (originalGaussRootEquations_hasStrictFDerivAt _ _ _
    (originalGaussPhaseSlice_contDiffAt _ _ _ (originalNormalPhase_contDiff F n 2).contDiffAt) hw.2.2).hasFDerivAt

theorem originalGauss_regular_parameter_local_branch {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (a w : Fin 2 → ℝ) (hw : w∈originalGaussRegularRootSet F n (a 0) (a 1)) :
    ∃ b : (Fin 2 → ℝ) → (Fin 2 → ℝ), b a=w ∧ ContDiffAt ℝ ∞ b a ∧
      (∀ᶠ q in 𝓝 a, originalGaussParameterEquations F n (q,b q)=0) ∧
      (∀ᶠ u in 𝓝 (a,w), originalGaussParameterEquations F n u=0 → u.2=b u.1) :=
  original_parameter_local_zero (originalGaussParameterEquations F n) a w ∞ (by simp)
    (originalGaussParameterEquations_contDiff F n ∞).contDiffAt
    (originalGaussParameterEquations_zero F n a w hw) _
    (originalGaussParameterEquations_partial F n a w hw)

end PaperI
