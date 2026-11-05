import PaperILean.OriginalUpperNormalPullback
import PaperILean.OriginalNormalPhaseJetBounds

/-! I848/I1301-I1305: coefficient estimates at the fixed normalized origin.
The complete pulled-back phase, the same graph and its actual normal pivot
are used. The degree-only constant precedes every frame and graph choice. -/
set_option maxSynthPendingDepth 4
noncomputable section
namespace PaperI
open Filter
open scoped Topology ContDiff

theorem originalGaussGraphPullback_continuousAt (g : Fin 6 → ℝ)
    (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hc : ContinuousAt c (originalGaussGraphBaseChange g v)) :
    ContinuousAt (originalGaussGraphPullback g c) v := by
  exact (((hc.comp (originalGaussGraphBaseChange_hasFDerivAt g v).continuousAt).sub
    (continuousAt_const.mul (continuous_apply (0 : Fin 2)).continuousAt)).sub
    (continuousAt_const.mul (continuous_apply (1 : Fin 2)).continuousAt)).sub continuousAt_const

theorem originalGaussGraphPullback_contDiffAt (g : Fin 6 → ℝ)
    (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) (n : WithTop ℕ∞)
    (hc : ContDiffAt ℝ n c (originalGaussGraphBaseChange g v)) :
    ContDiffAt ℝ n (originalGaussGraphPullback g c) v := by
  have hb : ContDiffAt ℝ n (originalGaussGraphBaseChange g) v := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact (((contDiff_apply ℝ ℝ (0 : Fin 2)).contDiffAt.add
        (contDiffAt_const.mul (contDiff_apply ℝ ℝ (1 : Fin 2)).contDiffAt)).add contDiffAt_const)
    · exact (contDiff_apply ℝ ℝ (1 : Fin 2)).contDiffAt.add contDiffAt_const
  exact ((((hc.comp v hb).sub (contDiffAt_const.mul (contDiff_apply ℝ ℝ (0 : Fin 2)).contDiffAt)).sub
    (contDiffAt_const.mul (contDiff_apply ℝ ℝ (1 : Fin 2)).contDiffAt)).sub contDiffAt_const)

theorem originalGaussFrameField_base_zero (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ) :
    originalGaussGraphBaseChange (originalGaussFrameField c Y a) 0 = ![Y a,a 1] := by
  ext i
  fin_cases i <;> simp [originalGaussGraphBaseChange,originalGaussFrameField,originalGaussNormalFrame]

theorem originalGaussFrameField_pullback_value_zero (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ) :
    originalGaussGraphPullback (originalGaussFrameField c Y a) c 0 = 0 := by
  unfold originalGaussGraphPullback
  rw [originalGaussFrameField_base_zero]
  simp [originalGaussFrameField,originalGaussNormalFrame]

theorem originalGaussFrameField_pullback_lift_zero (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ) :
    originalNormalLift (originalGaussGraphPullback (originalGaussFrameField c Y a) c) 0 = 0 := by
  ext i
  fin_cases i <;> simp [originalNormalLift,originalGaussFrameField_pullback_value_zero]

theorem originalGaussFrameField_normal_at_origin {k : ℕ} (F : CoefficientSpace k)
    (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    originalNormalPhase (originalUpperCoefficientPullback F (originalGaussFrameField c Y a)) n 0 =
      originalNormalPhase F n (originalNormalLift c ![Y a,a 1]) := by
  rw [originalUpperCoefficientPullback_normal F _ n hn]
  congr 1
  ext i
  fin_cases i <;> simp [originalUpperAffineEval,originalGaussFrameField,originalGaussNormalFrame,originalNormalLift]

theorem originalGaussFrameField_normal_root_germ {k : ℕ} (F : CoefficientSpace k)
    (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hroot : ∀ᶠ v in 𝓝 (![Y a,a 1] : Fin 2 → ℝ),
      originalNormalPhase F n (originalNormalLift c v)=0) :
    ∀ᶠ v in 𝓝 (0 : Fin 2 → ℝ),
      originalNormalPhase (originalUpperCoefficientPullback F (originalGaussFrameField c Y a)) n
        (originalNormalLift (originalGaussGraphPullback (originalGaussFrameField c Y a) c) v)=0 := by
  apply originalUpperCoefficientPullback_graph_root_germ F _ n hn c 0
  simpa only [originalGaussFrameField_base_zero] using hroot

theorem originalGauss_normalized_coefficient_graph_bounds (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M : ℝ, 1 ≤ M → ∀ F : CoefficientSpace k,
      ∀ m : ℕ, 2 ≤ m → m ≤ k/2 → ∀ (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ),
      ContinuousAt c ![Y a,a 1] →
      C*coefficientEuclideanNorm (originalUpperCoefficientPullback F (originalGaussFrameField c Y a)) ≤ M →
      (∀ᶠ v in 𝓝 (![Y a,a 1] : Fin 2 → ℝ), originalNormalPhase F (m-1) (originalNormalLift c v)=0) →
      originalNormalPhase F m (originalNormalLift c ![Y a,a 1]) ≠ 0 →
      |(originalNormalPhase F m (originalNormalLift c ![Y a,a 1]))⁻¹| ≤ M →
      let b := originalGaussGraphPullback (originalGaussFrameField c Y a) c
      ‖fderiv ℝ b 0‖ ≤ M^2 ∧ ‖fderiv ℝ (fderiv ℝ b) 0‖ ≤ M^6 ∧
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ b)) 0‖ ≤ 4*M^10 := by
  obtain ⟨C,hC,hbound⟩ := originalNormalPhase_manuscript_coefficient_bounds k {0} Bornology.isBounded_singleton
  refine ⟨C,hC,?_⟩
  intro M hM F m hm hmk c Y a hc hF hroot hk hki
  have hcont : ContinuousAt (originalGaussGraphPullback (originalGaussFrameField c Y a) c) 0 := by
    apply originalGaussGraphPullback_continuousAt
    simpa only [originalGaussFrameField_base_zero] using hc
  apply hbound M hM _ hF m hm hmk _ 0 hcont
  · simp only [originalGaussFrameField_pullback_lift_zero,Set.mem_singleton_iff]
  · exact originalGaussFrameField_normal_root_germ F c Y a (m-1) (by omega) hroot
  · simpa only [originalGaussFrameField_pullback_lift_zero,
      originalGaussFrameField_normal_at_origin F c Y a m (by omega)] using hk
  · simpa only [originalGaussFrameField_pullback_lift_zero,
      originalGaussFrameField_normal_at_origin F c Y a m (by omega)] using hki

end PaperI
