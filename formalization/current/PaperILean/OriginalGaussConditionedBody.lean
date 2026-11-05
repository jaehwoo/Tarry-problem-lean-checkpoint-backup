import PaperILean.OriginalGaussBodyCoefficientBounds

/-! I1305: compose the original coefficient-to-graph estimates with the actual
Gauss body calculation. The constant precedes phase, normal order, graph,
inverse and base point. A full-parent radius is not asserted here. -/
set_option maxSynthPendingDepth 4
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology ContDiff

theorem originalGauss_graph_jets_body_bounds
    (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c ![Y a,a 1]) (hY : DifferentiableAt ℝ Y a)
    (hr : originalGaussR c ![Y a,a 1] ≠ 0)
    (hright : ∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0)
    (M : ℝ) (hM : 1 ≤ M)
    (h2 : ‖fderiv ℝ (fderiv ℝ c) ![Y a,a 1]‖ ≤ M^6)
    (h3 : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ c)) ![Y a,a 1]‖ ≤ 4*M^10)
    (hi : |(originalGaussR c ![Y a,a 1])⁻¹| ≤ M) :
    |originalGaussShear c ![Y a,a 1]| ≤ 4*M^11 ∧
    |(originalGaussGraphHessian c ![Y a,a 1]).det/originalGaussR c ![Y a,a 1]| ≤ 32*M^21 ∧
    |fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![1,0]| ≤ 32*M^23 ∧
    |fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![0,1]| ≤ 256*M^33 ∧
    ∀ u : Fin 2 → ℝ,
      ‖originalAffineBodyCoordinates (originalGaussFrameField c Y a)
        (originalGaussFrameVelocity c Y a u)‖ ≤ 384*M^33*‖u‖ := by
  have hM0 : 0 ≤ M := by linarith
  have hH : 1 ≤ 4*M^10 := by nlinarith [one_le_pow₀ hM (n := 10)]
  have h2' : ‖fderiv ℝ (fderiv ℝ c) ![Y a,a 1]‖ ≤ 4*M^10 := by
    apply h2.trans
    have hp := pow_le_pow_right₀ hM (by decide : 6 ≤ 10)
    nlinarith [pow_nonneg hM0 10]
  have hc2 : ContDiffAt ℝ 2 c ![Y a,a 1] := hc.of_le (by decide)
  obtain ⟨hR,hS,hT⟩ := originalGauss_second_components_bound c _ hc2 (4*M^10) h2'
  have hd := originalGauss_shear_norm_bound c _ (4*M^10) M hM0 hS hi
  have hs := originalGauss_det_ratio_bound c _ hc2 (4*M^10) M (by positivity) hM0 hR hS hT hi
  obtain ⟨hp,hz⟩ := originalGauss_same_shear_derivative_bounds c Y a hc hY hr hright
    (4*M^10) M hH hM h2' h3 hi
  refine ⟨?_,?_,?_,?_,?_⟩
  · convert hd using 1 <;> ring
  · convert hs using 1 <;> ring
  · convert hp using 1 <;> ring
  · convert hz using 1 <;> ring
  · intro u
    have hb := originalGauss_body_coordinates_bound c Y a u hc hY hr hright
      (4*M^10) M hH hM h2' h3 hi
    convert hb using 1 <;> ring

theorem originalGauss_manuscript_coefficient_body_bounds (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M : ℝ, 1 ≤ M → ∀ F : CoefficientSpace k,
      C*coefficientEuclideanNorm F ≤ M → ∀ m : ℕ, 2 ≤ m → m ≤ k/2 →
      ∀ (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ), ContinuousAt c ![Y a,a 1] →
      originalNormalLift c ![Y a,a 1] ∈ X →
      (∀ᶠ t in 𝓝 (![Y a,a 1] : Fin 2 → ℝ), originalNormalPhase F (m-1) (originalNormalLift c t)=0) →
      originalNormalPhase F m (originalNormalLift c ![Y a,a 1]) ≠ 0 →
      |(originalNormalPhase F m (originalNormalLift c ![Y a,a 1]))⁻¹| ≤ M →
      originalGaussR c ![Y a,a 1] ≠ 0 → |(originalGaussR c ![Y a,a 1])⁻¹| ≤ M →
      DifferentiableAt ℝ Y a →
      (∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0) →
      |originalGaussShear c ![Y a,a 1]| ≤ 4*M^11 ∧
      |(originalGaussGraphHessian c ![Y a,a 1]).det/originalGaussR c ![Y a,a 1]| ≤ 32*M^21 ∧
      |fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![1,0]| ≤ 32*M^23 ∧
      |fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![0,1]| ≤ 256*M^33 ∧
      ∀ u : Fin 2 → ℝ,
        ‖originalAffineBodyCoordinates (originalGaussFrameField c Y a)
          (originalGaussFrameVelocity c Y a u)‖ ≤ 384*M^33*‖u‖ := by
  obtain ⟨C,hC,hb⟩ := originalNormalPhase_manuscript_coefficient_bounds k X hX
  refine ⟨C,hC,?_⟩
  intro M hM F hF m hm hmk c Y a hc hx hroot hk hki hr hri hY hright
  obtain ⟨h1,h2,h3⟩ := hb M hM F hF m hm hmk c _ hc hx hroot hk hki
  have he : m-1+1=m := by omega
  have hcs := originalNormalPhase_same_graph_smooth F (m-1) c _ hc hroot (by simpa only [he] using hk)
  exact originalGauss_graph_jets_body_bounds c Y a
    (hcs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)) hY hr hright M hM h2 h3 hri

end PaperI
