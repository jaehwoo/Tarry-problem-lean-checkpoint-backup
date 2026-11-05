import PaperILean.OriginalHaarWindowRelativeStage
import PaperILean.OriginalHaarWindowMeasures

/-! The original finite-component/relative-coordinate/Haar-box argument
for every bounded-degree quotient phase and all three source subgroups.
The arbitrary-polynomial representative and coset passages are separate. -/
noncomputable section
namespace PaperI
open Set MeasureTheory
open OriginalHaarWindowMeasures
open scoped ENNReal
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Complete normalized Haar bound from the original norm and physical pivot
hypotheses. Constants are uniform before the phase, window coefficients,
component basepoints, and both norm/pivot scale bounds. -/
theorem originalHaarOrbitWindow_volume_stage
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D : ℕ) :
    ∃ N M : ℕ, ∀ (K : OriginalHaarSubgroup) (F : CoefficientSpace k)
      (A : Finset (MvPolynomial (MonomialIndex k) ℝ)) (W : Set (CoefficientSpace k)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A W →
      ∀ B H : ℝ, 0 ≤ B → 0 ≤ H →
      (∀ J ∈ W, coefficientEuclideanNorm J ≤ B) →
      (∀ J ∈ W, ∀ v ∈ originalHaarSubgroupSet K,
        coordinateL2Norm v ≤ H*coefficientEuclideanNorm (originalHaarPhysicalLieAction J v)) →
      let L : ℝ := H*(Fintype.card (MonomialIndex k):ℝ)*(2*B)
      let R : ℝ := L*(1+L)^2
      subgroupHaar K (originalHaarOrbitWindow K F W) ≤
        (N:ℝ≥0∞)*ENNReal.ofReal (2*((1+2*R)^M))^4 := by
  obtain ⟨N,M,hRel⟩ := originalHaarOrbitWindow_relative_stage
    hCell hPath hHardt hQE hNash hPiece k s D
  refine ⟨N,M,?_⟩
  intro K F A W hAc hAd hAW B H hB hH hWnorm hWpiv
  dsimp only
  let E := originalHaarOrbitWindow K F W
  let L : ℝ := H*(Fintype.card (MonomialIndex k):ℝ)*(2*B)
  let R : ℝ := L*(1+L)^2
  let T : ℝ := (1+2*R)^M
  have hR : 0 ≤ R := by dsimp [R,L]; positivity
  have hT : 1 ≤ T := one_le_pow₀ (by linarith : 1 ≤ 1+2*R)
  have hr := hRel K F A W hAc hAd hAW B H hB hH hWnorm hWpiv
  letI : Finite (ConnectedComponents E) := hr.1
  letI : Fintype (ConnectedComponents E) := Fintype.ofFinite _
  let repr : ConnectedComponents E → E := fun c => (ConnectedComponents.surjective_coe c).choose
  have hrepr (c : ConnectedComponents E) : ConnectedComponents.mk (repr c) = c :=
    (ConnectedComponents.surjective_coe c).choose_spec
  let centers : ConnectedComponents E → (Fin 6 → ℝ) := fun c => (repr c).val
  have hcenters : ∀ c, centers c ∈ originalHaarSubgroupSet K := fun c => (repr c).property.1
  have hcover : ∀ x ∈ E, ∃ c, ‖originalUpperRelativeFrame (centers c) x‖ ≤ T := by
    intro x hx
    let c : ConnectedComponents E := ConnectedComponents.mk (⟨x,hx⟩:E)
    have heq : ConnectedComponents.mk (⟨x,hx⟩:E) = ConnectedComponents.mk (repr c) := (hrepr c).symm
    have hxc : x ∈ connectedComponentIn E (centers c) := by
      rw [connectedComponentIn_eq_image (repr c).property]
      exact ⟨⟨x,hx⟩,ConnectedComponents.coe_eq_coe'.mp heq,rfl⟩
    have hcc : centers c ∈ connectedComponentIn E (centers c) :=
      mem_connectedComponentIn (repr c).property
    have hbound := hr.2.2 (centers c) (centers c) x hcc hxc
    refine ⟨c,?_⟩
    dsimp only [T]
    exact (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)).trans hbound
  have hvol := finite_relative_box_cover K E centers T hT hcenters hcover
  have hcard : (Fintype.card (ConnectedComponents E):ℝ≥0∞) ≤ (N:ℝ≥0∞) := by
    have hc : Fintype.card (ConnectedComponents E) ≤ N := by
      simpa only [Nat.card_eq_fintype_card] using hr.2.1
    exact_mod_cast hc
  exact hvol.trans (mul_le_mul_right' hcard _)

end PaperI
