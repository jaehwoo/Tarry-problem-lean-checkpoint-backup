import PaperILean.OriginalHaarWindowPowerBound
import PaperILean.OriginalHaarArbitraryPhase

/-! Actual unrestricted-polynomial and arbitrary-left-coset conclusion of
the fixed-frame Haar lemma, using the proved coefficient-window estimate.
The lower-pivot hypothesis is the source's usual Euclidean singular-value
inequality, not a supplied path/body/relative-box conclusion. -/
noncomputable section
namespace PaperI
open Set MeasureTheory OriginalHaarWindowMeasures OriginalHaarArbitraryPhase
open scoped ENNReal

/-- The original s_min >= P^(-c) hypothesis in its equivalent universal
Euclidean lower-norm form, restricted to the literal physical Lie subspace. -/
def originalHaarPhysicalPivotLower {k : ℕ} (K : OriginalHaarSubgroup)
    (W : Set (CoefficientSpace k)) (P c : ℝ) : Prop :=
  ∀ J ∈ W, ∀ v ∈ originalHaarSubgroupSet K,
    P^(-c)*coordinateL2Norm v ≤
      coefficientEuclideanNorm (originalHaarPhysicalLieAction J v)

theorem originalHaarPhysicalPivotLower_inverse {k : ℕ} {K : OriginalHaarSubgroup}
    {W : Set (CoefficientSpace k)} {P c : ℝ} (hP : 0 < P)
    (hp : originalHaarPhysicalPivotLower K W P c) :
    ∀ J ∈ W, ∀ v ∈ originalHaarSubgroupSet K,
      coordinateL2Norm v ≤ P^c*
        coefficientEuclideanNorm (originalHaarPhysicalLieAction J v) := by
  intro J hJ v hv
  have hpos : 0 < P^c := Real.rpow_pos_of_pos hP c
  have h := mul_le_mul_of_nonneg_left (hp J hJ v hv) hpos.le
  rw [Real.rpow_neg hP.le,← mul_assoc,mul_inv_cancel₀ hpos.ne',one_mul] at h
  exact h

/-- The source's unrestricted phase quantifier and all left coset locations.
It is stronger than the polynomial assertion: if even one window point exists,
the exact inverse affine witness supplies a degree-k representative modulo
constants. There is no arbitrary-phase truncation or new degree assumption. -/
theorem originalFrameHaarFiber_left
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D : ℕ) :
    ∃ A0 : ℝ, 1 ≤ A0 ∧ ∀ c : ℝ, ∃ b : ℝ, 0 ≤ b ∧
      ∀ (K : OriginalHaarSubgroup)
        (A : Finset (MvPolynomial (MonomialIndex k) ℝ)) (W : Set (CoefficientSpace k)),
        A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A W →
        ∀ P : ℝ, 2 ≤ P →
        (∀ J ∈ W, coefficientEuclideanNorm J ≤ P^c) →
        originalHaarPhysicalPivotLower K W P c →
        ∀ (f : PhysicalSpace → ℝ) (g₀ : Fin 6 → ℝ),
          subgroupHaar K {g | g ∈ originalHaarSubgroupSet K ∧
            ∃ F ∈ W, ∀ x : PhysicalSpace,
              phase F x = normalizedAlong f (originalUpperAffineComp g₀ g) x} ≤
            ENNReal.ofReal (A0*P^b) := by
  obtain ⟨A0,hA0,hbound⟩ := originalHaarOrbitWindow_power_bound
    hCell hPath hHardt hQE hNash hPiece k s D
  refine ⟨A0,hA0,?_⟩
  intro c
  obtain ⟨b,hb,hFbound⟩ := hbound c
  refine ⟨b,hb,?_⟩
  intro K A W hAc hAd hAW P hP hnorm hpiv f g₀
  have hpiv' := originalHaarPhysicalPivotLower_inverse (by linarith : 0 < P) hpiv
  apply arbitrary_left_coset_bound_of_coefficient_bound
    (originalHaarSubgroupSet K) W (subgroupHaar K) (ENNReal.ofReal (A0*P^b))
  intro F
  simpa only [coefficientOrbitSet,originalHaarOrbitWindow] using
    hFbound K F A W hAc hAd hAW P hP hnorm hpiv'

end PaperI
