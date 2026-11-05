import PaperILean.OriginalFrameHaarFiber
import PaperILean.OriginalHaarWindowSingularValue

/-! The manuscript's literal least-singular-value statement of the complete
conditional Haar lemma. The physical matrix uses an orthonormal subgroup
domain basis and all domain Gram eigenvalues, including rank-deficient zeros. -/
noncomputable section
namespace PaperI
open Set MeasureTheory OriginalHaarWindowMeasures OriginalHaarArbitraryPhase
open scoped ENNReal

/-- Whole source lemma I2322-I2340 with its actual s_min hypothesis.
Named accepted published inputs remain explicit; every project application,
arbitrary phase, constant representative and coset passage is proved. -/
theorem originalFrameHaarFiber_literal
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
        (∀ J ∈ W, P^(-c) ≤ originalHaarPhysicalLeastSingularValue K J) →
        ∀ (f : PhysicalSpace → ℝ) (g₀ : Fin 6 → ℝ),
          (subgroupHaar K {g | g ∈ originalHaarSubgroupSet K ∧
            ∃ F ∈ W, ∀ x : PhysicalSpace,
              phase F x = normalizedAlong f (originalUpperAffineComp g₀ g) x} ≤
            ENNReal.ofReal (A0*P^b)) ∧
          (K = .H → subgroupHaar K {g | g ∈ originalHaarSubgroupSet K ∧
            ∃ F ∈ W, ∀ x : PhysicalSpace,
              phase F x = normalizedAlong f (originalUpperAffineComp g g₀) x} ≤
            ENNReal.ofReal (A0*P^b)) := by
  obtain ⟨A0,hA0,hbound⟩ := originalFrameHaarFiber
    hCell hPath hHardt hQE hNash hPiece k s D
  refine ⟨A0,hA0,?_⟩
  intro c
  obtain ⟨b,hb,hmain⟩ := hbound c
  refine ⟨b,hb,?_⟩
  intro K A W hAc hAd hAW P hP hnorm hpiv f g₀
  apply hmain K A W hAc hAd hAW P hP hnorm ?_ f g₀
  intro J hJ v hv
  exact (mul_le_mul_of_nonneg_right (hpiv J hJ) (coordinateL2Norm_nonneg v)).trans
    (originalHaarPhysicalLeastSingularValue_mul_norm_le K J v hv)

end PaperI
