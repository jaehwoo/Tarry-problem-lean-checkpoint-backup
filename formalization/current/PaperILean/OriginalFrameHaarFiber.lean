import PaperILean.OriginalHaarWindowArbitrary
import PaperILean.OriginalHaarWindowRightCoset

/-! Whole manuscript lemma I2322-I2340 under its original explicit window
and physical-pivot hypotheses and the named accepted BPR inputs. Includes
arbitrary polynomial representatives, unbounded coset locations and both
coset orientations for H. No incidence/contact conclusion is assumed. -/
noncomputable section
namespace PaperI
open Set MeasureTheory OriginalHaarWindowMeasures OriginalHaarArbitraryPhase
open OriginalHaarWindowRightCoset
open scoped ENNReal

/-- Complete conditional fixed-frame Haar lemma. Quantification over every
real-valued phase is stronger than the original arbitrary-polynomial statement;
a nonempty window supplies an exact degree-k representative by affine inversion.
The bounds involve only the normalized coefficients, including at path endpoints.
Source I2335's missing brackets are not used as an unnormalized constant bound. -/
theorem originalFrameHaarFiber
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
          (subgroupHaar K {g | g ∈ originalHaarSubgroupSet K ∧
            ∃ F ∈ W, ∀ x : PhysicalSpace,
              phase F x = normalizedAlong f (originalUpperAffineComp g₀ g) x} ≤
            ENNReal.ofReal (A0*P^b)) ∧
          (K = .H → subgroupHaar K {g | g ∈ originalHaarSubgroupSet K ∧
            ∃ F ∈ W, ∀ x : PhysicalSpace,
              phase F x = normalizedAlong f (originalUpperAffineComp g g₀) x} ≤
            ENNReal.ofReal (A0*P^b)) := by
  obtain ⟨A0,hA0,hbound⟩ := originalFrameHaarFiber_left
    hCell hPath hHardt hQE hNash hPiece k s D
  refine ⟨A0,hA0,?_⟩
  intro c
  obtain ⟨b,hb,hleft⟩ := hbound c
  refine ⟨b,hb,?_⟩
  intro K A W hAc hAd hAW P hP hnorm hpiv f g₀
  have hL := hleft K A W hAc hAd hAW P hP hnorm hpiv f g₀
  refine ⟨hL,?_⟩
  intro hK
  subst K
  change haarH _ ≤ _
  rw [← raw_haarH_left_right_domain_measure W f g₀]
  exact hL

end PaperI
