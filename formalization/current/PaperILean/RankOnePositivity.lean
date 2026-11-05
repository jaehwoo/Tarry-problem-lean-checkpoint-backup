import PaperILean.RankOneMatrixFactor
import PaperILean.RankOneAffinePhase

/-! I3251[0,577): exact positivity for normalized affine fields on the
original stopped augmented state. This proves the pointwise algebraic stage;
it does not assert a uniform minimum, conditioning exponent, or H bound. -/

noncomputable section
open Matrix
namespace PaperI.RankOnePositivity
open RankOneAffineMatrix RankOneAffinePhase

/-- The source's normalized rank-one annihilator exclusion and exact positivity.
The original Euclidean coefficient and full physical affine norms are retained.
The stop is the raw kappa inequality, with no additional same-P window. -/
theorem middle_cutoff_exact_positivity_stage {k : ℕ} (_hk : 2 ≤ k)
    (F : CoefficientSpace k) (ell : PhysicalAffineData)
    (κ : ℝ) (hκ : 0 < κ)
    (hstop : ∀ u : PhysicalSpace,
      κ ^ 2 * physicalEuclideanNorm u ^ 2 ≤
        coefficientEuclideanNorm (directionalCoefficientMap k u F) ^ 2 +
          physicalEuclideanNorm (ell.2 *ᵥ u) ^ 2)
    (b : PhysicalSpace) (N : Matrix (Fin 3) (Fin 3) ℝ)
    (hunit : affineFieldFrobenius b N = 1) :
    0 < max
      (coefficientEuclideanNorm (affineFieldCoefficientMap k b N F) +
        physicalAffineNorm (physicalAffineFieldAction ell b N))
      (descendingSingularValues (affineFieldMatrix b N) (1 : Fin 4)) := by
  by_contra hnot
  have hmax := le_of_not_gt hnot
  have hsum : coefficientEuclideanNorm (affineFieldCoefficientMap k b N F) +
      physicalAffineNorm (physicalAffineFieldAction ell b N) ≤ 0 :=
    (le_max_left _ _).trans hmax
  have hphase_nonneg : 0 ≤ coefficientEuclideanNorm
      (affineFieldCoefficientMap k b N F) := Real.sqrt_nonneg _
  have hphysical_nonneg := physicalAffineNorm_nonneg (physicalAffineFieldAction ell b N)
  have hphase_norm : coefficientEuclideanNorm (affineFieldCoefficientMap k b N F) = 0 := by
    linarith
  have hphysical_norm : physicalAffineNorm (physicalAffineFieldAction ell b N) = 0 := by
    linarith
  have hphase : affineFieldCoefficientMap k b N F = 0 := by
    apply (WithLp.linearEquiv 2 ℝ (CoefficientSpace k)).symm.injective
    rw [map_zero]
    exact norm_eq_zero.mp (by
      simpa only [coefficientEuclideanNorm_eq_norm] using hphase_norm)
  have hphysical : physicalAffineFieldAction ell b N = 0 :=
    (physicalAffineNorm_eq_zero_iff _).mp hphysical_norm
  have hσ : descendingSingularValues (affineFieldMatrix b N) (1 : Fin 4) = 0 :=
    le_antisymm ((le_max_right _ _).trans hmax) (descendingSingularValues_nonneg _ _)
  obtain ⟨u, hu, a, ha, hb, hN⟩ := normalized_factor_of_sigma2_zero b N hunit hσ
  exact stopped_rankone_action_ne_zero F ell κ hκ hstop b N u a hu ha hb hN
    ⟨hphase, hphysical⟩

end PaperI.RankOnePositivity
