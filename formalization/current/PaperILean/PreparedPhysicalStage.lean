import PaperILean.RegularSectionDifferential
import PaperILean.PreparedPhysicalNorms

/-! I3253[104,243): actual original physical derivatives and their product bound.
The preparation estimate is imposed on the derivative of the actual augmented path.
The body-coordinate formula and both physical derivative identities are conclusions. -/

noncomputable section
open Matrix
namespace PaperI.PreparedPhysicalStage
open RegularSectionDifferential PreparedPhysicalNorms MiddleSingularNorm RankOneAffineMatrix

noncomputable local instance : NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedAddCommGroup
noncomputable local instance : NormedSpace ℝ (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedSpace

/-- The derivative of the actual augmented path equals its original body action. -/
theorem augmented_deriv_eq_body {k : ℕ} (S0 : AugmentedState k)
    (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ) (hg : HasDerivAt g v t) :
    deriv (fun u => augmentedPullback S0 (g u)) t =
      augmentedOrbitDifferential k (augmentedPullback S0 (g t))
        (originalAffineBodyCoordinates (g t) v) :=
  (augmentedPullback_hasDerivAt_body S0 g v t hg).deriv

/-- The original physical translation derivative is the current matrix times the body translation. -/
theorem physical_translation_hasDerivAt_body {k : ℕ} (S0 : AugmentedState k)
    (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ) (hg : HasDerivAt g v t) :
    HasDerivAt (fun u => (augmentedPullback S0 (g u)).2.1)
      ((augmentedPullback S0 (g t)).2.2 *ᵥ
        upperAffineFieldTranslation (originalAffineBodyCoordinates (g t) v)) t :=
  (augmentedPullback_hasDerivAt_body S0 g v t hg).snd.fst

/-- The original physical linear derivative is the current matrix times the body linear field. -/
theorem physical_linear_hasDerivAt_body {k : ℕ} (S0 : AugmentedState k)
    (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ) (hg : HasDerivAt g v t) :
    HasDerivAt (fun u => (augmentedPullback S0 (g u)).2.2)
      ((augmentedPullback S0 (g t)).2.2 *
        upperAffineFieldLinear (originalAffineBodyCoordinates (g t) v)) t :=
  (augmentedPullback_hasDerivAt_body S0 g v t hg).snd.snd

/-- Complete local physical derivative and product-estimate stage from the actual
prepared augmented derivative. No physical invertibility or conditioning is assumed. -/
theorem prepared_physical_product_stage (k : ℕ) (_hk : 2 ≤ k)
    (S0 : AugmentedState k) (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ)
    (hg : HasDerivAt g v t) (P H Ca : ℝ) (hP : 2 ≤ P) (hH : 0 < H)
    (hprepared : augmentedStateNorm (deriv (fun u => augmentedPullback S0 (g u)) t) ≤
      P ^ Ca / H) :
    let S := augmentedPullback S0 (g t)
    let ξ := originalAffineBodyCoordinates (g t) v
    HasDerivAt (fun u => (augmentedPullback S0 (g u)).2.1)
        (S.2.2 *ᵥ upperAffineFieldTranslation ξ) t ∧
      HasDerivAt (fun u => (augmentedPullback S0 (g u)).2.2)
        (S.2.2 * upperAffineFieldLinear ξ) t ∧
      physicalMatrixFrobenius (S.2.2 * upperAffineFieldLinear ξ) +
        physicalEuclideanNorm (S.2.2 *ᵥ upperAffineFieldTranslation ξ) ≤
          P ^ (Ca + 1) / H ∧
      matrixFrobenius (S.2.2 * affineFieldMatrix (upperAffineFieldTranslation ξ)
        (upperAffineFieldLinear ξ)) ≤ P ^ Ca / H := by
  have hPpos : 0 < P := by linarith
  have hact : augmentedStateNorm
      (augmentedOrbitDifferential k (augmentedPullback S0 (g t))
        (originalAffineBodyCoordinates (g t) v)) ≤ P ^ Ca / H := by
    simpa only [augmented_deriv_eq_body S0 g v t hg] using hprepared
  dsimp only
  refine ⟨physical_translation_hasDerivAt_body S0 g v t hg,
    physical_linear_hasDerivAt_body S0 g v t hg, ?_, ?_⟩
  · calc
      _ ≤ 2 * augmentedStateNorm
          (augmentedOrbitDifferential k (augmentedPullback S0 (g t))
            (originalAffineBodyCoordinates (g t) v)) :=
        physical_blocks_sum_le_augmented _
      _ ≤ 2 * (P ^ Ca / H) := mul_le_mul_of_nonneg_left hact (by norm_num)
      _ = (2 * P ^ Ca) / H := (mul_div_assoc _ _ _).symm
      _ ≤ (P ^ Ca * P) / H := by
        apply div_le_div_of_nonneg_right _ hH.le
        nlinarith [Real.rpow_nonneg hPpos.le Ca]
      _ = P ^ (Ca + 1) / H := by rw [Real.rpow_add hPpos, Real.rpow_one]
  · rw [matrixFrobenius_mul_affine]
    exact (physicalAffineNorm_le_augmented
      (augmentedOrbitDifferential k (augmentedPullback S0 (g t))
        (originalAffineBodyCoordinates (g t) v))).trans hact

end PaperI.PreparedPhysicalStage
