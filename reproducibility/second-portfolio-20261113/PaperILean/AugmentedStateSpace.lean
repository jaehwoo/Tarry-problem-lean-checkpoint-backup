import PaperILean.AugmentedPhysicalAffine
import PaperILean.TranslationStopStability

/-! I595-607: the exact augmented state, with all physical affine coefficients.
The norm is explicitly Euclidean; the ambient product norm is not used.
Physical coefficients remain parameters and are not coefficient integration variables. -/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

abbrev AugmentedState (k : ℕ) := CoefficientSpace k × PhysicalAffineData
abbrev AugmentedCoordinateIndex (k : ℕ) :=
  MonomialIndex k ⊕ (Fin 3 ⊕ (Fin 3 × Fin 3))

def augmentedStateCoordinates (k : ℕ) :
    AugmentedState k ≃ₗ[ℝ] (AugmentedCoordinateIndex k → ℝ) where
  toFun S := Sum.elim S.1 (Sum.elim S.2.1 (fun ij => S.2.2 ij.1 ij.2))
  invFun v := (fun α => v (.inl α), (fun i => v (.inr (.inl i)),
    fun i j => v (.inr (.inr (i, j)))))
  left_inv S := by rfl
  right_inv v := by funext a; rcases a with a | (i | ij) <;> rfl
  map_add' S T := by funext a; rcases a with a | (i | ij) <;> rfl
  map_smul' r S := by funext a; rcases a with a | (i | ij) <;> rfl

def augmentedStateNorm {k : ℕ} (S : AugmentedState k) : ℝ :=
  coordinateL2Norm (augmentedStateCoordinates k S)

theorem augmentedStateNorm_nonneg {k : ℕ} (S : AugmentedState k) :
    0 ≤ augmentedStateNorm S := coordinateL2Norm_nonneg _

theorem augmentedStateNorm_sq {k : ℕ} (S : AugmentedState k) :
    augmentedStateNorm S ^ 2 = coefficientEuclideanNorm S.1 ^ 2 +
      (∑ i, S.2.1 i ^ 2) + ∑ i, ∑ j, S.2.2 i j ^ 2 := by
  rw [augmentedStateNorm, coordinateL2Norm_sq]
  simp only [Fintype.sum_sum_type, augmentedStateCoordinates, LinearEquiv.coe_mk,
    Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type]
  rw [coefficientEuclideanNorm, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  ring

theorem augmentedStateNorm_sq_eq {k : ℕ} (S : AugmentedState k) :
    augmentedStateNorm S ^ 2 = coefficientEuclideanNorm S.1 ^ 2 +
      physicalAffineNorm S.2 ^ 2 := by
  rw [augmentedStateNorm_sq, physicalAffineNorm_sq]
  ring

theorem augmentedStateNorm_eq_zero_iff {k : ℕ} (S : AugmentedState k) :
    augmentedStateNorm S = 0 ↔ S = 0 := by
  rw [augmentedStateNorm, coordinateL2Norm_eq_norm, norm_eq_zero]
  constructor
  · intro h
    apply (augmentedStateCoordinates k).injective
    apply (WithLp.linearEquiv 2 ℝ (AugmentedCoordinateIndex k → ℝ)).symm.injective
    simpa only [map_zero] using h
  · rintro rfl
    simp

theorem augmentedStateNorm_add_le {k : ℕ} (S T : AugmentedState k) :
    augmentedStateNorm (S + T) ≤ augmentedStateNorm S + augmentedStateNorm T := by
  simp only [augmentedStateNorm, coordinateL2Norm_eq_norm, map_add]
  exact norm_add_le _ _

theorem augmentedStateNorm_smul {k : ℕ} (r : ℝ) (S : AugmentedState k) :
    augmentedStateNorm (r • S) = |r| * augmentedStateNorm S := by
  simp only [augmentedStateNorm, map_smul]
  exact coordinateL2Norm_smul r _

/-- The exact source coefficient window and augmented translation inequality.
The global manuscript convention P>=2 is supplied when using this condition. -/
def AugmentedTranslationStopped {k : ℕ} (P : ℝ) (S : AugmentedState k) : Prop :=
  augmentedStateNorm S ≤ P ∧ ∀ h : PhysicalSpace,
    P ^ (-2 : ℤ) * physicalEuclideanNorm h ^ 2 ≤
      coefficientEuclideanNorm (directionalCoefficientMap k h S.1) ^ 2 +
        physicalEuclideanNorm (S.2.2 *ᵥ h) ^ 2

end PaperI
