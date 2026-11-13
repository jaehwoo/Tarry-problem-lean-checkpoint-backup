import PaperILean.AugmentedStateSpace
import PaperILean.AffineVectorFieldCoefficient
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! I595-607: the six-column augmented orbit differential. Its column order is
A,C,Tx,D,Ty,Tz. The phase component is differentiated before discarding its
constant; all physical affine coefficients are retained. No normal-column
rank or uniform quantitative singular-value estimate is assumed or proved. -/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

def augmentedOrbitDifferential (k : ℕ) (S : AugmentedState k) :
    (Fin 6 → ℝ) →ₗ[ℝ] AugmentedState k where
  toFun ξ :=
    (affineFieldCoefficientMap k (upperAffineFieldTranslation ξ) (upperAffineFieldLinear ξ) S.1,
     physicalAffineFieldAction S.2 (upperAffineFieldTranslation ξ) (upperAffineFieldLinear ξ))
  map_add' ξ ζ := by
    simp only [upperAffineFieldTranslation_add, upperAffineFieldLinear_add,
      affineFieldCoefficientMap_add_field, LinearMap.add_apply, physicalAffineFieldAction_add]
    rfl
  map_smul' r ξ := by
    simp only [upperAffineFieldTranslation_smul, upperAffineFieldLinear_smul,
      affineFieldCoefficientMap_smul_field, LinearMap.smul_apply, physicalAffineFieldAction_smul]
    rfl

theorem augmentedOrbit_phase {k : ℕ} (S : AugmentedState k)
    (ξ : Fin 6 → ℝ) (x : PhysicalSpace) :
    phase (augmentedOrbitDifferential k S ξ).1 x =
      fderiv ℝ (phase S.1) x
        (upperAffineFieldTranslation ξ + upperAffineFieldLinear ξ *ᵥ x) -
      fderiv ℝ (phase S.1) 0 (upperAffineFieldTranslation ξ) :=
  phase_affineFieldCoefficientMap _ _ _ _

theorem augmentedOrbit_physical {k : ℕ} (S : AugmentedState k)
    (ξ : Fin 6 → ℝ) (x : PhysicalSpace) :
    physicalAffineEval (augmentedOrbitDifferential k S ξ).2 x =
      fderiv ℝ (physicalAffineEval S.2) x
        (upperAffineFieldTranslation ξ + upperAffineFieldLinear ξ *ᵥ x) :=
  (fderiv_physicalAffineEval_field S.2 _ x _).symm

def augmentedOrbitMatrix (k : ℕ) (S : AugmentedState k) :
    Matrix (AugmentedCoordinateIndex k) (Fin 6) ℝ :=
  LinearMap.toMatrix' ((augmentedStateCoordinates k).toLinearMap.comp
    (augmentedOrbitDifferential k S))

theorem augmentedOrbitMatrix_column {k : ℕ} (S : AugmentedState k)
    (i : AugmentedCoordinateIndex k) (j : Fin 6) :
    augmentedOrbitMatrix k S i j =
      augmentedStateCoordinates k (augmentedOrbitDifferential k S (Pi.single j 1)) i := by
  rw [augmentedOrbitMatrix, LinearMap.toMatrix'_apply]
  have heq : (fun h : Fin 6 => if h = j then (1 : ℝ) else 0) = Pi.single j 1 := by
    funext h
    simp [Pi.single_apply, eq_comm]
  rw [heq]
  rfl

theorem augmentedOrbitMatrix_mulVec {k : ℕ} (S : AugmentedState k) (ξ : Fin 6 → ℝ) :
    augmentedOrbitMatrix k S *ᵥ ξ =
      augmentedStateCoordinates k (augmentedOrbitDifferential k S ξ) := by
  exact congrArg (fun f : (Fin 6 → ℝ) →ₗ[ℝ] (AugmentedCoordinateIndex k → ℝ) => f ξ)
    (Matrix.toLin'_toMatrix' ((augmentedStateCoordinates k).toLinearMap.comp
      (augmentedOrbitDifferential k S)))

theorem augmentedOrbitMatrix_norm {k : ℕ} (S : AugmentedState k) (ξ : Fin 6 → ℝ) :
    coordinateL2Norm (augmentedOrbitMatrix k S *ᵥ ξ) =
      augmentedStateNorm (augmentedOrbitDifferential k S ξ) := by
  rw [augmentedOrbitMatrix_mulVec]
  rfl

/-- Translation coordinates in the source's fixed six-generator ordering. -/
def upperAffineTranslationCoordinates : PhysicalSpace →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun h := ![0, 0, h 0, 0, h 1, h 2]
  map_add' h g := by ext i; fin_cases i <;> simp
  map_smul' r h := by ext i; fin_cases i <;> simp

theorem upperAffineFieldTranslation_translationCoordinates (h : PhysicalSpace) :
    upperAffineFieldTranslation (upperAffineTranslationCoordinates h) = h := by
  ext i; fin_cases i <;> rfl

theorem upperAffineFieldLinear_translationCoordinates (h : PhysicalSpace) :
    upperAffineFieldLinear (upperAffineTranslationCoordinates h) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem augmentedOrbit_translation {k : ℕ} (S : AugmentedState k) (h : PhysicalSpace) :
    augmentedOrbitDifferential k S (upperAffineTranslationCoordinates h) =
      (directionalCoefficientMap k h S.1, (S.2.2 *ᵥ h, 0)) := by
  simp only [augmentedOrbitDifferential, LinearMap.coe_mk, AddHom.coe_mk,
    upperAffineFieldTranslation_translationCoordinates, upperAffineFieldLinear_translationCoordinates,
    affineFieldCoefficientMap_translation, physicalAffineFieldAction_translation]

theorem augmentedOrbit_translation_norm_sq {k : ℕ} (S : AugmentedState k)
    (h : PhysicalSpace) :
    augmentedStateNorm (augmentedOrbitDifferential k S (upperAffineTranslationCoordinates h)) ^ 2 =
      coefficientEuclideanNorm (directionalCoefficientMap k h S.1) ^ 2 +
        physicalEuclideanNorm (S.2.2 *ᵥ h) ^ 2 := by
  rw [augmentedOrbit_translation, augmentedStateNorm_sq]
  simp only [physicalEuclideanNorm, coordinateL2Norm_sq]
  simp

theorem augmentedTranslationStopped_iff_orbit {k : ℕ} (P : ℝ) (S : AugmentedState k) :
    AugmentedTranslationStopped P S ↔ augmentedStateNorm S ≤ P ∧
      ∀ h : PhysicalSpace, P ^ (-2 : ℤ) * physicalEuclideanNorm h ^ 2 ≤
        augmentedStateNorm (augmentedOrbitDifferential k S (upperAffineTranslationCoordinates h)) ^ 2 := by
  simp only [AugmentedTranslationStopped, augmentedOrbit_translation_norm_sq]

theorem augmentedOrbit_normalized_translation_norm_sq {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (h : PhysicalSpace) :
    augmentedStateNorm (augmentedOrbitDifferential k
      (affineCoefficientMap k c B F, (c, B)) (upperAffineTranslationCoordinates h)) ^ 2 =
        augmentedTranslationQuadratic F c B h :=
  augmentedOrbit_translation_norm_sq _ _

/-- The source translation stop excludes nonzero constant translation fields
from the augmented kernel. It does not imply the full map is injective. -/
theorem augmentedOrbit_translation_eq_zero {k : ℕ} {P : ℝ} (hP : 0 < P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S)
    (h : PhysicalSpace)
    (hz : augmentedOrbitDifferential k S (upperAffineTranslationCoordinates h) = 0) : h = 0 := by
  have hbound := ((augmentedTranslationStopped_iff_orbit P S).mp hstop).2 h
  have hn : augmentedStateNorm (0 : AugmentedState k) = 0 :=
    (augmentedStateNorm_eq_zero_iff _).mpr rfl
  rw [hz, hn] at hbound
  have hc : 0 < P ^ (-2 : ℤ) := zpow_pos hP _
  have hs : physicalEuclideanNorm h ^ 2 ≤ 0 := by
    apply (mul_le_mul_left hc).mp
    simpa using hbound
  have he : physicalEuclideanNorm h = 0 := by
    nlinarith [physicalEuclideanNorm_nonneg h]
  change coordinateL2Norm h = 0 at he
  rw [coordinateL2Norm_eq_norm, norm_eq_zero] at he
  apply (WithLp.linearEquiv 2 ℝ (PhysicalSpace)).symm.injective
  simpa only [map_zero] using he

theorem augmentedOrbit_translation_injective {k : ℕ} {P : ℝ} (hP : 0 < P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S) :
    Function.Injective ((augmentedOrbitDifferential k S).comp upperAffineTranslationCoordinates) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro h hh
  exact augmentedOrbit_translation_eq_zero hP S hstop h hh

end PaperI
