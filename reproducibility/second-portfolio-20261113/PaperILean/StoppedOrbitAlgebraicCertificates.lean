import PaperILean.GramCertificatePolynomials
import PaperILean.StoppedOrbitSingularValues

/-! I595--607 and I668--694: exact graph certificates for the actual
normal least and full fourth values, and the unchanged all-h stop with
square roots and negative powers removed. The source range P >= 2 is kept. -/

noncomputable section
open scoped Matrix BigOperators
namespace PaperI

theorem normalOrbit_least_graph_certificate (k : ℕ) (S : AugmentedState k) (t : ℝ) :
    t = normalOrbitSingularValues k S 2 ↔
      ∃ s : Fin 3 → ℝ, OrderedGramCertificate (normalOrbitMatrix k S) s ∧ s 2 = t :=
  descendingSingularValue_graph_iff _ _ _

theorem augmentedOrbit_fourth_graph_certificate (k : ℕ) (S : AugmentedState k) (t : ℝ) :
    t = augmentedOrbitSingularValues k S 3 ↔
      ∃ s : Fin 6 → ℝ, OrderedGramCertificate (augmentedOrbitMatrix k S) s ∧ s 3 = t :=
  descendingSingularValue_graph_iff _ _ _

theorem augmentedStateNorm_le_iff_squared_coordinates {k : ℕ} {P : ℝ}
    (hP : 0 ≤ P) (S : AugmentedState k) :
    augmentedStateNorm S ≤ P ↔
      (∑ r, (augmentedStateCoordinates k S r) ^ 2) ≤ P ^ 2 := by
  rw [← coordinateL2Norm_sq]
  exact (sq_le_sq₀ (augmentedStateNorm_nonneg S) hP).symm

/-- Exact finite-coordinate stop; the universal physical direction is retained. -/
def SquaredAugmentedStop {k : ℕ} (P : ℝ) (S : AugmentedState k) : Prop :=
  (∑ r, (augmentedStateCoordinates k S r) ^ 2) ≤ P ^ 2 ∧
    ∀ h : PhysicalSpace, (∑ i, h i ^ 2) ≤
      P ^ 2 * ∑ r, ((augmentedOrbitMatrix k S *ᵥ upperAffineTranslationCoordinates h) r) ^ 2

theorem augmentedTranslationStopped_iff_squared {k : ℕ} {P : ℝ}
    (hP : 2 ≤ P) (S : AugmentedState k) :
    AugmentedTranslationStopped P S ↔ SquaredAugmentedStop P S := by
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  rw [augmentedTranslationStopped_iff_orbit, SquaredAugmentedStop,
    augmentedStateNorm_le_iff_squared_coordinates hPpos.le S]
  apply and_congr_right
  intro hwindow
  apply forall_congr'
  intro h
  rw [← augmentedOrbitMatrix_norm]
  simp only [physicalEuclideanNorm, coordinateL2Norm_sq]
  have hinv : P ^ (-2 : ℤ) = (P ^ 2)⁻¹ := by
    simp only [zpow_neg, zpow_ofNat]
  rw [hinv, inv_mul_le_iff₀ (sq_pos_of_pos hPpos)]

theorem stopped_normal_least_joint_certificate (k : ℕ) (P : ℝ)
    (S : AugmentedState k) (t : ℝ) :
    (2 ≤ P ∧ AugmentedTranslationStopped P S ∧ t = normalOrbitSingularValues k S 2) ↔
      2 ≤ P ∧ SquaredAugmentedStop P S ∧
        ∃ s : Fin 3 → ℝ, OrderedGramCertificate (normalOrbitMatrix k S) s ∧ s 2 = t := by
  by_cases hP : 2 ≤ P
  · rw [augmentedTranslationStopped_iff_squared hP, normalOrbit_least_graph_certificate]
  · simp [hP]

theorem stopped_augmented_fourth_joint_certificate (k : ℕ) (P : ℝ)
    (S : AugmentedState k) (t : ℝ) :
    (2 ≤ P ∧ AugmentedTranslationStopped P S ∧ t = augmentedOrbitSingularValues k S 3) ↔
      2 ≤ P ∧ SquaredAugmentedStop P S ∧
        ∃ s : Fin 6 → ℝ, OrderedGramCertificate (augmentedOrbitMatrix k S) s ∧ s 3 = t := by
  by_cases hP : 2 ≤ P
  · rw [augmentedTranslationStopped_iff_squared hP, augmentedOrbit_fourth_graph_certificate]
  · simp [hP]

end PaperI
