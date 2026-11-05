import PaperILean.PreparedPhysicalStage
import PaperILean.MiddleSingularStage
import PaperILean.RegularSectionDifferential

/-! Normalization support for I3253. Quantitative conditioning is retained as an
explicit premise in the later H-bound application, never inferred from the action. -/
noncomputable section
open Matrix
namespace PaperI.PreparedBodyNormalization
open PreparedPhysicalNorms MiddleSingularNorm RankOneAffineMatrix

def normalizedBody (ξ : Fin 6 → ℝ) : Fin 6 → ℝ :=
  (coordinateL2Norm ξ)⁻¹ • ξ

theorem inverse_body_norm_le (ξ : Fin 6 → ℝ) (P Cb : ℝ)
    (hP : 0 < P) (hbody : P ^ (-Cb) ≤ coordinateL2Norm ξ) :
    0 < coordinateL2Norm ξ ∧ (coordinateL2Norm ξ)⁻¹ ≤ P ^ Cb := by
  have hq : 0 < coordinateL2Norm ξ := (Real.rpow_pos_of_pos hP _).trans_le hbody
  refine ⟨hq, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hbody (Real.rpow_nonneg hP.le Cb)
  have he : P ^ Cb * P ^ (-Cb) = 1 := by
    rw [← Real.rpow_add hP]
    simp
  rw [he] at hm
  exact (inv_le_iff_one_le_mul₀ hq).mpr hm

theorem normalized_body_matrix_norm (ξ : Fin 6 → ℝ)
    (hξ : 0 < coordinateL2Norm ξ) :
    matrixFrobenius (affineFieldMatrix (upperAffineFieldTranslation (normalizedBody ξ))
      (upperAffineFieldLinear (normalizedBody ξ))) = 1 := by
  rw [normalizedBody, upperAffineFieldTranslation_smul, upperAffineFieldLinear_smul,
    affineFieldMatrix_smul, matrixFrobenius_smul, upperAffineFieldMatrix_norm,
    abs_of_nonneg (inv_nonneg.mpr hξ.le), inv_mul_cancel₀ hξ.ne']

theorem normalized_action_and_product_bound {k : ℕ} (S : AugmentedState k)
    (ξ : Fin 6 → ℝ) (P H Ca Cb : ℝ) (hP : 0 < P) (hH : 0 < H)
    (hbody : P ^ (-Cb) ≤ coordinateL2Norm ξ)
    (haction : augmentedStateNorm (augmentedOrbitDifferential k S ξ) ≤ P ^ Ca / H) :
    matrixFrobenius (affineFieldMatrix (upperAffineFieldTranslation (normalizedBody ξ))
      (upperAffineFieldLinear (normalizedBody ξ))) = 1 ∧
    augmentedStateNorm (augmentedOrbitDifferential k S (normalizedBody ξ)) ≤
      P ^ (Ca + Cb) / H ∧
    matrixFrobenius (S.2.2 * affineFieldMatrix
      (upperAffineFieldTranslation (normalizedBody ξ))
      (upperAffineFieldLinear (normalizedBody ξ))) ≤ P ^ (Ca + Cb) / H := by
  obtain ⟨hq, hi⟩ := inverse_body_norm_le ξ P Cb hP hbody
  have hscale : augmentedStateNorm (augmentedOrbitDifferential k S (normalizedBody ξ)) =
      (coordinateL2Norm ξ)⁻¹ * augmentedStateNorm (augmentedOrbitDifferential k S ξ) := by
    rw [normalizedBody, map_smul, augmentedStateNorm_smul,
      abs_of_nonneg (inv_nonneg.mpr hq.le)]
  have hbound : augmentedStateNorm (augmentedOrbitDifferential k S (normalizedBody ξ)) ≤
      P ^ (Ca + Cb) / H := by
    rw [hscale]
    calc
      _ ≤ (coordinateL2Norm ξ)⁻¹ * (P ^ Ca / H) :=
        mul_le_mul_of_nonneg_left haction (inv_nonneg.mpr hq.le)
      _ ≤ P ^ Cb * (P ^ Ca / H) :=
        mul_le_mul_of_nonneg_right hi (div_nonneg (Real.rpow_nonneg hP.le _) hH.le)
      _ = P ^ (Ca + Cb) / H := by
        rw [← mul_div_assoc, mul_comm (P ^ Cb), ← Real.rpow_add hP]
  refine ⟨normalized_body_matrix_norm ξ hq, hbound, ?_⟩
  calc
    _ = physicalAffineNorm (augmentedOrbitDifferential k S (normalizedBody ξ)).2 :=
      matrixFrobenius_mul_affine S.2 _ _
    _ ≤ augmentedStateNorm (augmentedOrbitDifferential k S (normalizedBody ξ)) :=
      physicalAffineNorm_le_augmented _
    _ ≤ _ := hbound

noncomputable local instance : NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedAddCommGroup
noncomputable local instance : NormedSpace ℝ (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedSpace

open RegularSectionDifferential PreparedPhysicalStage

/-- Normalize the actual original body field using only the source lower body bound.
The preparation estimate concerns the actual path derivative, not an assumed action. -/
theorem actual_normalized_body_estimates (k : ℕ) (_hk : 2 ≤ k)
    (S0 : AugmentedState k) (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ)
    (hg : HasDerivAt g v t) (P H Ca Cb : ℝ) (hP : 2 ≤ P) (hH : 0 < H)
    (hbody : P ^ (-Cb) ≤ coordinateL2Norm (originalAffineBodyCoordinates (g t) v))
    (hprepared : augmentedStateNorm (deriv (fun u => augmentedPullback S0 (g u)) t) ≤
      P ^ Ca / H) :
    let S := augmentedPullback S0 (g t)
    let η := normalizedBody (originalAffineBodyCoordinates (g t) v)
    matrixFrobenius (affineFieldMatrix (upperAffineFieldTranslation η)
      (upperAffineFieldLinear η)) = 1 ∧
    augmentedStateNorm (augmentedOrbitDifferential k S η) ≤ P ^ (Ca + Cb) / H ∧
    matrixFrobenius (S.2.2 * affineFieldMatrix (upperAffineFieldTranslation η)
      (upperAffineFieldLinear η)) ≤ P ^ (Ca + Cb) / H := by
  apply normalized_action_and_product_bound _ _ P H Ca Cb (by linarith) hH hbody
  simpa only [augmented_deriv_eq_body S0 g v t hg] using hprepared

/-- Conditional H bound for the actual prepared path. Only the quantitative
normalized singular-value lower bound is additionally required; it is not proved here. -/
theorem H_bound_of_normalized_conditioning (k : ℕ) (hk : 2 ≤ k)
    (S0 : AugmentedState k) (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ)
    (hg : HasDerivAt g v t) (P H d₂ Ca Cb Ccond Ccompare : ℝ)
    (hP : 2 ≤ P) (hH : 0 < H) (hd₂ : 0 < d₂)
    (hbody : P ^ (-Cb) ≤ coordinateL2Norm (originalAffineBodyCoordinates (g t) v))
    (hprepared : augmentedStateNorm (deriv (fun u => augmentedPullback S0 (g u)) t) ≤
      P ^ Ca / H)
    (hσ : P ^ (-Ccond) ≤ descendingSingularValues
      (affineFieldMatrix
        (upperAffineFieldTranslation (normalizedBody (originalAffineBodyCoordinates (g t) v)))
        (upperAffineFieldLinear (normalizedBody (originalAffineBodyCoordinates (g t) v))))
      (1 : Fin 4))
    (hcompare : d₂ ≤ P ^ Ccompare *
      descendingSingularValues (augmentedPullback S0 (g t)).2.2 (1 : Fin 3)) :
    H ≤ P ^ (Ccond + Ca + Cb + Ccompare) / d₂ := by
  have he := actual_normalized_body_estimates k hk S0 g v t hg P H Ca Cb
    hP hH hbody hprepared
  have hb := MiddleSingularStage.H_bound_of_prepared_estimates k hk
    (augmentedPullback S0 (g t)).2
    (upperAffineFieldTranslation (normalizedBody (originalAffineBodyCoordinates (g t) v)))
    (upperAffineFieldLinear (normalizedBody (originalAffineBodyCoordinates (g t) v)))
    P H d₂ Ccond (Ca + Cb) Ccompare hP hH hd₂ hσ he.2.2 hcompare
  simpa only [add_assoc] using hb

end PaperI.PreparedBodyNormalization
