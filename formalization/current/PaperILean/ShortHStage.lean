import PaperILean.PreparedPhysicalNorms
import PaperILean.SingularValueEuclideanBounds

/-! I3253[508,661): the short-H conclusion from the actual bounded physical window.
The original label is compared explicitly with the current physical singular value.
No quantitative conditioning, physical invertibility or rank hypothesis is assumed. -/
noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI.ShortHStage
open PreparedPhysicalNorms

theorem physical_euclidean_mul_norm_le_frobenius (B : Matrix (Fin 3) (Fin 3) ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    ‖Matrix.toEuclideanLin B x‖ ≤ physicalMatrixFrobenius B * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (physicalMatrixFrobenius_nonneg B) (norm_nonneg x))).mp
  simp only [mul_pow, physicalMatrixFrobenius_sq, PiLp.norm_sq_eq_of_L2,
    Real.norm_eq_abs, sq_abs, Matrix.piLp_equiv_toEuclideanLin_apply,
    Matrix.mulVec, dotProduct]
  calc
    (∑ i, (∑ j, B i j * x j) ^ 2) ≤
        ∑ i, (∑ j, B i j ^ 2) * (∑ j, x j ^ 2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (B i) x
    _ = _ := by rw [Finset.sum_mul]

theorem middle_singular_le_physicalFrobenius (B : Matrix (Fin 3) (Fin 3) ℝ) :
    descendingSingularValues B (1 : Fin 3) ≤ physicalMatrixFrobenius B := by
  obtain ⟨x, hx, hBx⟩ := descendingSingularValue_exists_unit_vector B (1 : Fin 3)
  simpa only [hx, hBx, mul_one] using physical_euclidean_mul_norm_le_frobenius B x

/-- The bounded actual augmented window supplies the original middle-label upper bound. -/
theorem original_middle_label_le_window_power {k : ℕ} (S : AugmentedState k)
    (P Cw Ccompare d₂ : ℝ) (hP : 0 < P)
    (hwindow : augmentedStateNorm S ≤ P ^ Cw)
    (hcompare : d₂ ≤ P ^ Ccompare * descendingSingularValues S.2.2 (1 : Fin 3)) :
    d₂ ≤ P ^ (Cw + Ccompare) := by
  have hsing : descendingSingularValues S.2.2 (1 : Fin 3) ≤ P ^ Cw :=
    (middle_singular_le_physicalFrobenius S.2.2).trans
      ((physical_matrix_le_affine S.2).trans ((physicalAffineNorm_le_augmented S).trans hwindow))
  calc
    d₂ ≤ P ^ Ccompare * P ^ Cw :=
      hcompare.trans (mul_le_mul_of_nonneg_left hsing (Real.rpow_nonneg hP.le _))
    _ = P ^ (Cw + Ccompare) := by rw [← Real.rpow_add hP, add_comm Ccompare Cw]

/-- Complete short-H manuscript stage. The actual window derives the upper bound
for the original d2; only the source polynomial short-H bound is retained. -/
theorem short_H_stage (k : ℕ) (_hk : 2 ≤ k) (S : AugmentedState k)
    (P H d₂ Ch Cw Ccompare : ℝ) (hP : 2 ≤ P) (_hH : 0 < H) (hd₂ : 0 < d₂)
    (hwindow : augmentedStateNorm S ≤ P ^ Cw)
    (hcompare : d₂ ≤ P ^ Ccompare * descendingSingularValues S.2.2 (1 : Fin 3))
    (hshort : H ≤ P ^ Ch) :
    H ≤ P ^ (Ch + Cw + Ccompare) / d₂ := by
  have hPpos : 0 < P := by linarith
  have hd := original_middle_label_le_window_power S P Cw Ccompare d₂ hPpos hwindow hcompare
  apply (le_div_iff₀ hd₂).mpr
  calc
    H * d₂ ≤ P ^ Ch * P ^ (Cw + Ccompare) :=
      mul_le_mul hshort hd hd₂.le (Real.rpow_nonneg hPpos.le _)
    _ = P ^ (Ch + Cw + Ccompare) := by rw [← Real.rpow_add hPpos, add_assoc]

end PaperI.ShortHStage
