import PaperILean.RotationOrientationPacking
import PaperILean.FrameEllipsoidQuotient

/-! I315: relative frame approximation after right orthogonal adjustment.
The final application explicitly retains the Gram representation hypothesis;
no general singular-value decomposition/ordering bridge is asserted here. -/
noncomputable section
open Set
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

def rotatedPositiveFrame (E : PositiveFrame) (O : rotationGroup3) : PositiveFrame :=
  ⟨rotationMatrix O * E.val, by
    rw [Matrix.det_mul, rotationMatrix_det, one_mul]
    exact E.property⟩

theorem rotatedPositiveFrame_inverse (E : PositiveFrame) (O : rotationGroup3) :
    (rotatedPositiveFrame E O).val⁻¹ = E.val⁻¹ * rotationMatrix O⁻¹ := by
  apply Matrix.inv_eq_right_inv
  change (rotationMatrix O * E.val) * (E.val⁻¹ * rotationMatrix O⁻¹) = 1
  calc
    (rotationMatrix O * E.val) * (E.val⁻¹ * rotationMatrix O⁻¹) =
        rotationMatrix O * (E.val * E.val⁻¹) * rotationMatrix O⁻¹ := by
      simp only [Matrix.mul_assoc]
    _ = rotationMatrix O * rotationMatrix O⁻¹ := by
      rw [Matrix.mul_nonsing_inv E.val (isUnit_iff_ne_zero.mpr E.property.ne'), Matrix.mul_one]
    _ = 1 := by rw [← rotationMatrix_mul, mul_inv_cancel, rotationMatrix_one]

theorem rotatedPositiveFrame_relative (E : PositiveFrame) (P O : rotationGroup3) :
    (rotatedPositiveFrame E P).val⁻¹ * (rotatedPositiveFrame E O).val =
      frameConjugate E (rotationMatrix (P⁻¹ * O)) := by
  rw [rotatedPositiveFrame_inverse, rotationMatrix_mul]
  simp only [rotatedPositiveFrame, frameConjugate, Matrix.mul_assoc]

theorem rotatedPositiveFrame_relative_error (E : PositiveFrame) (P O : rotationGroup3)
    (θ : ℝ) (h : P⁻¹ * O ∈ rotationNeighborhood E θ) :
    ‖(rotatedPositiveFrame E P).val⁻¹ * (rotatedPositiveFrame E O).val - 1‖ < θ := by
  rw [rotatedPositiveFrame_relative]
  exact (mem_rotationNeighborhood_iff E θ (P⁻¹ * O)).mp h

theorem rotatedPositiveFrame_sameGram_adjustment (E B : PositiveFrame)
    (P O : rotationGroup3) (θ : ℝ)
    (hgram : (rotatedPositiveFrame E O).val * (rotatedPositiveFrame E O).valᵀ = B.val * B.valᵀ)
    (h : P⁻¹ * O ∈ rotationNeighborhood E θ) :
    ∃ Q : Matrix (Fin 3) (Fin 3) ℝ, Q * Qᵀ = 1 ∧ Q.det = 1 ∧
      ‖(rotatedPositiveFrame E P).val⁻¹ * (B.val * Q) - 1‖ < θ := by
  obtain ⟨R, hR, hdet, hB⟩ := (same_gram_iff_right_specialOrthogonal
    (rotatedPositiveFrame E O) B).mp hgram
  refine ⟨Rᵀ, ?_, ?_, ?_⟩
  · simpa only [Matrix.transpose_transpose] using (Matrix.mul_eq_one_comm.mp hR)
  · simpa only [Matrix.det_transpose] using hdet
  · rw [hB, Matrix.mul_assoc, hR, Matrix.mul_one]
    exact rotatedPositiveFrame_relative_error E P O θ h

theorem rotationOrientationNet_gram_approximation :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i),
      e 0 ≤ e 1 → e 1 ≤ e 2 → ∀ θ : ℝ, 0 < θ → θ < 1/10 →
        ∃ s : Finset rotationGroup3,
          (s.card : ℝ) ≤ (C / θ^3) * (e 2 / e 0)^2 ∧
          (↑s : Set rotationGroup3).PairwiseDisjoint
            (rotationNeighborhoodTranslate (positiveDiagonalFrame e he) (θ/4)) ∧
          ∀ (B : PositiveFrame) (O : rotationGroup3),
            (rotatedPositiveFrame (positiveDiagonalFrame e he) O).val *
              (rotatedPositiveFrame (positiveDiagonalFrame e he) O).valᵀ = B.val * B.valᵀ →
            ∃ P ∈ s, ∃ Q : Matrix (Fin 3) (Fin 3) ℝ,
              Q * Qᵀ = 1 ∧ Q.det = 1 ∧
              ‖(rotatedPositiveFrame (positiveDiagonalFrame e he) P).val⁻¹ *
                (B.val * Q) - 1‖ < θ := by
  obtain ⟨C, hC, hnet⟩ := rotationOrientationNet_exists
  refine ⟨C, hC, ?_⟩
  intro e he h01 h12 θ hθ0 hθ
  obtain ⟨s, hs, hcard, hmax, hcover, hsep⟩ := hnet e he h01 h12 θ hθ0 hθ
  refine ⟨s, hcard, hs, ?_⟩
  intro B O hgram
  obtain ⟨P, hP, hPO⟩ := hcover O
  exact ⟨P, hP, rotatedPositiveFrame_sameGram_adjustment
    (positiveDiagonalFrame e he) B P O θ hgram hPO⟩

end PaperI
