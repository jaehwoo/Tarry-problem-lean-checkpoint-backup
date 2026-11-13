import PaperILean.FrameSingularDecomposition

/-! I311-315,331: the orientation net for every positive frame with prescribed
singular values. The Gram premise from checkpoint40 is discharged here.
The same finite family is chosen before every target frame and retains the
relative separation needed in I333. No local affine packing count is claimed. -/
noncomputable section
open Set
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

theorem rotatedPositiveFrame_relative_error_eq_conjugate
    (E : PositiveFrame) (O P : rotationGroup3) :
    (rotatedPositiveFrame E O).val⁻¹ * (rotatedPositiveFrame E P).val - 1 =
      frameConjugate E (rotationMatrix (O⁻¹ * P) - 1) := by
  rw [rotatedPositiveFrame_relative, frameConjugate_sub, frameConjugate_one]

theorem rotationOrientationNet_singular_approximation :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i),
      e 0 ≤ e 1 → e 1 ≤ e 2 → ∀ θ : ℝ, 0 < θ → θ < 1/10 →
        ∃ s : Finset rotationGroup3,
          (s.card : ℝ) ≤ (C / θ^3) * (e 2 / e 0)^2 ∧
          (↑s : Set rotationGroup3).PairwiseDisjoint
            (rotationNeighborhoodTranslate (positiveDiagonalFrame e he) (θ/4)) ∧
          (∀ O ∈ s, ∀ P ∈ s, O ≠ P →
            θ/4 ≤ ‖(rotatedPositiveFrame (positiveDiagonalFrame e he) O).val⁻¹ *
              (rotatedPositiveFrame (positiveDiagonalFrame e he) P).val - 1‖) ∧
          ∀ B : PositiveFrame, HasFrameSingularValues B e →
            ∃ P ∈ s, ∃ Q : Matrix (Fin 3) (Fin 3) ℝ,
              Q * Qᵀ = 1 ∧ Q.det = 1 ∧
              ‖(rotatedPositiveFrame (positiveDiagonalFrame e he) P).val⁻¹ *
                (B.val * Q) - 1‖ < θ := by
  obtain ⟨C, hC, hnet⟩ := rotationOrientationNet_exists
  refine ⟨C, hC, ?_⟩
  intro e he h01 h12 θ hθ0 hθ
  obtain ⟨s, hs, hcard, _, hcover, hsep⟩ := hnet e he h01 h12 θ hθ0 hθ
  refine ⟨s, hcard, hs, ?_, ?_⟩
  · intro O hO P hP hne
    rw [rotatedPositiveFrame_relative_error_eq_conjugate]
    exact hsep O hO P hP hne
  · intro B hB
    obtain ⟨O, hgram⟩ := frame_singular_gram_representation B e he hB
    obtain ⟨P, hP, hPO⟩ := hcover O
    exact ⟨P, hP, rotatedPositiveFrame_sameGram_adjustment
      (positiveDiagonalFrame e he) B P O θ hgram hPO⟩

end PaperI
