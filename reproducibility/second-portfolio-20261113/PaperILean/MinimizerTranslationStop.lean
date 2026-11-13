import PaperILean.MinimizerSpectralBounds
import PaperILean.TranslationGramBound
import PaperILean.TranslationRightFrameStability

/-! Actual-minimum augmented stopping, I239-241 and I261-265.
The constant is chosen before F,c,lambda,B,u, not after a minimum is selected.
The center-translation corollary retains the still-unproved uniform jet window
as an explicit input; the unshifted stopping theorem does not need that input. -/
noncomputable section
open scoped BigOperators Matrix
namespace PaperI

theorem real_matrix_sum_quadratic {n : ℕ} (s : Finset ℕ)
    (G : ℕ → Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    dotProduct u ((∑ r ∈ s, G r) *ᵥ u) = ∑ r ∈ s, dotProduct u (G r *ᵥ u) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert r s hr ih => simp only [Finset.sum_insert hr, Matrix.add_mulVec, dotProduct_add, ih]

theorem weightedJetContractionGram_quadratic {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (u : PhysicalSpace) :
    dotProduct u (weightedJetContractionGram F c B *ᵥ u) =
      translationWeightedContractionSum F c B u := by
  rw [weightedJetContractionGram, real_matrix_sum_quadratic,
    translationWeightedContractionSum_eq_Icc]
  apply Finset.sum_congr rfl
  intro r hr
  have hh := (Finset.mem_Icc.mp hr).1
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  rw [show n + 2 - 2 = n by omega]
  simp only [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul,
    Nat.add_sub_cancel, directionalContractionHSNorm]
  rw [jetContractionGram_quadratic (n := n + 1)]

theorem minimizing_gram_quadratic_dominance {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val)
    (u : PhysicalSpace) : (physicalEuclideanNorm u) ^ 2 ≤
      (physicalEuclideanNorm (B.val *ᵥ u)) ^ 2 + translationWeightedContractionSum F c B.val u := by
  have h := (minimizing_gram_dominance F c lam hlam B hB).2 u
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_add, rightGram_quadratic,
    weightedJetContractionGram_quadratic, ← physicalEuclideanNorm_sq_eq_dotProduct] at h
  linarith

theorem augmentedTranslation_lower_bound_of_minimum (k : ℕ) (hk : 2 ≤ k) :
    ∃ b : ℝ, 0 < b ∧ ∀ (F : CoefficientSpace k) (c : PhysicalSpace)
      (lam : ℝ), 0 ≤ lam → ∀ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) →
      ∀ u : PhysicalSpace, b * (physicalEuclideanNorm u) ^ 2 ≤
        augmentedTranslationQuadratic F c B.val u := by
  obtain ⟨b, hb, hs⟩ := augmentedTranslation_lower_bound_of_gram_dominance k hk
  refine ⟨b, hb, ?_⟩
  intro F c lam hlam B hB
  exact hs F c B.val (minimizing_gram_quadratic_dominance F c lam hlam B hB)

theorem source_augmentedTranslation_lower_bound_of_minimum (k : ℕ) (hk : 2 ≤ k) :
    ∃ b : ℝ, 0 < b ∧ ∀ (CX C0 R : ℝ), 2 ≤ CX → 2 ≤ C0 → 2 ≤ R →
      ∀ (F : CoefficientSpace k) (c : PhysicalSpace) (B : PositiveFrame),
      (∀ D : PositiveFrame, FrameEnergy F c (sourceRegularization CX C0 R) B.val ≤
        FrameEnergy F c (sourceRegularization CX C0 R) D.val) →
      ∀ u : PhysicalSpace, b * (physicalEuclideanNorm u) ^ 2 ≤
        augmentedTranslationQuadratic F c B.val u := by
  obtain ⟨b, hb, hs⟩ := augmentedTranslation_lower_bound_of_minimum k hk
  exact ⟨b, hb, fun CX C0 R hCX hC0 hR F c B hB =>
    hs F c _ (sourceRegularization_pos CX C0 R hCX hC0 hR).le B hB⟩

theorem minimizing_translationStop_bounded_right_frame (k : ℕ) (hk : 2 ≤ k)
    (L : ℝ) (hL : 1 ≤ L) :
    ∃ b : ℝ, 0 < b ∧ ∀ (F : CoefficientSpace k) (c : PhysicalSpace)
      (lam : ℝ), 0 ≤ lam → ∀ (B : PositiveFrame) (A : Matrix (Fin 3) (Fin 3) ℝ),
      (∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) →
      A.det ≠ 0 → euclideanFrameOperatorNorm A ≤ L → euclideanFrameOperatorNorm A⁻¹ ≤ L →
      ∀ u : PhysicalSpace, b * (physicalEuclideanNorm u) ^ 2 ≤
        augmentedTranslationQuadratic F c (B.val * A) u := by
  obtain ⟨a, ha, hs⟩ := augmentedTranslation_lower_bound_of_minimum k hk
  obtain ⟨b, hb, hright⟩ := translationStop_bounded_right_frame k hk L a hL ha
  refine ⟨b, hb, ?_⟩
  intro F c lam hlam B A hB hA hForward hInv
  exact hright F c B.val A hA hForward hInv (hs F c lam hlam B hB)

theorem minimizing_translationStop_uniform_radius_of_window (k : ℕ) (hk : 2 ≤ k) :
    ∃ b : ℝ, 0 < b ∧ ∀ M : ℝ, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (F : CoefficientSpace k) (c : PhysicalSpace) (lam : ℝ), 0 ≤ lam →
      ∀ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) →
      (∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B.val r ≤ M) →
      ∀ h : PhysicalSpace, physicalEuclideanNorm h ≤ δ → ∀ u : PhysicalSpace,
        (b / 2) * (physicalEuclideanNorm u) ^ 2 ≤
          augmentedTranslationQuadratic F (c + B.val *ᵥ h) B.val u := by
  obtain ⟨b, hb, hs⟩ := augmentedTranslation_uniform_radius_of_gram_dominance k hk
  refine ⟨b, hb, ?_⟩
  intro M
  obtain ⟨δ, hd, hd1, hδ⟩ := hs M
  refine ⟨δ, hd, hd1, ?_⟩
  intro F c lam hlam B hB hM
  exact hδ F c B.val hM (minimizing_gram_quadratic_dominance F c lam hlam B hB)

end PaperI
