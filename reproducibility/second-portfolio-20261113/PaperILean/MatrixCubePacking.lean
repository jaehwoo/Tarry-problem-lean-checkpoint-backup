import PaperILean.MatrixCubeLabels

/-! I333-336: the finite matrix-cube injection and its uniform count.
The hypotheses include both forward and inverse bounds. The constant 50^9
is absolute, and the cardinality theorem applies to arbitrary finite labels. -/
noncomputable section
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

theorem matrix_relative_error_eq_inv_mul_sub
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hA : IsUnit A.det) :
    A⁻¹ * B - 1 = A⁻¹ * (B - A) := by
  rw [Matrix.mul_sub, Matrix.nonsing_inv_mul A hA]

theorem matrixCubeLabel_eq_relative_error_le (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ)
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hA : IsUnit A.det) (hi : ‖A⁻¹‖ ≤ M)
    (h : matrixCubeLabel M δ A = matrixCubeLabel M δ B) :
    ‖A⁻¹ * B - 1‖ ≤ 3 * M * δ := by
  rw [matrix_relative_error_eq_inv_mul_sub A B hA]
  calc
    ‖A⁻¹ * (B - A)‖ ≤ ‖A⁻¹‖ * ‖B - A‖ := norm_mul_le _ _
    _ ≤ M * (3 * δ) := mul_le_mul hi
      (matrixCubeLabel_eq_opNorm_sub_le M δ hδ A B h) (norm_nonneg _) hM
    _ = 3 * M * δ := by ring

theorem matrixCubeLabel_injOn_of_separated {α : Type*}
    (s : Finset α) (C : α → Matrix (Fin 3) (Fin 3) ℝ)
    (M δ ε : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ) (hsmall : 3 * M * δ < ε)
    (hu : ∀ a ∈ s, IsUnit (C a).det) (hi : ∀ a ∈ s, ‖(C a)⁻¹‖ ≤ M)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ε ≤ ‖(C a)⁻¹ * C b - 1‖) :
    (↑s : Set α).InjOn (fun a => matrixCubeLabel M δ (C a)) := by
  intro a ha b hb heq
  by_contra hne
  have h := matrixCubeLabel_eq_relative_error_le M δ hM hδ (C a) (C b)
    (hu a ha) (hi a ha) heq
  exact (not_lt_of_ge (hsep a ha b hb hne)) (h.trans_lt hsmall)

theorem matrixCubePacking_card_le {α : Type*}
    (s : Finset α) (C : α → Matrix (Fin 3) (Fin 3) ℝ)
    (M δ ε : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ) (hsmall : 3 * M * δ < ε)
    (hu : ∀ a ∈ s, IsUnit (C a).det)
    (hf : ∀ a ∈ s, ‖C a‖ ≤ M) (hi : ∀ a ∈ s, ‖(C a)⁻¹‖ ≤ M)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ε ≤ ‖(C a)⁻¹ * C b - 1‖) :
    (s.card : ℝ) ≤ (2 * M / δ + 1) ^ 9 := by
  have hc : s.card ≤ (matrixCubeLabels M δ).card :=
    Finset.card_le_card_of_injOn (fun a => matrixCubeLabel M δ (C a))
      (fun a ha => matrixCubeLabel_mem M δ hδ (C a) (hf a ha))
      (matrixCubeLabel_injOn_of_separated s C M δ ε hM hδ hsmall hu hi hsep)
  exact (show (s.card : ℝ) ≤ (matrixCubeLabels M δ).card by exact_mod_cast hc).trans
    (matrixCubeLabels_card_le M δ hM hδ)

theorem matrixCubePacking_card_le_explicit {α : Type*}
    (s : Finset α) (C : α → Matrix (Fin 3) (Fin 3) ℝ)
    (M θ : ℝ) (hM : 2 ≤ M) (hθ0 : 0 < θ) (hθ : θ < 1/10)
    (hu : ∀ a ∈ s, IsUnit (C a).det)
    (hf : ∀ a ∈ s, ‖C a‖ ≤ M) (hi : ∀ a ∈ s, ‖(C a)⁻¹‖ ≤ M)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → θ/4 ≤ ‖(C a)⁻¹ * C b - 1‖) :
    (s.card : ℝ) ≤ (50 : ℝ)^9 * M^18 / θ^9 := by
  have hM0 : 0 < M := by linarith
  have hδ : 0 < θ / (24 * M) := by positivity
  have hdiam : 3 * M * (θ / (24 * M)) = θ/8 := by field_simp; ring
  have hsmall : 3 * M * (θ / (24 * M)) < θ/4 := by rw [hdiam]; linarith
  have hunit : 1 ≤ M^2 / θ := (le_div_iff₀ hθ0).mpr (by nlinarith)
  have hgrid : 2 * M / (θ / (24 * M)) + 1 ≤ 50 * M^2 / θ := by
    have heq : 2 * M / (θ / (24 * M)) = 48 * (M^2 / θ) := by
      field_simp
      ring
    rw [heq, show 50 * M^2 / θ = 50 * (M^2 / θ) by ring]
    linarith
  calc
    (s.card : ℝ) ≤ (2 * M / (θ / (24 * M)) + 1)^9 :=
      matrixCubePacking_card_le s C M (θ / (24 * M)) (θ/4) hM0.le hδ hsmall hu hf hi hsep
    _ ≤ (50 * M^2 / θ)^9 := pow_le_pow_left₀ (by positivity) hgrid _
    _ = (50 : ℝ)^9 * M^18 / θ^9 := by ring

end PaperI
