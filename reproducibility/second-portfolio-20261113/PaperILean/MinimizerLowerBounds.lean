import PaperILean.RawJetContractionBounds
import PaperILean.MinimizerTranslationStop
import PaperILean.OriginalEigenvectorFrameBound

/-! I234-241, I255-259: the inverse-R lower frame bound, in its equivalent
all-directions form. The proof uses the original unit-eigenvector balance
calculation and then passes to all directions. No lower frame bound is an input.
The logarithm-size and bounded-jet conclusions of I259 are not proved here.
-/
noncomputable section
open scoped BigOperators Matrix
namespace PaperI

theorem inverse_radius_bound_of_quadratic (C R x y : ℝ)
    (hC : 0 ≤ C) (hR : 1 ≤ R) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 2 ≤ (1 + C * R ^ 2) * y ^ 2) :
    (Real.sqrt (1 + C))⁻¹ / R * x ≤ y := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hs : 0 < Real.sqrt (1 + C) := Real.sqrt_pos.mpr (by linarith)
  have hf : 1 + C * R ^ 2 ≤ (1 + C) * R ^ 2 := by nlinarith
  have hh : x ^ 2 ≤ (Real.sqrt (1 + C) * R * y) ^ 2 := by
    calc
      x ^ 2 ≤ (1 + C * R ^ 2) * y ^ 2 := h
      _ ≤ ((1 + C) * R ^ 2) * y ^ 2 := mul_le_mul_of_nonneg_right hf (sq_nonneg y)
      _ = (Real.sqrt (1 + C) * R * y) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 + C)]
  have hl : x ≤ Real.sqrt (1 + C) * R * y :=
    (sq_le_sq₀ hx (by positivity)).mp hh
  calc
    (Real.sqrt (1 + C))⁻¹ / R * x = ((Real.sqrt (1 + C))⁻¹ * x) / R := by ring
    _ ≤ y := (div_le_iff₀ hR0).mpr ((inv_mul_le_iff₀ hs).mpr
      (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hl))

theorem minimizing_frame_lower_bound (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) :
    ∃ a : ℝ, 0 < a ∧ ∀ R : ℝ, 2 ≤ R → ∀ F : CoefficientSpace k,
      coefficientEuclideanNorm F ≤ 2 * R → ∀ c : PhysicalSpace, c ∈ X →
      ∀ lam : ℝ, 0 ≤ lam → ∀ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) →
      ∀ u : PhysicalSpace, a / R * physicalEuclideanNorm u ≤ physicalEuclideanNorm (B.val *ᵥ u) := by
  exact original_minimizing_frame_lower_bound k X hX

theorem source_minimizing_frame_lower_bound (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) :
    ∃ a : ℝ, 0 < a ∧ ∀ CX C0 R : ℝ, 2 ≤ CX → 2 ≤ C0 → 2 ≤ R →
      ∀ F : CoefficientSpace k, coefficientEuclideanNorm F ≤ 2 * R →
      ∀ c : PhysicalSpace, c ∈ X → ∀ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c (sourceRegularization CX C0 R) B.val ≤
        FrameEnergy F c (sourceRegularization CX C0 R) D.val) →
      ∀ u : PhysicalSpace, a / R * physicalEuclideanNorm u ≤ physicalEuclideanNorm (B.val *ᵥ u) := by
  obtain ⟨a, ha, hb⟩ := minimizing_frame_lower_bound k X hX
  exact ⟨a, ha, fun CX C0 R hCX hC0 hR F hF c hc B hB =>
    hb R hR F hF c hc _ (sourceRegularization_pos CX C0 R hCX hC0 hR).le B hB⟩

theorem source_minimizing_unit_direction_lower_bound (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) :
    ∃ a : ℝ, 0 < a ∧ ∀ CX C0 R : ℝ, 2 ≤ CX → 2 ≤ C0 → 2 ≤ R →
      ∀ F : CoefficientSpace k, coefficientEuclideanNorm F ≤ 2 * R →
      ∀ c : PhysicalSpace, c ∈ X → ∀ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c (sourceRegularization CX C0 R) B.val ≤
        FrameEnergy F c (sourceRegularization CX C0 R) D.val) →
      ∀ u : PhysicalSpace, physicalEuclideanNorm u = 1 → a / R ≤ physicalEuclideanNorm (B.val *ᵥ u) := by
  obtain ⟨a, ha, hb⟩ := source_minimizing_frame_lower_bound k X hX
  refine ⟨a, ha, ?_⟩
  intro CX C0 R hCX hC0 hR F hF c hc B hB u hu
  simpa only [hu, mul_one] using hb CX C0 R hCX hC0 hR F hF c hc B hB u

theorem source_minimizing_frame_and_stopping_common_constant (k : ℕ) (hk : 2 ≤ k)
    (X : Set PhysicalSpace) (hX : Bornology.IsBounded X) :
    ∃ a : ℝ, 0 < a ∧ ∀ CX C0 R : ℝ, 2 ≤ CX → 2 ≤ C0 → 2 ≤ R →
      ∀ F : CoefficientSpace k, coefficientEuclideanNorm F ≤ 2 * R →
      ∀ c : PhysicalSpace, c ∈ X → ∀ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c (sourceRegularization CX C0 R) B.val ≤
        FrameEnergy F c (sourceRegularization CX C0 R) D.val) →
      ∀ u : PhysicalSpace,
        (a / R * physicalEuclideanNorm u ≤ physicalEuclideanNorm (B.val *ᵥ u)) ∧
        (a * (physicalEuclideanNorm u) ^ 2 ≤ augmentedTranslationQuadratic F c B.val u) := by
  obtain ⟨a, ha, hframe⟩ := source_minimizing_frame_lower_bound k X hX
  obtain ⟨b, hb, hstop⟩ := source_augmentedTranslation_lower_bound_of_minimum k hk
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro CX C0 R hCX hC0 hR F hF c hc B hB u
  constructor
  · exact (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (min_le_left a b) (by linarith))
      (physicalEuclideanNorm_nonneg u)).trans (hframe CX C0 R hCX hC0 hR F hF c hc B hB u)
  · exact (mul_le_mul_of_nonneg_right (min_le_right a b) (sq_nonneg _)).trans
      (hstop CX C0 R hCX hC0 hR F c B hB u)

end PaperI
