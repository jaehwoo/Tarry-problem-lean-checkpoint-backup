import PaperILean.MatrixCubePacking
import PaperILean.RotationSingularApproximation

/-! I333-336: the cube count for orientations in a reference frame's relative
matrix neighborhood. Both matrix and inverse bounds are the manuscript bounds.
No singular-value ratio, reference-frame norm, or coefficient enters the constant. -/
noncomputable section
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

theorem relativeFrame_isUnit_det (Bstar B : PositiveFrame) :
    IsUnit (Bstar.val⁻¹ * B.val).det := by
  rw [Matrix.det_mul]
  exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr Bstar.property.ne')).mul
    (isUnit_iff_ne_zero.mpr B.property.ne')

theorem relativeFrame_left_reference_cancel (Bstar B D : PositiveFrame) :
    (Bstar.val⁻¹ * B.val)⁻¹ * (Bstar.val⁻¹ * D.val) = B.val⁻¹ * D.val := by
  rw [relativeFrame_inverse]
  calc
    (B.val⁻¹ * Bstar.val) * (Bstar.val⁻¹ * D.val) =
        B.val⁻¹ * (Bstar.val * Bstar.val⁻¹) * D.val := by simp only [Matrix.mul_assoc]
    _ = B.val⁻¹ * D.val := by
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr Bstar.property.ne'), Matrix.mul_one]

def relativeOrientationSet (s : Finset rotationGroup3) (Bstar E : PositiveFrame)
    (M : ℝ) : Finset rotationGroup3 := by
  classical
  exact s.filter fun O =>
    ‖Bstar.val⁻¹ * (rotatedPositiveFrame E O).val‖ ≤ M ∧
    ‖(Bstar.val⁻¹ * (rotatedPositiveFrame E O).val)⁻¹‖ ≤ M

theorem mem_relativeOrientationSet (s : Finset rotationGroup3) (Bstar E : PositiveFrame)
    (M : ℝ) (O : rotationGroup3) :
    O ∈ relativeOrientationSet s Bstar E M ↔ O ∈ s ∧
      ‖Bstar.val⁻¹ * (rotatedPositiveFrame E O).val‖ ≤ M ∧
      ‖(Bstar.val⁻¹ * (rotatedPositiveFrame E O).val)⁻¹‖ ≤ M := by
  classical
  simp [relativeOrientationSet]

theorem relativeOrientationSet_card_le (s : Finset rotationGroup3) (Bstar E : PositiveFrame)
    (M θ : ℝ) (hM : 2 ≤ M) (hθ0 : 0 < θ) (hθ : θ < 1/10)
    (hsep : ∀ O ∈ s, ∀ P ∈ s, O ≠ P →
      θ/4 ≤ ‖(rotatedPositiveFrame E O).val⁻¹ * (rotatedPositiveFrame E P).val - 1‖) :
    ((relativeOrientationSet s Bstar E M).card : ℝ) ≤ (50 : ℝ)^9 * M^18 / θ^9 := by
  apply matrixCubePacking_card_le_explicit (relativeOrientationSet s Bstar E M)
    (fun O => Bstar.val⁻¹ * (rotatedPositiveFrame E O).val) M θ hM hθ0 hθ
  · intro O _
    exact relativeFrame_isUnit_det Bstar (rotatedPositiveFrame E O)
  · intro O hO
    exact ((mem_relativeOrientationSet s Bstar E M O).mp hO).2.1
  · intro O hO
    exact ((mem_relativeOrientationSet s Bstar E M O).mp hO).2.2
  · intro O hO P hP hne
    rw [relativeFrame_left_reference_cancel]
    exact hsep O ((mem_relativeOrientationSet s Bstar E M O).mp hO).1
      P ((mem_relativeOrientationSet s Bstar E M P).mp hP).1 hne

end PaperI
