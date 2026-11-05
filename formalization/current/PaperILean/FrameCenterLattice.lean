import PaperILean.IntegerPointBoxes
import PaperILean.RelativeOrientationPacking

/-! I317,333,337: the actual integer center lattice and its relative count.
Every spacing gamma>0 is allowed; the additive endpoint term is not dropped.
PhysicalSpace and its Euclidean norm retain their existing definitions. -/
noncomputable section
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

def frameLatticePoint (γ : ℝ) (B : PositiveFrame) (z : Fin 3 → ℤ) : PhysicalSpace :=
  γ • (B.val *ᵥ integerPhysicalVector z)

def relativeCenterIndices (γ : ℝ) (Bstar B : PositiveFrame) (cstar : PhysicalSpace)
    (M : ℝ) : Set (Fin 3 → ℤ) :=
  {z | physicalEuclideanNorm (Bstar.val⁻¹ *ᵥ (frameLatticePoint γ B z - cstar)) ≤ M}

def relativeCenterPoints (γ : ℝ) (Bstar B : PositiveFrame) (cstar : PhysicalSpace)
    (M : ℝ) : Set PhysicalSpace :=
  frameLatticePoint γ B '' relativeCenterIndices γ Bstar B cstar M

theorem frameLatticePoint_normalized (γ : ℝ) (B : PositiveFrame) (z : Fin 3 → ℤ) :
    B.val⁻¹ *ᵥ frameLatticePoint γ B z = γ • integerPhysicalVector z := by
  simp only [frameLatticePoint, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    relativeFrame_initial, Matrix.one_mulVec]

theorem frameLatticePoint_injective (γ : ℝ) (hγ : 0 < γ) (B : PositiveFrame) :
    Function.Injective (frameLatticePoint γ B) := by
  intro z w h
  have hv := congrArg (fun v : PhysicalSpace => B.val⁻¹ *ᵥ v) h
  dsimp only at hv
  rw [frameLatticePoint_normalized, frameLatticePoint_normalized] at hv
  funext i
  have hi := congrArg (fun v : PhysicalSpace => v i) hv
  change γ * (z i : ℝ) = γ * (w i : ℝ) at hi
  exact_mod_cast (mul_left_cancel₀ hγ.ne' hi)

theorem scaled_integer_coordinate_bound (γ L : ℝ) (hγ : 0 < γ)
    (z : Fin 3 → ℤ) (a : PhysicalSpace)
    (h : physicalEuclideanNorm (γ • integerPhysicalVector z - a) ≤ L) :
    ∀ i, |(z i : ℝ) - a i / γ| ≤ L / γ := by
  intro i
  have hi := (physical_abs_apply_le (γ • integerPhysicalVector z - a) i).trans h
  change |γ * (z i : ℝ) - a i| ≤ L at hi
  have heq : (z i : ℝ) - a i / γ = (γ * (z i : ℝ) - a i) / γ := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hγ]
  exact div_le_div_of_nonneg_right hi hγ.le

theorem relativeCenter_displacement_identity (γ : ℝ) (Bstar B : PositiveFrame)
    (cstar : PhysicalSpace) (z : Fin 3 → ℤ) :
    (Bstar.val⁻¹ * B.val)⁻¹ *ᵥ
        (Bstar.val⁻¹ *ᵥ (frameLatticePoint γ B z - cstar)) =
      γ • integerPhysicalVector z - B.val⁻¹ *ᵥ cstar := by
  rw [relativeFrame_inverse, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr Bstar.property.ne'), Matrix.mul_one,
    Matrix.mulVec_sub, frameLatticePoint_normalized]

theorem relativeCenter_normalized_bound (γ : ℝ) (Bstar B : PositiveFrame)
    (cstar : PhysicalSpace) (M : ℝ) (hM : 0 ≤ M)
    (hinv : ‖(Bstar.val⁻¹ * B.val)⁻¹‖ ≤ M)
    (z : Fin 3 → ℤ) (hz : z ∈ relativeCenterIndices γ Bstar B cstar M) :
    physicalEuclideanNorm (γ • integerPhysicalVector z - B.val⁻¹ *ᵥ cstar) ≤ M^2 := by
  rw [← relativeCenter_displacement_identity γ Bstar B cstar z]
  exact (physicalEuclideanNorm_mulVec_le_opNorm _ _).trans
    (by simpa only [pow_two] using mul_le_mul hinv hz (physicalEuclideanNorm_nonneg _) hM)

theorem relativeCenter_coordinate_bound (γ : ℝ) (hγ : 0 < γ) (Bstar B : PositiveFrame)
    (cstar : PhysicalSpace) (M : ℝ) (hM : 0 ≤ M)
    (hinv : ‖(Bstar.val⁻¹ * B.val)⁻¹‖ ≤ M)
    (z : Fin 3 → ℤ) (hz : z ∈ relativeCenterIndices γ Bstar B cstar M) :
    ∀ i, |(z i : ℝ) - (B.val⁻¹ *ᵥ cstar) i / γ| ≤ M^2 / γ :=
  scaled_integer_coordinate_bound γ (M^2) hγ z (B.val⁻¹ *ᵥ cstar)
    (relativeCenter_normalized_bound γ Bstar B cstar M hM hinv z hz)

theorem relativeCenterIndices_finite (γ : ℝ) (hγ : 0 < γ) (Bstar B : PositiveFrame)
    (cstar : PhysicalSpace) (M : ℝ) (hM : 0 ≤ M)
    (hinv : ‖(Bstar.val⁻¹ * B.val)⁻¹‖ ≤ M) :
    (relativeCenterIndices γ Bstar B cstar M).Finite :=
  integerPointSet_finite_of_coordinate_bound _ (fun i => (B.val⁻¹ *ᵥ cstar) i / γ) (M^2/γ)
    (relativeCenter_coordinate_bound γ hγ Bstar B cstar M hM hinv)

theorem relativeCenterIndices_ncard_le (γ : ℝ) (hγ : 0 < γ) (Bstar B : PositiveFrame)
    (cstar : PhysicalSpace) (M : ℝ) (hM : 0 ≤ M)
    (hinv : ‖(Bstar.val⁻¹ * B.val)⁻¹‖ ≤ M) :
    ((relativeCenterIndices γ Bstar B cstar M).ncard : ℝ) ≤ (2*M^2/γ+2)^3 := by
  have h := integerPointSet_ncard_le _ (fun i => (B.val⁻¹ *ᵥ cstar) i / γ) (M^2/γ)
    (by positivity) (relativeCenter_coordinate_bound γ hγ Bstar B cstar M hM hinv)
  convert h using 1
  ring

theorem relativeCenterPoints_finite (γ : ℝ) (hγ : 0 < γ) (Bstar B : PositiveFrame)
    (cstar : PhysicalSpace) (M : ℝ) (hM : 0 ≤ M)
    (hinv : ‖(Bstar.val⁻¹ * B.val)⁻¹‖ ≤ M) :
    (relativeCenterPoints γ Bstar B cstar M).Finite :=
  (relativeCenterIndices_finite γ hγ Bstar B cstar M hM hinv).image _

theorem relativeCenterPoints_ncard_eq (γ : ℝ) (hγ : 0 < γ) (Bstar B : PositiveFrame)
    (cstar : PhysicalSpace) (M : ℝ) :
    (relativeCenterPoints γ Bstar B cstar M).ncard =
      (relativeCenterIndices γ Bstar B cstar M).ncard :=
  Set.ncard_image_of_injective _ (frameLatticePoint_injective γ hγ B)

end PaperI
