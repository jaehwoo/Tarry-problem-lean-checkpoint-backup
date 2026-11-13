import PaperILean.FrameCenterLattice
import Mathlib.Analysis.Normed.Group.Bounded

/-! I317,340: finiteness of the actual lattice in any bounded physical region.
This assertion is for each fixed positive frame and spacing; the uniform local
count is a separate theorem and does not depend on the size of the region. -/
noncomputable section
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

def frameLatticeIndicesIn (γ : ℝ) (B : PositiveFrame) (X : Set PhysicalSpace) :
    Set (Fin 3 → ℤ) := {z | frameLatticePoint γ B z ∈ X}

def frameLatticeCentersIn (γ : ℝ) (B : PositiveFrame) (X : Set PhysicalSpace) :
    Set PhysicalSpace := frameLatticePoint γ B '' frameLatticeIndicesIn γ B X

theorem physicalEuclideanNorm_le_sqrt_three_piNorm (v : PhysicalSpace) :
    physicalEuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := by
  have h := coordinateL2Norm_le_of_component_bound v ‖v‖ (norm_nonneg v)
    (fun i => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
  simpa [physicalEuclideanNorm] using h

theorem frameLatticeIndicesIn_coordinate_bound (γ : ℝ) (hγ : 0 < γ) (B : PositiveFrame)
    (X : Set PhysicalSpace) (T : ℝ) (hX : ∀ x ∈ X, physicalEuclideanNorm x ≤ T)
    (z : Fin 3 → ℤ) (hz : z ∈ frameLatticeIndicesIn γ B X) :
    ∀ i, |(z i : ℝ) - (0 : PhysicalSpace) i| ≤ ‖B.val⁻¹‖ * T / γ := by
  have hv : physicalEuclideanNorm (γ • integerPhysicalVector z - (0 : PhysicalSpace)) ≤
      ‖B.val⁻¹‖ * T := by
    rw [sub_zero, ← frameLatticePoint_normalized γ B z]
    exact (physicalEuclideanNorm_mulVec_le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (hX _ hz) (norm_nonneg _))
  simpa using scaled_integer_coordinate_bound γ (‖B.val⁻¹‖ * T) hγ z 0 hv

theorem frameLatticeIndicesIn_finite_of_euclidean_bound (γ : ℝ) (hγ : 0 < γ)
    (B : PositiveFrame) (X : Set PhysicalSpace) (T : ℝ)
    (hX : ∀ x ∈ X, physicalEuclideanNorm x ≤ T) :
    (frameLatticeIndicesIn γ B X).Finite :=
  integerPointSet_finite_of_coordinate_bound _ 0 (‖B.val⁻¹‖ * T / γ)
    (frameLatticeIndicesIn_coordinate_bound γ hγ B X T hX)

theorem frameLatticeIndicesIn_finite (γ : ℝ) (hγ : 0 < γ) (B : PositiveFrame)
    (X : Set PhysicalSpace) (hX : Bornology.IsBounded X) :
    (frameLatticeIndicesIn γ B X).Finite := by
  obtain ⟨T, _, hT⟩ := hX.exists_pos_norm_le
  apply frameLatticeIndicesIn_finite_of_euclidean_bound γ hγ B X (Real.sqrt 3 * T)
  intro x hx
  exact (physicalEuclideanNorm_le_sqrt_three_piNorm x).trans
    (mul_le_mul_of_nonneg_left (hT x hx) (Real.sqrt_nonneg _))

theorem frameLatticeCentersIn_eq_inter_range (γ : ℝ) (B : PositiveFrame)
    (X : Set PhysicalSpace) :
    frameLatticeCentersIn γ B X = X ∩ Set.range (frameLatticePoint γ B) := by
  ext x
  simp only [frameLatticeCentersIn, frameLatticeIndicesIn, Set.mem_image,
    Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_range]
  aesop

theorem frameLatticeCentersIn_finite (γ : ℝ) (hγ : 0 < γ) (B : PositiveFrame)
    (X : Set PhysicalSpace) (hX : Bornology.IsBounded X) :
    (frameLatticeCentersIn γ B X).Finite :=
  (frameLatticeIndicesIn_finite γ hγ B X hX).image _

theorem frameLatticeCentersIn_ncard_eq (γ : ℝ) (hγ : 0 < γ) (B : PositiveFrame)
    (X : Set PhysicalSpace) :
    (frameLatticeCentersIn γ B X).ncard = (frameLatticeIndicesIn γ B X).ncard :=
  Set.ncard_image_of_injective _ (frameLatticePoint_injective γ hγ B)

end PaperI
