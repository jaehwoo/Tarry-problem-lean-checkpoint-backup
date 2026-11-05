import PaperILean.EllipsoidGeometry

/-! Source278/298: right-orthogonal representative invariance and composition.
The representatives at the intersection may differ. The relative norm equality
below accounts for their orthogonal factor before the estimates are composed. -/
noncomputable section
open Set
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

theorem orthogonal_matrix_opNorm (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q * Qᵀ = 1) :
    ‖Q‖ = 1 := by
  apply CStarRing.norm_of_mem_unitary
  apply Matrix.mem_unitaryGroup_iff.mpr
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hQ

theorem matrix_opNorm_mul_orthogonal (A Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : Q * Qᵀ = 1) : ‖A * Q‖ = ‖A‖ := by
  apply CStarRing.norm_mul_mem_unitary
  apply Matrix.mem_unitaryGroup_iff.mpr
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hQ

theorem physicalEuclideanNorm_mulVec_orthogonal (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : Q * Qᵀ = 1) (v : PhysicalSpace) :
    physicalEuclideanNorm (Q *ᵥ v) = physicalEuclideanNorm v := by
  have hQt : Qᵀ * Qᵀᵀ = 1 := by
    simpa only [Matrix.transpose_transpose] using (Matrix.mul_eq_one_comm.mp hQ)
  unfold physicalEuclideanNorm coordinateL2Norm
  congr 1
  simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply] using sum_sq_orthogonal_rows Qᵀ hQt v

theorem frameBall_right_orthogonal (c : PhysicalSpace) (r : ℝ)
    (B Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q * Qᵀ = 1) :
    frameBall c r (B * Q) = frameBall c r B := by
  have hQt : Qᵀ * Qᵀᵀ = 1 := by
    simpa only [Matrix.transpose_transpose] using (Matrix.mul_eq_one_comm.mp hQ)
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨Q *ᵥ v, ?_, ?_⟩
    · simpa only [physicalUnitBall, mem_setOf_eq, physicalEuclideanNorm_mulVec_orthogonal Q hQ] using hv
    · dsimp only
      rw [Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, rfl⟩
    refine ⟨Qᵀ *ᵥ v, ?_, ?_⟩
    · simpa only [physicalUnitBall, mem_setOf_eq, physicalEuclideanNorm_mulVec_orthogonal Qᵀ hQt] using hv
    · dsimp only
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hQ, Matrix.mul_one]

theorem frameClosedBall_right_orthogonal (c : PhysicalSpace) (r : ℝ)
    (B Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q * Qᵀ = 1) :
    frameClosedBall c r (B * Q) = frameClosedBall c r B := by
  have hQt : Qᵀ * Qᵀᵀ = 1 := by
    simpa only [Matrix.transpose_transpose] using (Matrix.mul_eq_one_comm.mp hQ)
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨Q *ᵥ v, ?_, ?_⟩
    · simpa only [physicalClosedUnitBall, mem_setOf_eq, physicalEuclideanNorm_mulVec_orthogonal Q hQ] using hv
    · dsimp only
      rw [Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, rfl⟩
    refine ⟨Qᵀ *ᵥ v, ?_, ?_⟩
    · simpa only [physicalClosedUnitBall, mem_setOf_eq, physicalEuclideanNorm_mulVec_orthogonal Qᵀ hQt] using hv
    · dsimp only
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hQ, Matrix.mul_one]

theorem frameBalls_eq_of_same_gram (c : PhysicalSpace) (r : ℝ) (B C : PositiveFrame)
    (hgram : B.val * B.valᵀ = C.val * C.valᵀ) :
    frameBall c r B.val = frameBall c r C.val ∧
      frameClosedBall c r B.val = frameClosedBall c r C.val := by
  obtain ⟨Q, hQ, _, hC⟩ := (same_gram_iff_right_specialOrthogonal B C).mp hgram
  rw [hC, frameBall_right_orthogonal c r B.val Q hQ,
    frameClosedBall_right_orthogonal c r B.val Q hQ]
  exact ⟨rfl, rfl⟩

theorem relativeFrame_opNorm_eq_of_same_gram (B C D : PositiveFrame)
    (hgram : C.val * C.valᵀ = D.val * D.valᵀ) :
    ‖B.val⁻¹ * C.val‖ = ‖B.val⁻¹ * D.val‖ := by
  obtain ⟨Q, hQ, _, hD⟩ := (same_gram_iff_right_specialOrthogonal C D).mp hgram
  rw [hD, ← Matrix.mul_assoc, matrix_opNorm_mul_orthogonal _ Q hQ]

theorem relativeFrame_composition (B C D : PositiveFrame) :
    B.val⁻¹ * C.val = (B.val⁻¹ * D.val) * (C.val⁻¹ * D.val)⁻¹ := by
  rw [relativeFrame_inverse]
  symm
  calc
    (B.val⁻¹ * D.val) * (D.val⁻¹ * C.val) = B.val⁻¹ * (D.val * D.val⁻¹) * C.val := by
      simp only [Matrix.mul_assoc]
    _ = B.val⁻¹ * C.val := by
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr D.property.ne'), Matrix.mul_one]

theorem relativeFrame_comparison_of_same_gram (B C D E : PositiveFrame)
    (hgram : D.val * D.valᵀ = E.val * E.valᵀ) (L M : ℝ)
    (hD : ‖B.val⁻¹ * D.val‖ ≤ L) (hE : ‖(C.val⁻¹ * E.val)⁻¹‖ ≤ M) :
    ‖B.val⁻¹ * C.val‖ ≤ L * M := by
  rw [relativeFrame_opNorm_eq_of_same_gram B D E hgram] at hD
  rw [relativeFrame_composition B C E]
  exact (norm_mul_le _ _).trans (mul_le_mul hD hE (norm_nonneg _) ((norm_nonneg _).trans hD))

end PaperI
