import PaperILean.SPDFrameRepresentative

/-! The polar-log connection used at Paper I248, for arbitrary positive
frames. Positive orientation forces the final orthogonal factor into SO(3). -/
noncomputable section
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

theorem positiveFrame_inverse_mul_det_pos (B C : PositiveFrame) :
    0 < (B.val⁻¹ * C.val).det := by
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact mul_pos (inv_pos.mpr B.property) C.property

theorem exists_symmetric_exponential_connection (B C : PositiveFrame) :
    ∃ H : Matrix (Fin 3) (Fin 3) ℝ, H.IsSymm ∧
      ∃ Q : Matrix (Fin 3) (Fin 3) ℝ, Q * Qᵀ = 1 ∧ Q.det = 1 ∧
        C.val = B.val * NormedSpace.exp ℝ H * Q := by
  let D : PositiveFrame := ⟨B.val⁻¹ * C.val, positiveFrame_inverse_mul_det_pos B C⟩
  let S := spdFrameRepresentative D
  have hS : S.val.PosDef := spdFrameRepresentative_posDef D
  obtain ⟨Q, hQ, hdet, hD⟩ := (same_gram_iff_right_specialOrthogonal S D).mp
    (spdFrameRepresentative_gram D)
  refine ⟨CFC.log S.val,
    (realMatrix_isSelfAdjoint_iff_isSymm _).mp (IsSelfAdjoint.log (a := S.val)),
    Q, hQ, hdet, ?_⟩
  rw [sourceMatrix_exp_log S.val hS]
  have hC : C.val = B.val * D.val :=
    (Matrix.mul_nonsing_inv_cancel_left B.val C.val
      ((Matrix.isUnit_iff_isUnit_det B.val).mp (positiveFrame_isUnit B))).symm
  rw [hC, hD, Matrix.mul_assoc]

theorem same_gram_of_zero_exponential_connection (B C : PositiveFrame)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q * Qᵀ = 1)
    (hC : C.val = B.val * NormedSpace.exp ℝ (0 : Matrix (Fin 3) (Fin 3) ℝ) * Q) :
    B.val * B.valᵀ = C.val * C.valᵀ := by
  simp only [NormedSpace.exp_zero, mul_one] at hC
  rw [hC, frameGram_right_orthogonal _ Q hQ]

end PaperI
