import PaperILean.FrameEnergy

/-! Positive-determinant frames modulo right SO(3).
The Gram-matrix relation is proved equivalent to the explicit right-SO relation
before the energy is descended. No existence of a minimizer is assumed. -/

noncomputable section
open scoped Matrix
namespace PaperI

theorem inverse_right_factor_orthogonal {n : ℕ}
    (B C : Matrix (Fin n) (Fin n) ℝ) (hB : IsUnit B)
    (hgram : B * Bᵀ = C * Cᵀ) :
    (B⁻¹ * C) * (B⁻¹ * C)ᵀ = 1 := by
  have hi := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  calc
    (B⁻¹ * C) * (B⁻¹ * C)ᵀ = B⁻¹ * (C * Cᵀ) * B⁻¹ᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = B⁻¹ * (B * Bᵀ) * B⁻¹ᵀ := by rw [← hgram]
    _ = (B⁻¹ * B) * (B⁻¹ * B)ᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hi]; simp

theorem same_gram_iff_right_specialOrthogonal (B C : PositiveFrame) :
    (B.val * B.valᵀ = C.val * C.valᵀ) ↔
      ∃ Q : Matrix (Fin 3) (Fin 3) ℝ, Q * Qᵀ = 1 ∧ Q.det = 1 ∧ C.val = B.val * Q := by
  constructor
  · intro hgram
    let Q := B.val⁻¹ * C.val
    have hQ : Q * Qᵀ = 1 := inverse_right_factor_orthogonal _ _ (positiveFrame_isUnit B) hgram
    have hpos : 0 < Q.det := by
      dsimp [Q]
      rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      exact mul_pos (inv_pos.mpr B.property) C.property
    have hsq : Q.det * Q.det = 1 := by
      simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using congrArg Matrix.det hQ
    have hdet : Q.det = 1 := by nlinarith
    refine ⟨Q, hQ, hdet, ?_⟩
    exact (Matrix.mul_nonsing_inv_cancel_left B.val C.val
      ((Matrix.isUnit_iff_isUnit_det B.val).mp (positiveFrame_isUnit B))).symm
  · rintro ⟨Q, hQ, _, hC⟩
    rw [hC, frameGram_right_orthogonal _ Q hQ]

def positiveFrameGramSetoid : Setoid PositiveFrame where
  r B C := B.val * B.valᵀ = C.val * C.valᵀ
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

def PositiveFrameEllipsoid := Quotient positiveFrameGramSetoid

theorem FrameEnergy_eq_of_same_gram {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B C : PositiveFrame)
    (hgram : B.val * B.valᵀ = C.val * C.valᵀ) :
    FrameEnergy F c lam B.val = FrameEnergy F c lam C.val := by
  obtain ⟨Q, hQ, hdet, hC⟩ := (same_gram_iff_right_specialOrthogonal B C).mp hgram
  rw [hC, FrameEnergy_right_specialOrthogonal F c lam B.val Q hQ hdet]

def ellipsoidFrameEnergy {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (lam : ℝ) : PositiveFrameEllipsoid → ℝ :=
  Quotient.lift (fun B : PositiveFrame => FrameEnergy F c lam B.val)
    (fun B C h => FrameEnergy_eq_of_same_gram F c lam B C h)

theorem ellipsoidFrameEnergy_mk {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (lam : ℝ) (B : PositiveFrame) :
    ellipsoidFrameEnergy F c lam (Quotient.mk positiveFrameGramSetoid B) =
      FrameEnergy F c lam B.val := rfl

theorem positiveFrameEllipsoid_eq_iff (B C : PositiveFrame) :
    Quotient.mk positiveFrameGramSetoid B = Quotient.mk positiveFrameGramSetoid C ↔
      ∃ Q : Matrix (Fin 3) (Fin 3) ℝ, Q * Qᵀ = 1 ∧ Q.det = 1 ∧ C.val = B.val * Q := by
  rw [Quotient.eq]
  exact same_gram_iff_right_specialOrthogonal B C

end PaperI
