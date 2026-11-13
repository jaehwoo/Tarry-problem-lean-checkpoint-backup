import PaperILean.FrameEllipsoidQuotient
import PaperILean.SpectralFrameBarrier

/-! Every positive frame has a positive-definite representative with precisely
the same Gram matrix and energy. No minimum is presupposed. Paper I 246. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem posSemidef_posDef_of_det_ne_zero {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) (hdet : S.det ≠ 0) : S.PosDef := by
  have hp : ∀ i, 0 < hS.isHermitian.eigenvalues i := by
    intro i
    have he : hS.isHermitian.eigenvalues i ≠ 0 := by
      have hh := hS.isHermitian.det_eq_prod_eigenvalues
      rw [hh] at hdet
      exact (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)
    exact lt_of_le_of_ne (hS.eigenvalues_nonneg i) he.symm
  have hspec : S = orthogonalConjugate hS.isHermitian.eigenvectorUnitary
      (Matrix.diagonal hS.isHermitian.eigenvalues) := by
    simpa [orthogonalConjugate, Function.comp_def] using hS.isHermitian.spectral_theorem
  rw [hspec]
  exact orthogonalConjugate_posDef _ _ (Matrix.PosDef.diagonal hp)

theorem sourcePositiveSqrt_posDef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) : (sourcePositiveSqrt A hA).PosDef :=
  posSemidef_posDef_of_det_ne_zero _ hA.posSemidef.posSemidef_sqrt
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (sourcePositiveSqrt_isUnit A hA)))

def spdFrameRepresentative (B : PositiveFrame) : PositiveFrame :=
  ⟨sourcePositiveSqrt (B.val * B.valᵀ) (positiveFrame_gram_posDef B),
    (sourcePositiveSqrt_posDef _ (positiveFrame_gram_posDef B)).det_pos⟩

theorem spdFrameRepresentative_posDef (B : PositiveFrame) :
    (spdFrameRepresentative B).val.PosDef :=
  sourcePositiveSqrt_posDef _ (positiveFrame_gram_posDef B)

theorem spdFrameRepresentative_gram (B : PositiveFrame) :
    (spdFrameRepresentative B).val * (spdFrameRepresentative B).valᵀ = B.val * B.valᵀ := by
  dsimp only [spdFrameRepresentative]
  rw [(sourcePositiveSqrt_isSymm _ (positiveFrame_gram_posDef B)).eq, sourcePositiveSqrt_mul_self]

theorem spdFrameRepresentative_energy {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame) :
    FrameEnergy F c lam (spdFrameRepresentative B).val = FrameEnergy F c lam B.val :=
  FrameEnergy_eq_of_same_gram F c lam _ B (spdFrameRepresentative_gram B)

theorem spdFrameRepresentative_quotient (B : PositiveFrame) :
    Quotient.mk positiveFrameGramSetoid (spdFrameRepresentative B) =
      Quotient.mk positiveFrameGramSetoid B :=
  Quotient.sound (spdFrameRepresentative_gram B)

theorem exists_posDef_same_gram_energy {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame) :
    ∃ S : Matrix (Fin 3) (Fin 3) ℝ, S.PosDef ∧ S * Sᵀ = B.val * B.valᵀ ∧
      FrameEnergy F c lam S = FrameEnergy F c lam B.val :=
  ⟨(spdFrameRepresentative B).val, spdFrameRepresentative_posDef B,
    spdFrameRepresentative_gram B, spdFrameRepresentative_energy F c lam B⟩

theorem FrameEnergy_positiveFrame_ge_three {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (B : PositiveFrame) :
    3 ≤ FrameEnergy F c lam B.val := by
  rw [← spdFrameRepresentative_energy F c lam B]
  exact FrameEnergy_posDef_ge_three F c lam hlam _ (spdFrameRepresentative_posDef B)

end PaperI
