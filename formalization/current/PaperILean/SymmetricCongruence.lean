import PaperILean.SymmetricLogSmoothness

/-! Exact congruence on the real symmetric space, with no commutation premise. -/
noncomputable section
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

def symmetricCongruence {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (A : SymmetricMatrix n) : SymmetricMatrix n :=
  symmetricMatrixOf (B * A.val * Bᵀ) (by
    show (B * A.val * Bᵀ)ᵀ = B * A.val * Bᵀ
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, A.property.eq, Matrix.mul_assoc])

theorem symmetricCongruence_coe {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (A : SymmetricMatrix n) : (symmetricCongruence B A).val = B * A.val * Bᵀ := rfl

theorem symmetricCongruence_one {n : ℕ} (A : SymmetricMatrix n) :
    symmetricCongruence 1 A = A := by
  apply Subtype.ext
  simp [symmetricCongruence_coe]

theorem symmetricCongruence_comp {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℝ)
    (A : SymmetricMatrix n) :
    symmetricCongruence B (symmetricCongruence C A) = symmetricCongruence (B * C) A := by
  apply Subtype.ext
  simp only [symmetricCongruence_coe, Matrix.transpose_mul, Matrix.mul_assoc]

theorem symmetricCongruence_inv_left {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : IsUnit B) (A : SymmetricMatrix n) :
    symmetricCongruence B⁻¹ (symmetricCongruence B A) = A := by
  rw [symmetricCongruence_comp, Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB),
    symmetricCongruence_one]

theorem symmetricCongruence_inv_right {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : IsUnit B) (A : SymmetricMatrix n) :
    symmetricCongruence B (symmetricCongruence B⁻¹ A) = A := by
  rw [symmetricCongruence_comp, Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB),
    symmetricCongruence_one]

theorem symmetricCongruence_posDef {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : IsUnit B) (A : SymmetricMatrix n) (hA : A.val.PosDef) :
    (symmetricCongruence B A).val.PosDef := by
  simpa only [symmetricCongruence_coe, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_transpose] using hA.conjTranspose_mul_mul_same (B := Bᵀ)
      (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_transpose B).mpr hB))

theorem contDiff_symmetricCongruence {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ ⊤ (symmetricCongruence B) := by
  have h : ContDiff ℝ ⊤ (fun A : SymmetricMatrix n => B * A.val * Bᵀ) :=
    (contDiff_const.mul (symmetricMatrixIncl n).contDiff).mul contDiff_const
  have he : (fun A : SymmetricMatrix n => symmetricMatrixProjection n (B * A.val * Bᵀ)) =
      symmetricCongruence B := by
    funext A
    exact symmetricMatrixProjection_of_symm _ (symmetricCongruence B A).property
  simpa only [Function.comp_def, he] using (symmetricMatrixProjection n).contDiff.comp h

def positiveSymmetricCone (n : ℕ) : Set (SymmetricMatrix n) := {A | A.val.PosDef}

theorem range_symmetricMatrixExp {n : ℕ} :
    Set.range (symmetricMatrixExp : SymmetricMatrix n → SymmetricMatrix n) = positiveSymmetricCone n := by
  ext A
  constructor
  · rintro ⟨X, rfl⟩
    exact symmetricMatrixExp_posDef X
  · intro hA
    exact ⟨symmetricMatrixLog A, symmetricMatrixExp_log A hA⟩

theorem isOpen_positiveSymmetricCone (n : ℕ) : IsOpen (positiveSymmetricCone n) := by
  rw [← range_symmetricMatrixExp, ← Set.image_univ]
  exact (isOpenMap_of_hasStrictFDerivAt_equiv
    (fun X : SymmetricMatrix n => symmetricMatrixExp_hasStrictFDerivAt X)) Set.univ isOpen_univ

end PaperI
