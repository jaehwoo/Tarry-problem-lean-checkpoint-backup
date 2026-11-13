import PaperILean.FrameBalance

/-! Spectral consequences of the exact balance, manuscript I256-265.
The auxiliary matrix theorem keeps positivity of A, semidefiniteness of G,
and nonnegative regularization explicit. It does not assume a spectral bound.
No nonempty dimension or simple-spectrum hypothesis is needed. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem real_posSemidef_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (t : ℝ) (ht : 0 ≤ t) : (t • A).PosSemidef := by
  refine ⟨?_, ?_⟩
  · exact (realMatrix_isHermitian_iff_isSymm _).mpr
      (((realMatrix_isHermitian_iff_isSymm _).mp hA.isHermitian).smul t)
  intro x
  simpa only [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul] using
    mul_nonneg ht (hA.2 x)

theorem real_posSemidef_diag_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (i : Fin n) : 0 ≤ A i i := by
  simpa using hA.2 (Pi.single i 1)

theorem orthogonalConjugate_posSemidef {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) :
    (orthogonalConjugate U A).PosSemidef :=
  hA.mul_mul_conjTranspose_same (U : Matrix (Fin n) (Fin n) ℝ)

theorem orthogonalConjugate_add {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (A D : Matrix (Fin n) (Fin n) ℝ) :
    orthogonalConjugate U (A + D) = orthogonalConjugate U A + orthogonalConjugate U D := by
  simp [orthogonalConjugate, Matrix.mul_add, Matrix.add_mul]

theorem orthogonalConjugate_one {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ)) :
    orthogonalConjugate U 1 = 1 := by
  simp [orthogonalConjugate, unitary.coe_mul_star_self]

theorem sourceMatrix_log_eigenbasis_diagonal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    orthogonalConjugate (star hA.isHermitian.eigenvectorUnitary) (CFC.log A) =
      Matrix.diagonal (fun i => Real.log (hA.isHermitian.eigenvalues i)) := by
  rw [sourceMatrix_log_eq_spectral A hA]
  exact orthogonalConjugate_star_inverse _ _

theorem balance_eigenvalues_le_one {n : ℕ}
    (A G : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hG : G.PosSemidef)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hbal : A + G + (2 * lam) • CFC.log A = 1) (i : Fin n) :
    hA.isHermitian.eigenvalues i ≤ 1 := by
  let U := star hA.isHermitian.eigenvectorUnitary
  have hd := congrArg (orthogonalConjugate U) hbal
  simp only [orthogonalConjugate_add, orthogonalConjugate_smul,
    orthogonalConjugate_one, U, sourceMatrix_eigenbasis_diagonal A hA,
    sourceMatrix_log_eigenbasis_diagonal A hA] at hd
  have hi := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) hd
  simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply_eq] at hi
  have hg := real_posSemidef_diag_nonneg _ (orthogonalConjugate_posSemidef U G hG) i
  by_contra h
  have he : 1 < hA.isHermitian.eigenvalues i := lt_of_not_ge h
  have hl : 0 ≤ Real.log (hA.isHermitian.eigenvalues i) := Real.log_nonneg he.le
  have hm := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlam) hl
  dsimp [U] at hg
  linarith

theorem neg_log_posSemidef_of_eigenvalues_le_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (hupper : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) : (-CFC.log A).PosSemidef := by
  have hp : (Matrix.diagonal (fun i => -Real.log (hA.isHermitian.eigenvalues i))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => neg_nonneg.mpr
      (Real.log_nonpos (hA.eigenvalues_pos i).le (hupper i)))
  have h := orthogonalConjugate_posSemidef hA.isHermitian.eigenvectorUnitary _ hp
  rw [sourceMatrix_log_eq_spectral A hA]
  have hd : Matrix.diagonal (fun i => -Real.log (hA.isHermitian.eigenvalues i)) =
      -Matrix.diagonal (fun i => Real.log (hA.isHermitian.eigenvalues i)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  simpa only [hd, orthogonalConjugate, Matrix.mul_neg, Matrix.neg_mul] using h

theorem one_sub_posSemidef_of_eigenvalues_le_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (hupper : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) : (1 - A).PosSemidef := by
  have hp : (Matrix.diagonal (fun i => 1 - hA.isHermitian.eigenvalues i)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hupper i))
  have h := orthogonalConjugate_posSemidef hA.isHermitian.eigenvectorUnitary _ hp
  have hs : orthogonalConjugate hA.isHermitian.eigenvectorUnitary
      (Matrix.diagonal hA.isHermitian.eigenvalues) = A := by
    simpa [orthogonalConjugate, Function.comp_def] using hA.isHermitian.spectral_theorem.symm
  have he : Matrix.diagonal (fun i => 1 - hA.isHermitian.eigenvalues i) =
      1 - Matrix.diagonal hA.isHermitian.eigenvalues := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  rw [he] at h
  have heq : orthogonalConjugate hA.isHermitian.eigenvectorUnitary
      (1 - Matrix.diagonal hA.isHermitian.eigenvalues) = 1 - A := by
    calc
      _ = 1 - orthogonalConjugate hA.isHermitian.eigenvectorUnitary
          (Matrix.diagonal hA.isHermitian.eigenvalues) := by
        simp [orthogonalConjugate, Matrix.mul_sub, Matrix.sub_mul, unitary.coe_mul_star_self]
      _ = 1 - A := by rw [hs]
  rw [heq] at h
  exact h

theorem balance_gram_dominance {n : ℕ}
    (A G : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hG : G.PosSemidef)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hbal : A + G + (2 * lam) • CFC.log A = 1) : (A + G - 1).PosSemidef := by
  have hlog := neg_log_posSemidef_of_eigenvalues_le_one A hA
    (balance_eigenvalues_le_one A G hA hG lam hlam hbal)
  have he : A + G - 1 = (2 * lam) • (-CFC.log A) := by
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_left (by rw [sub_add_eq_add_sub, hbal, sub_self])
  rw [he]
  exact real_posSemidef_smul _ hlog _ (by positivity)

end PaperI
