import PaperILean.RotationNeighborhoods
import Mathlib.LinearAlgebra.Matrix.Spectrum

/-! I311-315,331: reorder an orthonormal eigenbasis and orient it in SO(3).
No simplicity of eigenvalues or ordering of the library's eigenvalue list is assumed.
The correction det(V) • V is used only in the fixed odd dimension three. -/
noncomputable section
open scoped Matrix
namespace PaperI

theorem orthogonal_columns_reindex (U : Matrix (Fin 3) (Fin 3) ℝ)
    (hU : U * Uᵀ = 1) (σ : Equiv.Perm (Fin 3)) :
    U.submatrix id σ * (U.submatrix id σ)ᵀ = 1 := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, hU,
    Matrix.submatrix_id_id]

theorem spectral_basis_reindex_diagonal (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A.IsHermitian) (σ : Equiv.Perm (Fin 3)) :
    let V := (hA.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℝ).submatrix id σ
    Vᵀ * A * V = Matrix.diagonal (hA.eigenvalues ∘ σ) := by
  let U : Matrix (Fin 3) (Fin 3) ℝ := hA.eigenvectorUnitary
  have hd : Uᵀ * A * U = Matrix.diagonal hA.eigenvalues := by
    simpa only [U, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def,
      RCLike.ofReal_real_eq_id, id_eq] using hA.star_mul_self_mul_eq_diagonal
  change (U.submatrix id σ)ᵀ * A * U.submatrix id σ = _
  calc
    (U.submatrix id σ)ᵀ * A * U.submatrix id σ =
        (Uᵀ * A).submatrix σ (Equiv.refl (Fin 3)) *
          U.submatrix (Equiv.refl (Fin 3)) σ := by
      rw [Matrix.transpose_submatrix]
      congr 1
    _ = (Uᵀ * A * U).submatrix σ σ :=
      Matrix.submatrix_mul_equiv _ _ _ _ _
    _ = Matrix.diagonal (hA.eigenvalues ∘ σ) := by
      rw [hd, Matrix.submatrix_diagonal_equiv]

theorem exists_rotation_preserving_congruence (V : Matrix (Fin 3) (Fin 3) ℝ)
    (hV : V * Vᵀ = 1) :
    ∃ O : rotationGroup3, ∀ A : Matrix (Fin 3) (Fin 3) ℝ,
      (rotationMatrix O)ᵀ * A * rotationMatrix O = Vᵀ * A * V := by
  have hs : V.det * V.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using
      congrArg Matrix.det hV
  let W : Matrix (Fin 3) (Fin 3) ℝ := V.det • V
  have hW : W * Wᵀ = 1 := by
    simp only [W, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hs, one_smul, hV]
  have hd : W.det = 1 := by
    dsimp only [W]
    rw [Matrix.det_smul, Fintype.card_fin]
    calc
      V.det^3 * V.det = (V.det * V.det)^2 := by ring
      _ = 1 := by rw [hs]; norm_num
  have hmem : W ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    refine ⟨?_, hd⟩
    apply (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mpr
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hW
  obtain ⟨O, hO⟩ := (exists_rotationMatrix_iff W).mpr hmem
  refine ⟨O, fun A => ?_⟩
  rw [hO]
  simp only [W, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hs, one_smul]

theorem exists_oriented_spectral_diagonal (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A.IsHermitian) (σ : Equiv.Perm (Fin 3)) :
    ∃ O : rotationGroup3, (rotationMatrix O)ᵀ * A * rotationMatrix O =
      Matrix.diagonal (hA.eigenvalues ∘ σ) := by
  let U : Matrix (Fin 3) (Fin 3) ℝ := hA.eigenvectorUnitary
  have hU : U * Uᵀ = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      unitary.coe_mul_star_self hA.eigenvectorUnitary
  obtain ⟨O, hO⟩ := exists_rotation_preserving_congruence
    (U.submatrix id σ) (orthogonal_columns_reindex U hU σ)
  refine ⟨O, (hO A).trans ?_⟩
  exact spectral_basis_reindex_diagonal A hA σ

end PaperI
