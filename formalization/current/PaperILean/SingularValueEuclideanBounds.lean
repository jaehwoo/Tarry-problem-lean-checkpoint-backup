import PaperILean.RectangularSingularValues
import Mathlib.Tactic

/-! Euclidean interpretation of the singular values used in I668--690.
The least singular value is an attained lower bound for the operator norm ratio.
This is pointwise finite-dimensional linear algebra; no uniform power bound is asserted.
-/

noncomputable section
open scoped Matrix InnerProductSpace
namespace PaperI

variable {m : Type*} [Fintype m] {n : ℕ}

theorem matrix_euclidean_norm_sq_eq_gram_inner (A : Matrix m (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin A x‖ ^ 2 =
      ⟪x, Matrix.toEuclideanLin (Aᴴ * A) x⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.piLp_equiv_toEuclideanLin_apply, star_trivial, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [← Matrix.mulVec_mulVec]
  conv_rhs => rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem matrix_gram_eigenvector_apply (A : Matrix m (Fin n) ℝ) (i : Fin n) :
    Matrix.toEuclideanLin (Aᴴ * A)
      ((Matrix.isHermitian_transpose_mul_self A).eigenvectorBasis i) =
      (Matrix.isHermitian_transpose_mul_self A).eigenvalues i •
        (Matrix.isHermitian_transpose_mul_self A).eigenvectorBasis i := by
  apply PiLp.ext
  exact congrFun ((Matrix.isHermitian_transpose_mul_self A).mulVec_eigenvectorBasis i)

theorem matrix_euclidean_norm_sq_eq_eigenvalue_sum (A : Matrix m (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin A x‖ ^ 2 =
      ∑ i, (Matrix.isHermitian_transpose_mul_self A).eigenvalues i *
        ⟪(Matrix.isHermitian_transpose_mul_self A).eigenvectorBasis i, x⟫_ℝ ^ 2 := by
  classical
  let b := (Matrix.isHermitian_transpose_mul_self A).eigenvectorBasis
  rw [matrix_euclidean_norm_sq_eq_gram_inner, ← b.sum_inner_mul_inner]
  apply Finset.sum_congr rfl
  intro i hi
  have hs := Matrix.isHermitian_iff_isSymmetric.mp
    (Matrix.isHermitian_transpose_mul_self A)
  rw [← hs, matrix_gram_eigenvector_apply]
  simp only [real_inner_smul_left]
  rw [real_inner_comm x (b i)]
  dsimp [b]
  ring

theorem least_descendingSingularValue_le_rectangular (A : Matrix m (Fin (n + 1)) ℝ)
    (i : Fin (n + 1)) :
    descendingSingularValues A (Fin.last n) ≤ rectangularSingularValues A i := by
  simpa [descendingSingularValues] using
    descendingSingularValues_antitone A (Fin.le_last ((singularValueOrder A).symm i))

theorem least_descendingSingularValue_mul_norm_le (A : Matrix m (Fin (n + 1)) ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    descendingSingularValues A (Fin.last n) * ‖x‖ ≤ ‖Matrix.toEuclideanLin A x‖ := by
  classical
  let b := (Matrix.isHermitian_transpose_mul_self A).eigenvectorBasis
  have hnorm : ∑ i, ⟪b i, x⟫_ℝ ^ 2 = ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner x
  have hsq : descendingSingularValues A (Fin.last n) ^ 2 * ‖x‖ ^ 2 ≤
      ‖Matrix.toEuclideanLin A x‖ ^ 2 := by
    rw [← hnorm, Finset.mul_sum, matrix_euclidean_norm_sq_eq_eigenvalue_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    rw [← rectangularSingularValues_sq]
    have hle := least_descendingSingularValue_le_rectangular A i
    have hn := descendingSingularValues_nonneg A (Fin.last n)
    nlinarith
  have hn := descendingSingularValues_nonneg A (Fin.last n)
  have hx := norm_nonneg x
  have hAx := norm_nonneg (Matrix.toEuclideanLin A x)
  nlinarith [mul_nonneg hn hx]

theorem rectangularSingularValue_eigenvector_norm (A : Matrix m (Fin n) ℝ) (i : Fin n) :
    ‖Matrix.toEuclideanLin A
      ((Matrix.isHermitian_transpose_mul_self A).eigenvectorBasis i)‖ =
      rectangularSingularValues A i := by
  have hsq := matrix_euclidean_norm_sq_eq_gram_inner A
    ((Matrix.isHermitian_transpose_mul_self A).eigenvectorBasis i)
  rw [matrix_gram_eigenvector_apply, real_inner_smul_right,
    real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one] at hsq
  have hn := rectangularSingularValues_nonneg A i
  have hs := rectangularSingularValues_sq A i
  have hAx := norm_nonneg (Matrix.toEuclideanLin A
    ((Matrix.isHermitian_transpose_mul_self A).eigenvectorBasis i))
  nlinarith

theorem descendingSingularValue_exists_unit_vector (A : Matrix m (Fin n) ℝ) (i : Fin n) :
    ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧
      ‖Matrix.toEuclideanLin A x‖ = descendingSingularValues A i := by
  refine ⟨(Matrix.isHermitian_transpose_mul_self A).eigenvectorBasis
    (singularValueOrder A i), OrthonormalBasis.norm_eq_one _ _, ?_⟩
  exact rectangularSingularValue_eigenvector_norm A (singularValueOrder A i)

/-- The last value in the decreasing list is exactly the best lower norm constant. -/
theorem le_least_descendingSingularValue_iff (A : Matrix m (Fin (n + 1)) ℝ) (c : ℝ) :
    c ≤ descendingSingularValues A (Fin.last n) ↔
      ∀ x : EuclideanSpace ℝ (Fin (n + 1)), c * ‖x‖ ≤ ‖Matrix.toEuclideanLin A x‖ := by
  constructor
  · intro hc x
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg x)).trans
      (least_descendingSingularValue_mul_norm_le A x)
  · intro h
    obtain ⟨x, hx, hAx⟩ := descendingSingularValue_exists_unit_vector A (Fin.last n)
    simpa [hx, hAx] using h x

end PaperI
