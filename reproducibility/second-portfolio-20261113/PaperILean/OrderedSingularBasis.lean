import PaperILean.LeastSingularValueContinuity

/-! I600, I668--694: the actual right Gram eigenbasis reindexed by the
unchanged decreasing singular-value order. No continuity of this basis is asserted. -/

noncomputable section
open scoped Matrix InnerProductSpace
namespace PaperI
variable {m : Type*} [Fintype m] {n : ℕ}

def orderedSingularBasis (A : Matrix m (Fin n) ℝ) :
    OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  (Matrix.isHermitian_transpose_mul_self A).eigenvectorBasis.reindex
    (singularValueOrder A).symm

theorem orderedSingularBasis_apply (A : Matrix m (Fin n) ℝ) (i : Fin n) :
    orderedSingularBasis A i =
      (Matrix.isHermitian_transpose_mul_self A).eigenvectorBasis (singularValueOrder A i) := by
  simp [orderedSingularBasis, OrthonormalBasis.reindex_apply]

theorem matrix_norm_sq_eq_ordered_singular_sum (A : Matrix m (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin A x‖ ^ 2 =
      ∑ i, descendingSingularValues A i ^ 2 * ⟪orderedSingularBasis A i, x⟫_ℝ ^ 2 := by
  rw [matrix_euclidean_norm_sq_eq_eigenvalue_sum]
  simp only [descendingSingularValues_sq, orderedSingularBasis_apply]
  exact (Equiv.sum_comp (singularValueOrder A) _).symm

theorem orderedSingularBasis_sum_inner_sq (A : Matrix m (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i, ⟪orderedSingularBasis A i, x⟫_ℝ ^ 2) = ‖x‖ ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using (orderedSingularBasis A).sum_sq_norm_inner x

theorem ordered_singular_lower_bound_of_tail_zero (A : Matrix m (Fin n) ℝ)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n))
    (hx : ∀ j, i < j → ⟪orderedSingularBasis A j, x⟫_ℝ = 0) :
    descendingSingularValues A i * ‖x‖ ≤ ‖Matrix.toEuclideanLin A x‖ := by
  have hsq : descendingSingularValues A i ^ 2 * ‖x‖ ^ 2 ≤
      ‖Matrix.toEuclideanLin A x‖ ^ 2 := by
    rw [← orderedSingularBasis_sum_inner_sq A x, Finset.mul_sum,
      matrix_norm_sq_eq_ordered_singular_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hji : j ≤ i
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have ho := descendingSingularValues_antitone A hji
      have hn := descendingSingularValues_nonneg A i
      nlinarith
    · simp [hx j (lt_of_not_ge hji)]
  have hn := descendingSingularValues_nonneg A i
  have hx := norm_nonneg x
  have hAx := norm_nonneg (Matrix.toEuclideanLin A x)
  nlinarith [mul_nonneg hn hx]

theorem ordered_singular_upper_bound_of_head_zero (A : Matrix m (Fin n) ℝ)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n))
    (hx : ∀ j, j < i → ⟪orderedSingularBasis A j, x⟫_ℝ = 0) :
    ‖Matrix.toEuclideanLin A x‖ ≤ descendingSingularValues A i * ‖x‖ := by
  have hsq : ‖Matrix.toEuclideanLin A x‖ ^ 2 ≤
      descendingSingularValues A i ^ 2 * ‖x‖ ^ 2 := by
    rw [← orderedSingularBasis_sum_inner_sq A x, Finset.mul_sum,
      matrix_norm_sq_eq_ordered_singular_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hij : i ≤ j
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have ho := descendingSingularValues_antitone A hij
      have hn := descendingSingularValues_nonneg A j
      nlinarith
    · simp [hx j (lt_of_not_ge hij)]
  have hn := descendingSingularValues_nonneg A i
  have hx := norm_nonneg x
  have hAx := norm_nonneg (Matrix.toEuclideanLin A x)
  nlinarith [mul_nonneg hn hx]

end PaperI
