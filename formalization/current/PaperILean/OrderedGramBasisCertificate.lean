import PaperILean.OrderedSingularValueContinuity

/-! I600, I625--638, I668--694: identification of an ordered nonnegative
Gram diagonalization with the unchanged singular-value list. This supplies
finite-dimensional algebraic infrastructure, not semialgebraic growth. -/

noncomputable section
open scoped Matrix InnerProductSpace
namespace PaperI
variable {m : Type*} [Fintype m] {n : ℕ}

theorem orderedSingularBasis_gram_apply (A : Matrix m (Fin n) ℝ) (i : Fin n) :
    Matrix.toEuclideanLin (Aᵀ * A) (orderedSingularBasis A i) =
      descendingSingularValues A i ^ 2 • orderedSingularBasis A i := by
  rw [orderedSingularBasis_apply, descendingSingularValues_sq]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    matrix_gram_eigenvector_apply A (singularValueOrder A i)

theorem gram_basis_norm_sq (A : Matrix m (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (s : Fin n → ℝ)
    (heig : ∀ i, Matrix.toEuclideanLin (Aᵀ * A) (b i) = s i ^ 2 • b i)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin A x‖ ^ 2 = ∑ i, s i ^ 2 * ⟪b i, x⟫_ℝ ^ 2 := by
  rw [matrix_euclidean_norm_sq_eq_gram_inner, ← b.sum_inner_mul_inner]
  apply Finset.sum_congr rfl
  intro i hi
  have hs := Matrix.isHermitian_iff_isSymmetric.mp
    (Matrix.isHermitian_transpose_mul_self A)
  rw [← hs]
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, heig, real_inner_smul_left]
  rw [real_inner_comm x (b i)]
  ring

theorem gram_basis_lower_bound (A : Matrix m (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (s : Fin n → ℝ) (hn : ∀ i, 0 ≤ s i) (ho : Antitone s)
    (heig : ∀ i, Matrix.toEuclideanLin (Aᵀ * A) (b i) = s i ^ 2 • b i)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n))
    (hx : ∀ j, i < j → ⟪b j, x⟫_ℝ = 0) :
    s i * ‖x‖ ≤ ‖Matrix.toEuclideanLin A x‖ := by
  have hsum : (∑ j, ⟪b j, x⟫_ℝ ^ 2) = ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner x
  have hsq : s i ^ 2 * ‖x‖ ^ 2 ≤ ‖Matrix.toEuclideanLin A x‖ ^ 2 := by
    rw [← hsum, Finset.mul_sum, gram_basis_norm_sq A b s heig]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hji : j ≤ i
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have h := ho hji
      have hni := hn i
      nlinarith
    · simp [hx j (lt_of_not_ge hji)]
  have hni := hn i
  have hnx := norm_nonneg x
  have hAx := norm_nonneg (Matrix.toEuclideanLin A x)
  nlinarith [mul_nonneg hni hnx]

theorem gram_basis_upper_bound (A : Matrix m (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (s : Fin n → ℝ) (hn : ∀ i, 0 ≤ s i) (ho : Antitone s)
    (heig : ∀ i, Matrix.toEuclideanLin (Aᵀ * A) (b i) = s i ^ 2 • b i)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n))
    (hx : ∀ j, j < i → ⟪b j, x⟫_ℝ = 0) :
    ‖Matrix.toEuclideanLin A x‖ ≤ s i * ‖x‖ := by
  have hsum : (∑ j, ⟪b j, x⟫_ℝ ^ 2) = ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner x
  have hsq : ‖Matrix.toEuclideanLin A x‖ ^ 2 ≤ s i ^ 2 * ‖x‖ ^ 2 := by
    rw [← hsum, Finset.mul_sum, gram_basis_norm_sq A b s heig]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hij : i ≤ j
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have h := ho hij
      have hnj := hn j
      nlinarith
    · simp [hx j (lt_of_not_ge hij)]
  have hni := hn i
  have hnx := norm_nonneg x
  have hAx := norm_nonneg (Matrix.toEuclideanLin A x)
  nlinarith [mul_nonneg hni hnx]

theorem ordered_gram_basis_unique (A : Matrix m (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (s : Fin n → ℝ) (hn : ∀ i, 0 ≤ s i) (ho : Antitone s)
    (heig : ∀ i, Matrix.toEuclideanLin (Aᵀ * A) (b i) = s i ^ 2 • b i) :
    s = descendingSingularValues A := by
  funext i
  apply le_antisymm
  · obtain ⟨x, hx, hb, ha⟩ := orthonormal_flags_intersect b (orderedSingularBasis A) i
    exact (mul_le_mul_right (norm_pos_iff.mpr hx)).mp
      ((gram_basis_lower_bound A b s hn ho heig i x hb).trans
        (ordered_singular_upper_bound_of_head_zero A i x ha))
  · obtain ⟨x, hx, ha, hb⟩ := orthonormal_flags_intersect (orderedSingularBasis A) b i
    exact (mul_le_mul_right (norm_pos_iff.mpr hx)).mp
      ((ordered_singular_lower_bound_of_tail_zero A i x ha).trans
        (gram_basis_upper_bound A b s hn ho heig i x hb))

theorem descendingSingularValues_eq_iff_gram_basis (A : Matrix m (Fin n) ℝ)
    (s : Fin n → ℝ) :
    s = descendingSingularValues A ↔
      (∀ i, 0 ≤ s i) ∧ Antitone s ∧
        ∃ b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
          ∀ i, Matrix.toEuclideanLin (Aᵀ * A) (b i) = s i ^ 2 • b i := by
  constructor
  · rintro rfl
    exact ⟨descendingSingularValues_nonneg A, descendingSingularValues_antitone A,
      orderedSingularBasis A, orderedSingularBasis_gram_apply A⟩
  · rintro ⟨hn, ho, b, hb⟩
    exact ordered_gram_basis_unique A b s hn ho hb

end PaperI
