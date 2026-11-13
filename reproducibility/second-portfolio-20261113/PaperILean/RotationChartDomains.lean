import PaperILean.SkewCoordinateVolume

/-! I327: ordinary chart-domain control, uniform in all positive side ratios.
No logarithm inverse identity or Haar-density statement is assumed here. -/
noncomputable section
open Set
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem positive_ratio_min_le_one (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    min (a / b) (b / a) ≤ 1 := by
  rcases le_total a b with h | h
  · exact (min_le_left _ _).trans ((div_le_one hb).mpr h)
  · exact (min_le_right _ _).trans ((div_le_one ha).mpr h)

theorem skew_opNorm_le_three_mul_conjugate (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : Hᵀ = -H) :
    ‖H‖ ≤ 3 * ‖diagonalFrameConjugate e H‖ := by
  apply matrix_opNorm_le_three_mul_entry_bound H _ (norm_nonneg _)
  intro i j
  exact (skew_weighted_entry_le_of_opNorm_le e he H hH _ le_rfl i j).trans
    (by
      simpa using mul_le_mul_of_nonneg_left
        (positive_ratio_min_le_one (e i) (e j) (he i) (he j))
        (norm_nonneg (diagonalFrameConjugate e H)))

theorem anisotropicSkewBall_ordinary_norm (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H ∈ anisotropicSkewBall e t) :
    ‖H‖ < 3 * t := by
  exact (skew_opNorm_le_three_mul_conjugate e he H hH.1).trans_lt
    (mul_lt_mul_of_pos_left hH.2 (by norm_num))

theorem skewCoordinateBall_ordinary_norm (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (x : PhysicalSpace) (hx : x ∈ skewCoordinateBall e t) :
    ‖skewMatrixOfCoordinates x‖ < 3 * t :=
  anisotropicSkewBall_ordinary_norm e he t _ ⟨skewMatrixOfCoordinates_skew x, hx⟩

theorem rotationMatrix_row_sq_sum (O : rotationGroup3) (i : Fin 3) :
    ∑ j : Fin 3, (rotationMatrix O i j)^2 = 1 := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A i i)
    (rotationMatrix_orthogonal O)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, pow_two] using h

theorem rotationMatrix_sub_one_row_sq_sum (O : rotationGroup3) (i : Fin 3) :
    ∑ j : Fin 3, ((rotationMatrix O - 1) i j)^2 = 2 - 2 * rotationMatrix O i i := by
  have h := rotationMatrix_row_sq_sum O i
  fin_cases i <;> simp [Fin.sum_univ_succ, Matrix.sub_apply, Matrix.one_apply] at * <;>
    nlinarith

theorem rotationMatrix_sub_one_fullHS_sq (O : rotationGroup3) :
    (matrixFullHSNorm (rotationMatrix O - 1))^2 =
      6 - 2 * ∑ i : Fin 3, rotationMatrix O i i := by
  rw [matrixFullHSNorm_sq]
  simp_rw [rotationMatrix_sub_one_row_sq_sum]
  norm_num [Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem diagonalFrameConjugate_diagonal (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    diagonalFrameConjugate e A i i = A i i := by
  rw [diagonalFrameConjugate_apply e he, div_self (he i).ne', mul_one]

theorem rotation_diagonal_displacement_bound (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (O : rotationGroup3) (i : Fin 3) :
    |rotationMatrix O i i - 1| ≤ ‖diagonalFrameConjugate e (rotationMatrix O - 1)‖ := by
  have h := matrix_entry_abs_le_opNorm (diagonalFrameConjugate e (rotationMatrix O - 1)) i i
  rwa [diagonalFrameConjugate_diagonal e he, Matrix.sub_apply, Matrix.one_apply_eq] at h

theorem rotation_sub_one_fullHS_sq_le (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (O : rotationGroup3) :
    (matrixFullHSNorm (rotationMatrix O - 1))^2 ≤
      6 * ‖diagonalFrameConjugate e (rotationMatrix O - 1)‖ := by
  rw [rotationMatrix_sub_one_fullHS_sq]
  have h0 := (abs_le.mp (rotation_diagonal_displacement_bound e he O 0)).1
  have h1 := (abs_le.mp (rotation_diagonal_displacement_bound e he O 1)).1
  have h2 := (abs_le.mp (rotation_diagonal_displacement_bound e he O 2)).1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero]
  norm_num at *
  linarith

theorem rotation_sub_one_opNorm_sq_le (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (O : rotationGroup3) :
    ‖rotationMatrix O - 1‖^2 ≤ 6 * ‖diagonalFrameConjugate e (rotationMatrix O - 1)‖ := by
  exact ((sq_le_sq₀ (norm_nonneg _) (matrixFullHSNorm_nonneg _)).mpr
    (matrix_opNorm_le_fullHS _)).trans (rotation_sub_one_fullHS_sq_le e he O)

theorem rotationNeighborhood_ordinary_norm_lt_one (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (ht : t < 1 / 6) (O : rotationGroup3)
    (hO : O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t) :
    ‖rotationMatrix O - 1‖ < 1 := by
  have h := rotation_sub_one_opNorm_sq_le e he O
  change ‖diagonalFrameConjugate e (rotationMatrix O - 1)‖ < t at hO
  nlinarith [sq_nonneg (‖rotationMatrix O - 1‖ - 1)]

theorem rotationNeighborhood_source_ordinary_domain (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (ht : t < 1 / 10) (O : rotationGroup3)
    (hO : O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t) :
    ‖rotationMatrix O - 1‖ < 1 :=
  rotationNeighborhood_ordinary_norm_lt_one e he t (by linarith) O hO

end PaperI
