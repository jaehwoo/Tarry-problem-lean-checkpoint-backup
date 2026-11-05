import PaperILean.ScalarLogSpectralDerivatives
import PaperILean.MatrixOrthogonalReduction

/-! Exact algebra of the source spectral chain rule214-223, including collisions.
The coefficient forms below are finite expressions, NOT definitions of actual
derivatives of log energy. The cited symmetric-space Frechet theorem remains
unformalized. Curve derivatives supplied as their inputs are actual derivatives.
-/

noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

def exponentialDiagonal {n : ℕ} (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => Real.exp (a i))

theorem exponentialDiagonal_posDef {n : ℕ} (a : Fin n → ℝ) :
    (exponentialDiagonal a).PosDef :=
  Matrix.posDef_diagonal_iff.mpr (fun i => Real.exp_pos (a i))

theorem sourcePositiveSqrt_exponentialDiagonal {n : ℕ} (a : Fin n → ℝ) :
    sourcePositiveSqrt (exponentialDiagonal a) (exponentialDiagonal_posDef a) =
      Matrix.diagonal (fun i => Real.exp (a i / 2)) := by
  have hp : (Matrix.diagonal (fun i => Real.exp (a i / 2))).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun i => (Real.exp_pos _).le)
  apply Eq.symm
  apply hp.eq_sqrt_of_sq_eq (exponentialDiagonal_posDef a).posSemidef
  rw [pow_two, Matrix.diagonal_mul_diagonal]
  unfold exponentialDiagonal
  apply congrArg Matrix.diagonal
  funext i
  rw [← Real.exp_add]
  congr 1
  ring

theorem sourceMatrixCurve_exponentialDiagonal_first_entry {n : ℕ}
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    deriv (sourceMatrixCurve (exponentialDiagonal a) (exponentialDiagonal_posDef a) H) 0 i j =
      2 * Real.exp ((a i + a j) / 2) * H i j := by
  rw [sourceMatrixCurve_first_derivative_zero, sourcePositiveSqrt_exponentialDiagonal]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [show (a i + a j) / 2 = a i / 2 + a j / 2 by ring, Real.exp_add]
  ring

theorem sourceMatrixCurve_exponentialDiagonal_second_diagonal {n : ℕ}
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (i : Fin n) :
    deriv (deriv (sourceMatrixCurve (exponentialDiagonal a) (exponentialDiagonal_posDef a) H))
      0 i i = 4 * Real.exp (a i) * (∑ j, (H i j) ^ 2) := by
  rw [sourceMatrixCurve_second_derivative_zero, sourcePositiveSqrt_exponentialDiagonal]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [pow_two, Matrix.mul_apply]
  have hs : (∑ j, H i j * H j i) = ∑ j, (H i j) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hH.apply i j, pow_two]
  rw [hs]
  have he : Real.exp (a i / 2) * Real.exp (a i / 2) = Real.exp (a i) := by
    rw [← Real.exp_add]; congr 1; ring
  calc
    _ = 4 * (Real.exp (a i / 2) * Real.exp (a i / 2)) * (∑ j, (H i j) ^ 2) := by ring
    _ = _ := by rw [he]; simp only [pow_two]

def diagonalLogSpectralGradient {n : ℕ} (a : Fin n → ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, logSquareFirst (Real.exp (a i)) * W i i

def diagonalLogSpectralHessian {n : ℕ} (a : Fin n → ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (∑ i, logSquareSecond (Real.exp (a i)) * (V i i) ^ 2) +
    2 * ∑ i, ∑ j, if i < j then
      logSquareDividedDifference (Real.exp (a i)) (Real.exp (a j)) * (V i j) ^ 2 else 0

theorem symmetric_matrix_weighted_square_sum_split {n : ℕ} (w : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    (∑ i, w i * ∑ j, (H i j) ^ 2) = (∑ i, w i * (H i i) ^ 2) +
      ∑ i, ∑ j, if i < j then (w i + w j) * (H i j) ^ 2 else 0 := by
  have hgt : (∑ i, ∑ j, if j < i then w i * (H i j) ^ 2 else 0) =
      ∑ i, ∑ j, if i < j then w j * (H i j) ^ 2 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hH.apply i j]
  have htri (i j : Fin n) : w i * (H i j) ^ 2 =
      (if i = j then w i * (H i j) ^ 2 else 0) +
      (if i < j then w i * (H i j) ^ 2 else 0) +
      (if j < i then w i * (H i j) ^ 2 else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, ne_of_lt hij, not_lt_of_ge hij.le]
    · subst j; simp
    · simp [hij, (ne_of_lt hij).symm, not_lt_of_ge hij.le]
  calc
    _ = ∑ i, ∑ j, ((if i = j then w i * (H i j) ^ 2 else 0) +
        (if i < j then w i * (H i j) ^ 2 else 0) +
        (if j < i then w i * (H i j) ^ 2 else 0)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl (fun j _ => htri i j)
    _ = (∑ i, w i * (H i i) ^ 2) +
        (∑ i, ∑ j, if i < j then w i * (H i j) ^ 2 else 0) +
        (∑ i, ∑ j, if j < i then w i * (H i j) ^ 2 else 0) := by
      simp [Finset.sum_add_distrib]
    _ = _ := by
      rw [hgt, add_assoc, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> ring

theorem diagonalLogSpectralGradient_source_acceleration {n : ℕ}
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    diagonalLogSpectralGradient a
      (deriv (deriv (sourceMatrixCurve (exponentialDiagonal a) (exponentialDiagonal_posDef a) H)) 0) =
      (∑ i, 8 * a i * (H i i) ^ 2) +
        ∑ i, ∑ j, if i < j then 8 * (a i + a j) * (H i j) ^ 2 else 0 := by
  have he : diagonalLogSpectralGradient a
      (deriv (deriv (sourceMatrixCurve (exponentialDiagonal a) (exponentialDiagonal_posDef a) H)) 0) =
      ∑ i, (8 * a i) * ∑ j, (H i j) ^ 2 := by
    unfold diagonalLogSpectralGradient
    apply Finset.sum_congr rfl
    intro i hi
    rw [sourceMatrixCurve_exponentialDiagonal_second_diagonal a H hH i]
    simp only [logSquareFirst, Real.log_exp]
    field_simp
    ring
  rw [he, symmetric_matrix_weighted_square_sum_split (fun i => 8 * a i) H hH]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

theorem exp_half_sum_square (a b : ℝ) :
    (Real.exp ((a + b) / 2)) ^ 2 = Real.exp a * Real.exp b := by
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem diagonalLogSpectralHessian_source_velocity {n : ℕ}
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    diagonalLogSpectralHessian a
      (deriv (sourceMatrixCurve (exponentialDiagonal a) (exponentialDiagonal_posDef a) H) 0) =
      (∑ i, (4 * (Real.exp (a i)) ^ 2 * logSquareSecond (Real.exp (a i))) * (H i i) ^ 2) +
        ∑ i, ∑ j, if i < j then
          (8 * Real.exp (a i) * Real.exp (a j) *
            logSquareDividedDifference (Real.exp (a i)) (Real.exp (a j))) * (H i j) ^ 2 else 0 := by
  unfold diagonalLogSpectralHessian
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [sourceMatrixCurve_exponentialDiagonal_first_entry]
    rw [show (a i + a i) / 2 = a i by ring]
    ring
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · simp only [if_pos hij]
      rw [sourceMatrixCurve_exponentialDiagonal_first_entry, mul_pow, mul_pow,
        exp_half_sum_square]
      ring
    · simp only [if_neg hij, mul_zero]

theorem diagonalLogSpectral_chain_algebra {n : ℕ}
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    diagonalLogSpectralHessian a
        (deriv (sourceMatrixCurve (exponentialDiagonal a) (exponentialDiagonal_posDef a) H) 0) +
      diagonalLogSpectralGradient a
        (deriv (deriv (sourceMatrixCurve (exponentialDiagonal a) (exponentialDiagonal_posDef a) H)) 0) =
      logSpectralHessianForm a H := by
  rw [diagonalLogSpectralHessian_source_velocity, diagonalLogSpectralGradient_source_acceleration a H hH]
  unfold logSpectralHessianForm
  rw [Finset.mul_sum, Finset.mul_sum]
  have hreorder (d o e p : ℝ) : (d + o) + (e + p) = (d + e) + (o + p) := by ring
  rw [hreorder, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hc := logSquare_diagonal_chain_coefficient (Real.exp (a i)) (Real.exp_pos _)
    simp only [logSquareFirst, Real.log_exp] at hc
    have he : 4 * Real.exp (a i) * (2 * a i / Real.exp (a i)) = 8 * a i := by
      field_simp; ring
    rw [he] at hc
    nlinarith [sq_nonneg (H i i)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · simp only [if_pos hij]
      rw [← add_mul, logSquare_pair_chain_coefficient]
      ring
    · simp only [if_neg hij, add_zero, mul_zero]

end PaperI
