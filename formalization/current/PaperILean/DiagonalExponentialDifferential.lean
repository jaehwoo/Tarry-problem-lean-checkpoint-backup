import PaperILean.MatrixExponentialDifferential
import Mathlib.Data.Matrix.Basis
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Actual exponential differential at every real diagonal matrix, including
repeated diagonal entries. The coefficient is an exponential divided difference
with its derivative value at a collision. This is not a CFC-log derivative.
-/

noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

set_option maxHeartbeats 800000

def expDividedDifference (a b : ℝ) : ℝ :=
  if a = b then Real.exp a else (Real.exp a - Real.exp b) / (a - b)

theorem expDividedDifference_self (a : ℝ) : expDividedDifference a a = Real.exp a := by
  simp [expDividedDifference]

theorem expDividedDifference_symm (a b : ℝ) :
    expDividedDifference a b = expDividedDifference b a := by
  by_cases h : a = b
  · subst b; rfl
  · simp only [expDividedDifference, if_neg h, if_neg (Ne.symm h)]
    rw [← neg_sub (Real.exp a) (Real.exp b), ← neg_sub a b, neg_div_neg_eq]

theorem expDividedDifference_pos (a b : ℝ) : 0 < expDividedDifference a b := by
  rcases lt_trichotomy a b with h | h | h
  · rw [expDividedDifference, if_neg (ne_of_lt h)]
    exact div_pos_of_neg_of_neg (sub_neg.mpr (Real.exp_lt_exp.mpr h)) (sub_neg.mpr h)
  · subst b; simpa [expDividedDifference] using Real.exp_pos a
  · rw [expDividedDifference, if_neg (ne_of_gt h)]
    exact div_pos (sub_pos.mpr (Real.exp_lt_exp.mpr h)) (sub_pos.mpr h)

theorem expDividedDifference_ne_zero (a b : ℝ) : expDividedDifference a b ≠ 0 :=
  ne_of_gt (expDividedDifference_pos a b)

theorem diagonal_mul_matrixUnit {n : ℕ} (a : Fin n → ℝ) (i j : Fin n) :
    Matrix.diagonal a * Matrix.stdBasisMatrix i j 1 =
      a i • Matrix.stdBasisMatrix i j (1 : ℝ) := by
  ext u v
  by_cases hi : i = u <;> by_cases hj : j = v <;>
    simp [Matrix.diagonal_mul, Matrix.stdBasisMatrix, Matrix.smul_apply, hi, hj]

theorem matrixUnit_mul_diagonal {n : ℕ} (a : Fin n → ℝ) (i j : Fin n) :
    Matrix.stdBasisMatrix i j 1 * Matrix.diagonal a =
      a j • Matrix.stdBasisMatrix i j (1 : ℝ) := by
  ext u v
  by_cases hi : i = u <;> by_cases hj : j = v <;>
    simp [Matrix.mul_diagonal, Matrix.stdBasisMatrix, Matrix.smul_apply, hi, hj]

theorem matrix_exp_diagonal_real {n : ℕ} (a : Fin n → ℝ) :
    NormedSpace.exp ℝ (Matrix.diagonal a) = Matrix.diagonal (fun i => Real.exp (a i)) := by
  simpa only [Pi.exp_def, ← Real.exp_eq_exp_ℝ] using Matrix.exp_diagonal ℝ a

theorem matrixExpDifferential_diagonal_matrixUnit {n : ℕ}
    (a : Fin n → ℝ) (i j : Fin n) :
    matrixExpDifferential (Matrix.diagonal a) (Matrix.stdBasisMatrix i j 1) =
      expDividedDifference (a i) (a j) • Matrix.stdBasisMatrix i j (1 : ℝ) := by
  by_cases h : a i = a j
  · have hc : Commute (Matrix.diagonal a) (Matrix.stdBasisMatrix i j (1 : ℝ)) := by
      show Matrix.diagonal a * Matrix.stdBasisMatrix i j 1 =
        Matrix.stdBasisMatrix i j 1 * Matrix.diagonal a
      rw [diagonal_mul_matrixUnit, matrixUnit_mul_diagonal, h]
    rw [matrixExpDifferential_commuting_direction _ _ hc, matrix_exp_diagonal_real,
      diagonal_mul_matrixUnit]
    simp [expDividedDifference, h]
  · have hc := matrixExpDifferential_commutator_direction
      (Matrix.diagonal a) (Matrix.stdBasisMatrix i j (1 : ℝ))
    rw [matrixUnit_mul_diagonal, diagonal_mul_matrixUnit, ← sub_smul,
      map_smul, matrix_exp_diagonal_real, matrixUnit_mul_diagonal,
      diagonal_mul_matrixUnit, ← sub_smul] at hc
    have hn : a j - a i ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    calc
      _ = (a j - a i)⁻¹ • ((a j - a i) •
          matrixExpDifferential (Matrix.diagonal a) (Matrix.stdBasisMatrix i j 1)) :=
        (inv_smul_smul₀ hn _).symm
      _ = (a j - a i)⁻¹ • ((Real.exp (a j) - Real.exp (a i)) •
          Matrix.stdBasisMatrix i j 1) := by rw [hc]
      _ = _ := by
        rw [smul_smul]
        congr 1
        rw [expDividedDifference, if_neg h]
        rw [mul_comm, ← div_eq_mul_inv,
          ← neg_sub (Real.exp (a i)) (Real.exp (a j)),
          ← neg_sub (a i) (a j), neg_div_neg_eq]

def diagonalExpDifferential {n : ℕ} (a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun V => Matrix.of (fun i j => expDividedDifference (a i) (a j) * V i j)
    map_add' := by intros; ext; simp [mul_add]
    map_smul' := by intros; ext; simp [smul_eq_mul, mul_left_comm] }

theorem diagonalExpDifferential_apply {n : ℕ} (a : Fin n → ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    diagonalExpDifferential a V i j = expDividedDifference (a i) (a j) * V i j := rfl

theorem matrixExpDifferential_diagonal {n : ℕ} (a : Fin n → ℝ) :
    matrixExpDifferential (Matrix.diagonal a) = diagonalExpDifferential a := by
  apply ContinuousLinearMap.ext
  intro V
  calc
    _ = ∑ i, ∑ j, matrixExpDifferential (Matrix.diagonal a)
        (V i j • Matrix.stdBasisMatrix i j 1) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_stdBasisMatrix V]
      simp only [map_sum, Matrix.smul_stdBasisMatrix, smul_eq_mul, mul_one]
    _ = ∑ i, ∑ j, Matrix.stdBasisMatrix i j
        (expDividedDifference (a i) (a j) * V i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul, matrixExpDifferential_diagonal_matrixUnit, smul_smul,
        Matrix.smul_stdBasisMatrix, smul_eq_mul, mul_one, mul_comm]
    _ = diagonalExpDifferential a V := (Matrix.matrix_eq_sum_stdBasisMatrix _).symm

theorem matrix_exp_diagonal_hasFDerivAt {n : ℕ} (a : Fin n → ℝ) :
    HasFDerivAt (NormedSpace.exp ℝ) (diagonalExpDifferential a) (Matrix.diagonal a) := by
  rw [← matrixExpDifferential_diagonal]
  exact matrix_exp_hasFDerivAt _

def diagonalExpDifferentialEquiv {n : ℕ} (a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ ≃L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (LinearEquiv.toContinuousLinearEquiv {
    toFun := diagonalExpDifferential a
    invFun := fun V => Matrix.of (fun i j => (expDividedDifference (a i) (a j))⁻¹ * V i j)
    map_add' := (diagonalExpDifferential a).map_add
    map_smul' := (diagonalExpDifferential a).map_smul
    left_inv := by intro V; ext i j; simp [diagonalExpDifferential_apply,
      ← mul_assoc, expDividedDifference_ne_zero]
    right_inv := by intro V; ext i j; simp [diagonalExpDifferential_apply,
      ← mul_assoc, expDividedDifference_ne_zero] })

theorem diagonalExpDifferentialEquiv_apply {n : ℕ} (a : Fin n → ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) :
    diagonalExpDifferentialEquiv a V = diagonalExpDifferential a V := rfl

theorem diagonalExpDifferentialEquiv_symm_apply {n : ℕ} (a : Fin n → ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (diagonalExpDifferentialEquiv a).symm V i j =
      (expDividedDifference (a i) (a j))⁻¹ * V i j := rfl

end PaperI
