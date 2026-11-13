import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

open Matrix

namespace PaperI.AffineSurfaceCross

abbrev Space := Fin 3 → ℝ

def cross (u w : Space) : Space :=
  ![u 1 * w 2 - u 2 * w 1, u 2 * w 0 - u 0 * w 2, u 0 * w 1 - u 1 * w 0]

def gram (u w : Space) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => dotProduct (![u,w] i) (![u,w] j)

theorem dot_self_nonneg (u : Space) : 0 ≤ dotProduct u u := by
  simp [dotProduct, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]

theorem dot_self_eq_zero_iff (u : Space) : dotProduct u u = 0 ↔ u = 0 :=
  dotProduct_self_eq_zero

theorem cross_dot_left (u w : Space) : dotProduct (cross u w) u = 0 := by
  simp [cross, dotProduct, Fin.sum_univ_succ]
  ring

theorem cross_dot_right (u w : Space) : dotProduct (cross u w) w = 0 := by
  simp [cross, dotProduct, Fin.sum_univ_succ]
  ring

theorem cross_dot_self (u w : Space) :
    dotProduct (cross u w) (cross u w) = (gram u w).det := by
  simp [cross, gram, Matrix.det_fin_two, dotProduct, Fin.sum_univ_succ]
  ring

theorem transpose_mulVec_cross (B : Matrix (Fin 3) (Fin 3) ℝ) (u w : Space) :
    B.transpose.mulVec (cross (B.mulVec u) (B.mulVec w)) = B.det • cross u w := by
  ext i
  fin_cases i <;>
    simp [cross, Matrix.mulVec, Matrix.transpose_apply, Matrix.det_fin_three,
      dotProduct, Fin.sum_univ_succ] <;> ring

theorem cross_mulVec (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0) (u w : Space) :
    cross (B.mulVec u) (B.mulVec w) =
      B.det • (B⁻¹).transpose.mulVec (cross u w) := by
  have h := congrArg ((B⁻¹).transpose.mulVec) (transpose_mulVec_cross B u w)
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB),
    Matrix.transpose_one, Matrix.one_mulVec, Matrix.mulVec_smul] at h
  exact h

theorem inverse_transpose_pairing (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (n z : Space) :
    dotProduct ((B⁻¹).transpose.mulVec n) (B.mulVec z) = dotProduct n z := by
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB), Matrix.one_mulVec]

end PaperI.AffineSurfaceCross
