import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! Determinant algebra for I3263--I3265 and I3276.  The actual derivative
matrices are proved separately.  The rows are the four defining equations and
the columns are `(c,a,b,d)`.  No derivative premise is introduced here. -/

noncomputable section
namespace PaperI.NormalFibers

/-- The common matrix shape of the two actual normalization differentials.
The three lower entries in the first column and the last row's second entry
are retained as arbitrary real numbers: expansion eliminates them. -/
def normalizationMatrix
    (lambda gy cY cZ cQ qA qB qD : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![lambda, 0, 0, 0;
     cY, lambda, 0, 0;
     cZ, 0, lambda, gy;
     cQ, qA, qB, qD]

/-- Exact expansion in the source row and coordinate order. -/
theorem det_normalizationMatrix (lambda gy cY cZ cQ qA qB qD : ℝ) :
    (normalizationMatrix lambda gy cY cZ cQ qA qB qD).det =
      lambda ^ 2 * (lambda * qD - gy * qB) := by
  rw [Matrix.det_succ_row_zero]
  simp [normalizationMatrix, Fin.sum_univ_succ, Matrix.det_fin_three]
  ring

/-- Chart I's exact signed determinant under the actual y-normalization.
Only the two surviving entries from the last row are substituted. -/
theorem det_normalizationMatrix_chartI
    (lambda gy cY cZ cQ qA a xx xy yy : ℝ)
    (hnormal : a * lambda + gy = 0) :
    (normalizationMatrix lambda gy cY cZ cQ qA
      (a * xx + xy) (a * xy + yy)).det =
        lambda ^ 3 * (a ^ 2 * xx + 2 * a * xy + yy) := by
  rw [det_normalizationMatrix]
  have hgy : gy = -(a * lambda) := by
    calc
      gy = (a * lambda + gy) - a * lambda := by ring
      _ = -(a * lambda) := by rw [hnormal]; ring
  rw [hgy]
  ring

/-- Chart II's exact signed determinant under the actual y-normalization.
The coefficient 2 is the derivative of the quadratic chart equation. -/
theorem det_normalizationMatrix_chartII
    (lambda gy cY cZ cQ qA a b d xx xy xz yy yz : ℝ)
    (hnormal : a * lambda + gy = 0) :
    (normalizationMatrix lambda gy cY cZ cQ qA
      (2 * (b * xx + d * xy + xz))
      (2 * (b * xy + d * yy + yz))).det =
        2 * lambda ^ 3 *
          (a * b * xx + (a * d + b) * xy + a * xz + d * yy + yz) := by
  rw [det_normalizationMatrix]
  have hgy : gy = -(a * lambda) := by
    calc
      gy = (a * lambda + gy) - a * lambda := by ring
      _ = -(a * lambda) := by rw [hnormal]; ring
  rw [hgy]
  ring

end PaperI.NormalFibers
