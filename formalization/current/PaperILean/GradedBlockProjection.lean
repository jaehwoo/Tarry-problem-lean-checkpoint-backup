import PaperILean.TensorContractionBounds
import Mathlib.LinearAlgebra.Matrix.Block

/-! I1484[123,236): exact graded transfer before perturbation. The same
grade map indexes rows and columns. Strict off-diagonal entries receive
no size bound. Literal square-block row norms are preserved exactly. -/

noncomputable section
open scoped BigOperators

namespace PaperI.GradedBlockProjection

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- Retain precisely the square diagonal grade blocks. -/
noncomputable def diagonalPart (grade : Fin n → α)
    (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if grade i = grade j then X i j else 0

theorem diagonalPart_blockTriangular (grade : Fin n → α)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    (diagonalPart grade X).BlockTriangular grade := by
  intro i j hij
  simp only [diagonalPart, if_neg (ne_of_gt hij)]

theorem diagonalPart_squareBlock (grade : Fin n → α)
    (X : Matrix (Fin n) (Fin n) ℝ) (a : α) :
    (diagonalPart grade X).toSquareBlock grade a = X.toSquareBlock grade a := by
  ext i j
  change (if grade i.val = grade j.val then X i.val j.val else 0) = X i.val j.val
  rw [if_pos (i.property.trans j.property.symm)]

/-- Exact determinant transfer; only occupied grades enter the finite product. -/
theorem diagonalPart_det (grade : Fin n → α)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.BlockTriangular grade) :
    (diagonalPart grade X).det = X.det := by
  classical
  rw [(diagonalPart_blockTriangular grade X).det, hX.det]
  apply Finset.prod_congr rfl
  intro a ha
  rw [diagonalPart_squareBlock]

/-- Zero padding a literal diagonal-block row preserves its Euclidean norm. -/
theorem diagonalPart_row_norm (grade : Fin n → α)
    (X : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    coordinateL2Norm (diagonalPart grade X i) =
      coordinateL2Norm ((X.toSquareBlock grade (grade i)) ⟨i, rfl⟩) := by
  classical
  unfold coordinateL2Norm
  congr 1
  change (∑ j : Fin n, diagonalPart grade X i j ^ 2) =
    ∑ j : {j : Fin n // grade j = grade i}, X i j.val ^ 2
  calc
    (∑ j : Fin n, diagonalPart grade X i j ^ 2) =
        ∑ j ∈ Finset.univ.filter (fun j => grade j = grade i), X i j ^ 2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : grade j = grade i
      · simp only [diagonalPart, if_pos h.symm, if_pos h]
      · simp only [diagonalPart, if_neg (Ne.symm h), if_neg h, zero_pow (by decide : 2 ≠ 0)]
    _ = _ := Finset.sum_subtype _ (fun j => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) _

/-- The same norm identity applies to actual diagonal-block row errors. -/
theorem diagonalPart_row_error_norm (grade : Fin n → α)
    (A B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    coordinateL2Norm (diagonalPart grade A i - diagonalPart grade B i) =
      coordinateL2Norm ((A.toSquareBlock grade (grade i)) ⟨i, rfl⟩ -
        (B.toSquareBlock grade (grade i)) ⟨i, rfl⟩) := by
  have hrow : diagonalPart grade A i - diagonalPart grade B i =
      diagonalPart grade (A - B) i := by
    funext j
    by_cases h : grade i = grade j <;> simp [diagonalPart, h]
  rw [hrow, diagonalPart_row_norm]
  rfl

end PaperI.GradedBlockProjection
