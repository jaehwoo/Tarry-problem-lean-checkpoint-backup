import PaperILean.GradedBlockProjection
import PaperILean.SamplingDeterminantStability

/-! I1484[123,236): perturb only the square diagonal grade blocks.
The strict off-diagonal entries of both original matrices are unrestricted.
An arbitrary linear-order grade also includes the opposite orientation by
using its order dual; the hypotheses always concern literal block rows. -/

noncomputable section
namespace PaperI.GradedSamplingStability

open GradedBlockProjection SamplingDeterminantStability

/-- The exact row-perturbation estimate after removing strictly off-grade
entries by the block-triangular determinant identity. The zero-dimensional
case retains arbitrary M and eps <= 1. -/
theorem graded_determinant_row_perturbation {α : Type*} [LinearOrder α]
    (n : ℕ) (grade : Fin n → α) (B A : Matrix (Fin n) (Fin n) ℝ)
    (M eps : ℝ) (heps1 : eps ≤ 1)
    (hBtri : B.BlockTriangular grade) (hAtri : A.BlockTriangular grade)
    (hrows : ∀ i, coordinateL2Norm
      ((B.toSquareBlock grade (grade i)) ⟨i, rfl⟩) ≤ M)
    (herror : ∀ i, coordinateL2Norm
      ((A.toSquareBlock grade (grade i)) ⟨i, rfl⟩ -
       (B.toSquareBlock grade (grade i)) ⟨i, rfl⟩) ≤ eps) :
    |A.det - B.det| ≤ (n : ℝ) * eps * (M + 1) ^ (n - 1) := by
  have h := DeterminantRowPerturbation.determinant_row_perturbation n
    (diagonalPart grade B) (diagonalPart grade A) M eps heps1
    (fun i => by simpa only [diagonalPart_row_norm] using hrows i)
    (fun i => by simpa only [diagonalPart_row_error_norm] using herror i)
  simpa only [diagonalPart_det grade B hBtri,
    diagonalPart_det grade A hAtri] using h

/-- Complete unbounded-entry graded perturbation stage: the original full
determinant retains half its model value from bounds on diagonal block rows
alone. The same degree-dependent exponent is fixed before P, n, the grade
and both matrices; no bound is imposed on their strict off-diagonal entries. -/
theorem graded_sampling_determinant_stability_stage {α : Type*} [LinearOrder α]
    (k : ℕ) (hk : 2 ≤ k) (Cm Cb : ℝ) (P M b : ℝ) (n : ℕ)
    (grade : Fin n → α) (B A : Matrix (Fin n) (Fin n) ℝ)
    (hn : n ≤ dimension k) (hP : 2 ≤ P) (hwindow : M ≤ P ^ Cm)
    (hb : P ^ (-Cb) ≤ b) (hdet : b ≤ |B.det|)
    (hBtri : B.BlockTriangular grade) (hAtri : A.BlockTriangular grade)
    (hrows : ∀ i, coordinateL2Norm
      ((B.toSquareBlock grade (grade i)) ⟨i, rfl⟩) ≤ M)
    (herror : ∀ i, coordinateL2Norm
      ((A.toSquareBlock grade (grade i)) ⟨i, rfl⟩ -
       (B.toSquareBlock grade (grade i)) ⟨i, rfl⟩) ≤
      P ^ (-samplingToleranceExponent k Cm Cb)) :
    |B.det| / 2 ≤ |A.det| ∧ b / 2 ≤ |A.det| ∧ A.det ≠ 0 := by
  have hdet' : b ≤ |(diagonalPart grade B).det| := by
    simpa only [diagonalPart_det grade B hBtri] using hdet
  have h := sampling_determinant_stability_stage k hk Cm Cb P M b n
    (diagonalPart grade B) (diagonalPart grade A) hn hP hwindow hb hdet'
    (fun i => by simpa only [diagonalPart_row_norm] using hrows i)
    (fun i => by simpa only [diagonalPart_row_error_norm] using herror i)
  simpa only [diagonalPart_det grade B hBtri,
    diagonalPart_det grade A hAtri] using h

end PaperI.GradedSamplingStability
