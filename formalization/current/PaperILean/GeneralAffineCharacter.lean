import PaperILean.AffineCharacterTargets
import PaperILean.OriginalAffineDeterminant
import PaperILean.CoefficientChange
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! The three-dimensional affine character in every degree.

This uses an alternative argument: dilation makes translation and elementary
shear determinants nonzero idempotents; matrix induction reduces the centered
signed character to shears and diagonals. The absolute determinant theorem
below now specializes the original triangularity, homogeneous, orthogonal
and singular-value-decomposition proof. -/

open scoped BigOperators
open Matrix

noncomputable section
namespace PaperI

theorem affineCoefficientMap_det_comp (k : ℕ) (c d : PhysicalSpace)
    (B A : Matrix (Fin 3) (Fin 3) ℝ) :
    LinearMap.det (affineCoefficientMap k (c + B *ᵥ d) (B * A)) =
      LinearMap.det (affineCoefficientMap k d A) *
        LinearMap.det (affineCoefficientMap k c B) := by
  have h : affineCoefficientMap k (c + B *ᵥ d) (B * A) =
      (affineCoefficientMap k d A).comp (affineCoefficientMap k c B) := by
    apply LinearMap.ext
    intro F
    exact (affineCoefficientMap_comp k c d B A F).symm
  rw [h, LinearMap.det_comp]

theorem affineCoefficientMap_translation_det (k : ℕ) (c : PhysicalSpace) :
    LinearMap.det (affineCoefficientMap k c (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 1 := by
  let D : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal (fun _ => 2)
  have hD : D.det ≠ 0 := by simp [D, Matrix.det_diagonal]
  have hDmap := affineCoefficientMap_det_ne_zero k 0 D hD
  have hc : D *ᵥ c = c + c := by
    ext i
    simp [D, Matrix.mulVec_diagonal]
    ring
  have hleft := affineCoefficientMap_det_comp k 0 c D 1
  have hright := affineCoefficientMap_det_comp k (c + c) 0 1 D
  simp only [zero_add, hc, Matrix.mul_one] at hleft
  simp only [Matrix.mulVec_zero, add_zero, Matrix.one_mul] at hright
  have hequal : LinearMap.det (affineCoefficientMap k c 1) =
      LinearMap.det (affineCoefficientMap k (c + c) 1) := by
    apply mul_right_cancel₀ hDmap
    exact hleft.symm.trans (hright.trans (mul_comm _ _))
  have hdouble := affineCoefficientMap_det_comp k c c 1 1
  simp only [Matrix.one_mulVec, Matrix.one_mul] at hdouble
  have hnonzero := affineCoefficientMap_det_ne_zero k c 1 (by simp)
  have hidempotent : LinearMap.det (affineCoefficientMap k c 1) *
      LinearMap.det (affineCoefficientMap k c 1) =
      LinearMap.det (affineCoefficientMap k c 1) := hdouble.symm.trans hequal.symm
  apply mul_left_cancel₀ hnonzero
  simpa using hidempotent

theorem diagonal_transvection_double (i j : Fin 3) (hij : i ≠ j) (t : ℝ) :
    Matrix.diagonal (fun a => if a = i then (2 : ℝ) else 1) *
        Matrix.transvection i j t =
      Matrix.transvection i j (t + t) *
        Matrix.diagonal (fun a => if a = i then (2 : ℝ) else 1) := by
  classical
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transvection,
    Matrix.add_apply, Matrix.one_apply, Matrix.stdBasisMatrix]
  by_cases ha : a = i <;> by_cases hb : b = j <;> by_cases hab : a = b <;>
    simp_all [eq_comm] <;> ring

theorem affineCoefficientMap_centered_det_mul (k : ℕ)
    (B A : Matrix (Fin 3) (Fin 3) ℝ) :
    LinearMap.det (affineCoefficientMap k 0 (B * A)) =
      LinearMap.det (affineCoefficientMap k 0 B) *
        LinearMap.det (affineCoefficientMap k 0 A) := by
  simpa only [Matrix.mulVec_zero, add_zero, mul_comm] using
    affineCoefficientMap_det_comp k 0 0 B A

theorem affineCoefficientMap_transvection_det (k : ℕ) (i j : Fin 3)
    (hij : i ≠ j) (t : ℝ) :
    LinearMap.det (affineCoefficientMap k 0 (Matrix.transvection i j t)) = 1 := by
  classical
  let D : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.diagonal (fun a => if a = i then (2 : ℝ) else 1)
  have hD : D.det ≠ 0 := by
    dsimp [D]
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (by intro a ha; split_ifs <;> norm_num)
  have hDmap := affineCoefficientMap_det_ne_zero k 0 D hD
  have hleft := affineCoefficientMap_centered_det_mul k D (Matrix.transvection i j t)
  have hright := affineCoefficientMap_centered_det_mul k
    (Matrix.transvection i j (t + t)) D
  have hsimilar := diagonal_transvection_double i j hij t
  change D * Matrix.transvection i j t = Matrix.transvection i j (t + t) * D at hsimilar
  have hequal : LinearMap.det (affineCoefficientMap k 0 (Matrix.transvection i j t)) =
      LinearMap.det (affineCoefficientMap k 0 (Matrix.transvection i j (t + t))) := by
    apply mul_left_cancel₀ hDmap
    exact hleft.symm.trans (congrArg (fun B =>
      LinearMap.det (affineCoefficientMap k 0 B)) hsimilar |>.trans
        (hright.trans (mul_comm _ _)))
  have hdouble := affineCoefficientMap_centered_det_mul k
    (Matrix.transvection i j t) (Matrix.transvection i j t)
  rw [Matrix.transvection_mul_transvection_same i j hij] at hdouble
  have hnonzero := affineCoefficientMap_det_ne_zero k 0 (Matrix.transvection i j t)
    (by rw [Matrix.det_transvection_of_ne i j hij]; norm_num)
  have hidempotent :
      LinearMap.det (affineCoefficientMap k 0 (Matrix.transvection i j t)) *
        LinearMap.det (affineCoefficientMap k 0 (Matrix.transvection i j t)) =
      LinearMap.det (affineCoefficientMap k 0 (Matrix.transvection i j t)) :=
    hdouble.symm.trans hequal.symm
  apply mul_left_cancel₀ hnonzero
  simpa using hidempotent

theorem affineCoefficientMap_centered_det (k : ℕ)
    (B : Matrix (Fin 3) (Fin 3) ℝ) :
    LinearMap.det (affineCoefficientMap k 0 B) = B.det ^ chi k := by
  classical
  apply Matrix.diagonal_transvection_induction
    (fun B : Matrix (Fin 3) (Fin 3) ℝ =>
      LinearMap.det (affineCoefficientMap k 0 B) = B.det ^ chi k) B
  · intro b hb
    rw [affineCoefficientMap_diagonal_det, Matrix.det_diagonal]
  · intro t
    rw [Matrix.TransvectionStruct.toMatrix,
      affineCoefficientMap_transvection_det k t.i t.j t.hij,
      Matrix.det_transvection_of_ne t.i t.j t.hij, one_pow]
  · intro A B hA hB
    rw [affineCoefficientMap_centered_det_mul, hA, hB, Matrix.det_mul, mul_pow]

theorem affineCoefficientMap_det (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) :
    LinearMap.det (affineCoefficientMap k c B) = B.det ^ chi k := by
  rw [affineCoefficientMap_factor, LinearMap.det_comp,
    affineCoefficientMap_translation_det, mul_one, affineCoefficientMap_centered_det]

theorem affineCoefficientMap_abs_det (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) :
    |LinearMap.det (affineCoefficientMap k c B)| = |B.det| ^ chi k := by
  exact AllDim.Original.affineCoefficientMap_abs_det_original 3 k c B

theorem translationDeterminantStatement (k : ℕ) : TranslationDeterminantStatement k :=
  affineCoefficientMap_translation_det k

theorem centeredLinearCharacterStatement (k : ℕ) : CenteredLinearCharacterStatement k :=
  fun B => affineCoefficientMap_abs_det k 0 B

theorem affineCharacterStatement (k : ℕ) : AffineCharacterStatement k :=
  affineCoefficientMap_abs_det k

end PaperI
