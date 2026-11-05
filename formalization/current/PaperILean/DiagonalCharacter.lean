import PaperILean.AffinePullback
import PaperILean.CharacterCombinatorics

/-! The full, all-degree determinant character for centered diagonal frames,
including singular matrices and the empty degree-zero coefficient space.
This is only the diagonal part of Lemma 2.1(i). -/

open scoped BigOperators
open Matrix

noncomputable section
namespace PaperI

def diagonalCoefficientMap (k : ℕ) (b : Fin 3 → ℝ) :
    CoefficientSpace k →ₗ[ℝ] CoefficientSpace k :=
  LinearMap.pi (fun α : MonomialIndex k =>
    (LinearMap.mulLeft ℝ (∏ i, b i ^ (α.val i).val)).comp (LinearMap.proj α))

theorem diagonalCoefficientMap_apply (k : ℕ) (b : Fin 3 → ℝ)
    (F : CoefficientSpace k) (α : MonomialIndex k) :
    diagonalCoefficientMap k b F α = (∏ i, b i ^ (α.val i).val) * F α := rfl

theorem affinePoint_diagonal (b : Fin 3 → ℝ) (x : PhysicalSpace) :
    affinePoint 0 (Matrix.diagonal b) x = fun i => b i * x i := by
  change 0 + Matrix.diagonal b *ᵥ x = _
  rw [zero_add]
  funext i
  exact Matrix.mulVec_diagonal b x i

theorem affineCoefficientMap_diagonal (k : ℕ) (b : Fin 3 → ℝ) :
    affineCoefficientMap k 0 (Matrix.diagonal b) = diagonalCoefficientMap k b := by
  apply LinearMap.ext
  intro F
  apply coefficient_ext
  intro x
  rw [phase_affineCoefficientMap, phase_zero, sub_zero, affinePoint_diagonal]
  unfold phase
  apply Finset.sum_congr rfl
  intro α hα
  simp only [mul_pow, Finset.prod_mul_distrib, diagonalCoefficientMap_apply]
  ring

theorem affineCoefficientMap_diagonal_det (k : ℕ) (b : Fin 3 → ℝ) :
    LinearMap.det (affineCoefficientMap k 0 (Matrix.diagonal b)) =
      (∏ i, b i) ^ chi k := by
  classical
  rw [affineCoefficientMap_diagonal, diagonalCoefficientMap, LinearMap.det_pi]
  simp_rw [LinearMap.det_mulLeft]
  rw [Finset.prod_comm]
  simp_rw [Finset.prod_pow_eq_pow_sum, sum_monomialCoordinate]
  rw [Finset.prod_pow]

theorem affineCoefficientMap_diagonal_abs_det (k : ℕ) (b : Fin 3 → ℝ) :
    |LinearMap.det (affineCoefficientMap k 0 (Matrix.diagonal b))| =
      |(Matrix.diagonal b).det| ^ chi k := by
  rw [affineCoefficientMap_diagonal_det, Matrix.det_diagonal, abs_pow]

end PaperI
