import PaperILean.AllDimAffinePullback
import PaperILean.AllDimIndexWeights

/-! The full, all-degree determinant character for centered diagonal frames,
including singular matrices and the empty degree-zero coefficient space.
This is only the diagonal part of Lemma 2.1(i). -/

open scoped BigOperators
open Matrix

noncomputable section
namespace PaperI.AllDim

variable {n : ℕ}

def diagonalCoefficientMap (n k : ℕ) (b : Fin n → ℝ) :
    CoefficientSpace n k →ₗ[ℝ] CoefficientSpace n k :=
  LinearMap.pi (fun α : MonomialIndex n k =>
    (LinearMap.mulLeft ℝ (∏ i, b i ^ (α.val i).val)).comp (LinearMap.proj α))

theorem diagonalCoefficientMap_apply (n k : ℕ) (b : Fin n → ℝ)
    (F : CoefficientSpace n k) (α : MonomialIndex n k) :
    diagonalCoefficientMap n k b F α = (∏ i, b i ^ (α.val i).val) * F α := rfl

theorem affinePoint_diagonal (b : Fin n → ℝ) (x : (PhysicalSpace n)) :
    affinePoint 0 (Matrix.diagonal b) x = fun i => b i * x i := by
  change 0 + Matrix.diagonal b *ᵥ x = _
  rw [zero_add]
  funext i
  exact Matrix.mulVec_diagonal b x i

theorem affineCoefficientMap_diagonal (n k : ℕ) (b : Fin n → ℝ) :
    affineCoefficientMap n k 0 (Matrix.diagonal b) = diagonalCoefficientMap n k b := by
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

theorem affineCoefficientMap_diagonal_det (n k : ℕ) (b : Fin n → ℝ) :
    LinearMap.det (affineCoefficientMap n k 0 (Matrix.diagonal b)) =
      (∏ i, b i) ^ chi n k := by
  classical
  rw [affineCoefficientMap_diagonal, diagonalCoefficientMap, LinearMap.det_pi]
  simp_rw [LinearMap.det_mulLeft]
  rw [Finset.prod_comm]
  simp_rw [Finset.prod_pow_eq_pow_sum, sum_monomialCoordinate]
  rw [Finset.prod_pow]

theorem affineCoefficientMap_diagonal_abs_det (n k : ℕ) (b : Fin n → ℝ) :
    |LinearMap.det (affineCoefficientMap n k 0 (Matrix.diagonal b))| =
      |(Matrix.diagonal b).det| ^ chi n k := by
  rw [affineCoefficientMap_diagonal_det, Matrix.det_diagonal, abs_pow]

end PaperI.AllDim
