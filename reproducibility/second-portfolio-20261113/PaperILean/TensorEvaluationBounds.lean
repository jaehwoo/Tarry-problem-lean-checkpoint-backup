import PaperILean.TensorFrameBounds
import PaperILean.EllipsoidGeometry

/-! Euclidean evaluation bounds for the actual ordered-component HS norm.
These include order zero and arbitrary, not necessarily symmetric, tensors. -/
noncomputable section
open scoped BigOperators
namespace PaperI

theorem tensorHSNorm_zero_order (T : TensorSpace 0) (v : Fin 0 → PhysicalSpace) :
    tensorHSNorm T = |T v| := by
  have h : tensorCoordinates T = fun _ => T v := by
    funext a
    exact congrArg T (Subsingleton.elim _ v)
  simp [tensorHSNorm, h, coordinateL2Norm, Real.sqrt_sq_eq_abs]

theorem abs_tensor_apply_le_HS {n : ℕ} (T : TensorSpace n)
    (v : Fin n → PhysicalSpace) :
    |T v| ≤ tensorHSNorm T * ∏ j, physicalEuclideanNorm (v j) := by
  induction n with
  | zero => simp [← tensorHSNorm_zero_order T v]
  | succ n ih =>
    have h := ih (T.curryLeft (v 0)) (Fin.tail v)
    simp only [ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail] at h
    calc
      _ ≤ tensorHSNorm (T.curryLeft (v 0)) * ∏ j, physicalEuclideanNorm (Fin.tail v j) := h
      _ ≤ (physicalEuclideanNorm (v 0) * tensorHSNorm T) *
          ∏ j, physicalEuclideanNorm (Fin.tail v j) :=
        mul_le_mul_of_nonneg_right (tensorHSNorm_curryLeft_le T (v 0))
          (Finset.prod_nonneg (fun j _ => physicalEuclideanNorm_nonneg _))
      _ = _ := by rw [Fin.prod_univ_succ]; simp only [Fin.tail]; ring

theorem abs_tensor_diagonal_le_HS {n : ℕ} (T : TensorSpace n) (z : PhysicalSpace) :
    |T (fun _ => z)| ≤ tensorHSNorm T * physicalEuclideanNorm z ^ n := by
  simpa using abs_tensor_apply_le_HS T (fun _ => z)

theorem tensor_smul_frame {n : ℕ} (T : TensorSpace n)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (ρ : ℝ) :
    T.compContinuousLinearMap (fun _ => frameLinearMap (ρ • B)) =
      ρ^n • T.compContinuousLinearMap (fun _ => frameLinearMap B) := by
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.smul_apply, frameLinearMap_apply, Matrix.smul_mulVec_assoc]
  rw [T.map_smul_univ]
  simp

end PaperI
