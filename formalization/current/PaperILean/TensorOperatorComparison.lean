import PaperILean.TensorEvaluationBounds
import PaperILean.BoundedCenterLattice

/-! Explicit comparison with Lean's pi operator norm. The manuscript's raw
Hilbert--Schmidt tensor norm is retained, including derivative order zero. -/
noncomputable section
open scoped BigOperators
namespace PaperI

theorem physicalEuclideanNorm_le_three_piNorm (v : PhysicalSpace) :
    physicalEuclideanNorm v ≤ 3 * ‖v‖ :=
  (physicalEuclideanNorm_le_sqrt_three_piNorm v).trans
    (mul_le_mul_of_nonneg_right (by simpa using sqrt_three_pow_le 1) (norm_nonneg v))

theorem tensor_opNorm_le_HS {n : ℕ} (T : TensorSpace n) :
    ‖T‖ ≤ (3 : ℝ)^n * tensorHSNorm T := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) (tensorHSNorm_nonneg T))
  intro v
  calc
    ‖T v‖ = |T v| := Real.norm_eq_abs _
    _ ≤ tensorHSNorm T * ∏ j, physicalEuclideanNorm (v j) := abs_tensor_apply_le_HS T v
    _ ≤ tensorHSNorm T * ∏ j, (3 * ‖v j‖) := mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun j _ => physicalEuclideanNorm_nonneg _)
        (fun j _ => physicalEuclideanNorm_le_three_piNorm _)) (tensorHSNorm_nonneg T)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp; ring

end PaperI
