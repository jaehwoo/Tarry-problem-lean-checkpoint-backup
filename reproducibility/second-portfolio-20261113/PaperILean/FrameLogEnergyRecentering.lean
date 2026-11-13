import PaperILean.FramePolarLogEnergy
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Convex.Deriv

/-! Apply the checked polar bound at every point of B exp(tH).
The recentered frame stays in GL-positive. The final strict-convexity theorem
concerns the logarithmic term, not the full minimizing-frame energy. -/

noncomputable section
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

def recenteredPositiveFrame (B : PositiveFrame) (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : H.IsSymm) (s : ℝ) : PositiveFrame :=
  ⟨B.val * NormedSpace.exp ℝ (s • H), by
    rw [Matrix.det_mul]
    exact mul_pos B.property (symmetric_matrix_exp_posDef (s • H) (hH.smul s)).det_pos⟩

theorem frameLogEnergyCurve_recenter (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (s t : ℝ) :
    frameLogEnergyCurve B H (s + t) =
      frameLogEnergyCurve (recenteredPositiveFrame B H hH s) H t := by
  have he : NormedSpace.exp ℝ ((s + t) • H) =
      NormedSpace.exp ℝ (s • H) * NormedSpace.exp ℝ (t • H) := by
    rw [add_smul]
    exact Matrix.exp_add_of_commute ℝ _ _ (((Commute.refl H).smul_left s).smul_right t)
  simp only [frameLogEnergyCurve, recenteredPositiveFrame, he, Matrix.mul_assoc]

theorem frameLogEnergyCurve_deriv_recenter (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (s t : ℝ) :
    deriv (frameLogEnergyCurve (recenteredPositiveFrame B H hH s) H) t =
      deriv (frameLogEnergyCurve B H) (s + t) := by
  have he : frameLogEnergyCurve (recenteredPositiveFrame B H hH s) H =
      fun u => frameLogEnergyCurve B H (s + u) :=
    funext (fun u => (frameLogEnergyCurve_recenter B H hH s u).symm)
  rw [he, deriv_comp_const_add]

theorem frameLogEnergyCurve_second_deriv_recenter (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (s t : ℝ) :
    deriv (deriv (frameLogEnergyCurve (recenteredPositiveFrame B H hH s) H)) t =
      deriv (deriv (frameLogEnergyCurve B H)) (s + t) := by
  have he := funext (frameLogEnergyCurve_deriv_recenter B H hH s)
  rw [he, deriv_comp_const_add]

theorem frameLogEnergyCurve_second_derivative_ge_HS_at (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (t : ℝ) :
    8 * (matrixFullHSNorm H) ^ 2 ≤ deriv (deriv (frameLogEnergyCurve B H)) t := by
  have h := frameLogEnergyCurve_second_derivative_ge_HS (recenteredPositiveFrame B H hH t) H hH
  rwa [frameLogEnergyCurve_second_deriv_recenter B H hH t 0, add_zero] at h

theorem frameLogEnergyCurve_second_derivative_pos_at (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (hne : H ≠ 0) (t : ℝ) :
    0 < deriv (deriv (frameLogEnergyCurve B H)) t := by
  have h := frameLogEnergyCurve_second_derivative_pos (recenteredPositiveFrame B H hH t) H hH hne
  rwa [frameLogEnergyCurve_second_deriv_recenter B H hH t 0, add_zero] at h

theorem frameLogEnergyCurve_differentiable (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    Differentiable ℝ (frameLogEnergyCurve B H) := by
  rw [frameLogEnergyCurve_eq_source B H hH]
  intro t
  exact (hasDerivAt_sourceMatrixLogEnergyCurve _ (positiveFrame_gram_posDef B)
    _ (orthogonalConjugate_isSymm _ H hH) t).differentiableAt

theorem frameLogEnergyCurve_deriv_differentiable (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    Differentiable ℝ (deriv (frameLogEnergyCurve B H)) := by
  intro t
  have h : DifferentiableAt ℝ
      (deriv (frameLogEnergyCurve (recenteredPositiveFrame B H hH t) H)) 0 := by
    rw [frameLogEnergyCurve_eq_source _ H hH]
    exact (hasDerivAt_deriv_sourceMatrixLogEnergyCurve_zero _
      (positiveFrame_gram_posDef _) _ (orthogonalConjugate_isSymm _ H hH)).differentiableAt
  rw [funext (frameLogEnergyCurve_deriv_recenter B H hH t)] at h
  simpa only [add_zero] using differentiableAt_comp_const_add.mp h

theorem frameLogEnergyCurve_strictConvex (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (hne : H ≠ 0) :
    StrictConvexOn ℝ Set.univ (frameLogEnergyCurve B H) :=
  strictConvexOn_univ_of_deriv2_pos (frameLogEnergyCurve_differentiable B H hH).continuous
    (frameLogEnergyCurve_second_derivative_pos_at B H hH hne)

end PaperI
